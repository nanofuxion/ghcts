/** Typeclass elaboration: surface Haskell with classes to surface Haskell
 * without them, i.e. explicit dictionary passing, exactly the way GHC does it
 * before Core.
 *
 * A class becomes a data type whose fields are its superclass dictionaries
 * followed by its methods; an instance becomes a top-level value of that type
 * (`$fShowInt`); a method becomes a field selector taking the dictionary; a
 * constrained binding gains one leading parameter per constraint; a call site
 * either selects the instance (its type is known) or forwards a dictionary it
 * was given (its type is a variable it is quantified over).
 *
 * Everything this pass emits is ordinary surface AST, so `src/desugar.ts`
 * compiles the result with no idea that classes ever existed.
 *
 * Deciding *which* dictionary is a typing question, so this pass carries a
 * Hindley-Milner inference. Deliberate restrictions, each of which produces a
 * diagnostic rather than a wrong dictionary:
 *
 *   - a class may have any number of parameters, and an instance is selected by
 *     matching *all* of them. An instance head may be non-ground and carry a
 *     context (`Eq a => Eq [a]`); such an instance is a *function* from
 *     dictionaries to a dictionary, and selecting it is recursive.
 *   - a multi-parameter class may declare functional dependencies
 *     (`class MonadState s m | m -> s`), and they are honoured by an
 *     improvement pass that unifies a wanted's determined arguments with those
 *     of the given or instance its determining arguments already match. That
 *     pass runs once per binding, at the point the binding is finished, not
 *     interleaved with unification the way GHC's solver runs it: a type that
 *     only improvement could have supplied is therefore known in time to
 *     select a dictionary or to be generalised, but not in time to stop an
 *     earlier unification in the same binding from going wrong first.
 *   - a binding with a signature takes its constraints from that signature, in
 *     that order; those are the *givens*, and a wanted constraint is discharged
 *     against them directly or through a superclass path. A binding without a
 *     signature has its constraints inferred, and a binding without a
 *     signature *and* without parameters is not generalised at all (Haskell's
 *     monomorphism restriction) - which is what lets `main = show (1 + 2)`
 *     default to `Int` instead of becoming a function of two dictionaries.
 *   - an integer literal is `fromInteger` applied to a raw machine literal, so
 *     `1 + 2 :: Int` really goes through `$fNumInt`. At the unboxed type
 *     `IntPrim` there is no `Num` instance to select and the literal stays
 *     raw; that is the one place a `Num` wanted is discharged structurally,
 *     because `IntPrim` *is* the machine integer.
 *   - an integer *pattern* is monomorphic at `Int` (or `IntPrim` when the
 *     scrutinee is already unboxed). GHC compiles a literal pattern through
 *     `==`; here it is compiled structurally, as a match on `I <lit>`, which
 *     is only sound at the one type whose representation we know.
 */
import type {
  CaseAlternative,
  ClassDeclaration,
  DataDeclaration,
  Declaration,
  Expr,
  Guard,
  InstanceDeclaration,
  LocalBinding,
  Module,
  Pattern,
  SignatureDeclaration,
  Span,
  ValueDeclaration,
} from "./ast.js";
import { instanceHead, instanceMethodValues } from "./dictionary.js";
import { renameDeclarations, renameValue, resolveProgram, type Scope } from "./modules.js";
import { error } from "./diagnostics.js";
import { constructorTable, derivedEqMethod, expandSugar, fieldSelectors } from "./sugar.js";
import { PRELUDE_SOURCE } from "./prelude.js";
import { withLibraryModules } from "./library.js";
import { parseModule } from "./parser.js";
import type { Diagnostic } from "./types.js";

export interface ElaborateResult {
  module: Module;
  diagnostics: Diagnostic[];
}

// ---------------------------------------------------------------- types ----

interface TVar {
  id: number;
  ref: Type | null;
}

type Type =
  | { tag: "var"; v: TVar }
  | { tag: "con"; name: string }
  | { tag: "app"; fn: Type; arg: Type }
  /** Only inside a `Scheme`; instantiation replaces these with fresh vars. */
  | { tag: "gen"; index: number };

/** `MonadState s m` is `{ cls: "MonadState", types: [s, m] }`: the argument
 * list is what makes a class multi-parameter, and every consumer here - given,
 * wanted, instance head, superclass path - carries the whole list. */
interface Constraint {
  cls: string;
  types: Type[];
}

const sameTypes = (a: readonly Type[], b: readonly Type[]): boolean =>
  a.length === b.length && a.every((t, i) => sameType(t, b[i]!));

/** A constraint as it is spelled in a diagnostic and as the key that stops the
 * superclass walk revisiting a node. */
const showConstraint = (cls: string, types: readonly Type[]): string =>
  [cls, ...types.map(showType)].join(" ");

interface Scheme {
  gens: number;
  constraints: Constraint[];
  type: Type;
}

const tcon = (name: string): Type => ({ tag: "con", name });
const tapp = (fn: Type, arg: Type): Type => ({ tag: "app", fn, arg });
const tfun = (a: Type, b: Type): Type => tapp(tapp(tcon("->"), a), b);
const tlist = (a: Type): Type => tapp(tcon("[]"), a);
const tInt = tcon("Int");
const tBool = tcon("Bool");
const tChar = tcon("Char");
const tString = tlist(tChar);

let nextTVar = 0;
const freshVar = (): Type => ({ tag: "var", v: { id: nextTVar++, ref: null } });

function prune(t: Type): Type {
  if (t.tag === "var" && t.v.ref) {
    const inner = prune(t.v.ref);
    t.v.ref = inner;
    return inner;
  }
  return t;
}

function occurs(v: TVar, t: Type): boolean {
  const p = prune(t);
  if (p.tag === "var") return p.v === v;
  if (p.tag === "app") return occurs(v, p.fn) || occurs(v, p.arg);
  return false;
}

/** Unification failure is reported by the caller, which has a span; returning
 * a boolean keeps every inference site able to continue with the types it
 * already has rather than aborting the module. */
function unify(a: Type, b: Type): boolean {
  const x = prune(a);
  const y = prune(b);
  if (x.tag === "var") {
    if (y.tag === "var" && y.v === x.v) return true;
    if (occurs(x.v, y)) return false;
    x.v.ref = y;
    return true;
  }
  if (y.tag === "var") return unify(y, x);
  if (x.tag === "con" && y.tag === "con") return x.name === y.name;
  if (x.tag === "app" && y.tag === "app") return unify(x.fn, y.fn) && unify(x.arg, y.arg);
  return false;
}

function typeVars(t: Type, out: TVar[] = []): TVar[] {
  const p = prune(t);
  if (p.tag === "var" && !out.includes(p.v)) out.push(p.v);
  if (p.tag === "app") {
    typeVars(p.fn, out);
    typeVars(p.arg, out);
  }
  return out;
}

const sameType = (a: Type, b: Type): boolean => {
  const x = prune(a);
  const y = prune(b);
  if (x.tag === "var" || y.tag === "var") return x.tag === "var" && y.tag === "var" && x.v === y.v;
  if (x.tag === "con" && y.tag === "con") return x.name === y.name;
  if (x.tag === "app" && y.tag === "app") return sameType(x.fn, y.fn) && sameType(x.arg, y.arg);
  return false;
};

/** The type constructor an instance is chosen by; `undefined` while the type
 * is still an unsolved variable. */
function headCon(t: Type): string | undefined {
  const p = prune(t);
  if (p.tag === "con") return p.name;
  if (p.tag === "app") return headCon(p.fn);
  return undefined;
}

function substGens(t: Type, images: Type[]): Type {
  const p = prune(t);
  if (p.tag === "gen") return images[p.index] ?? freshVar();
  if (p.tag === "app") return tapp(substGens(p.fn, images), substGens(p.arg, images));
  return p;
}

function instantiate(scheme: Scheme): { type: Type; constraints: Constraint[] } {
  const images = Array.from({ length: scheme.gens }, () => freshVar());
  return {
    type: substGens(scheme.type, images),
    constraints: scheme.constraints.map((c) => ({ cls: c.cls, types: c.types.map((t) => substGens(t, images)) })),
  };
}

/** Replace the listed variables by `gen` indices, in the given order, so a
 * scheme's constraint order (and therefore a binding's dictionary parameter
 * order) is stable between the definition and every call site. */
function quantify(vars: TVar[], type: Type, constraints: Constraint[]): Scheme {
  const index = new Map(vars.map((v, i) => [v, i]));
  const go = (t: Type): Type => {
    const p = prune(t);
    if (p.tag === "var") {
      const i = index.get(p.v);
      return i === undefined ? p : { tag: "gen", index: i };
    }
    if (p.tag === "app") return tapp(go(p.fn), go(p.arg));
    return p;
  };
  return { gens: vars.length, type: go(type), constraints: constraints.map((c) => ({ cls: c.cls, types: c.types.map(go) })) };
}

// --------------------------------------------------------- type parsing ----

const TYPE_TOKEN = /->|=>|[A-Za-z_][A-Za-z0-9_'.]*|[[\](),]/g;

function splitTop(tokens: readonly string[], separator: string): string[][] {
  const parts: string[][] = [[]];
  let depth = 0;
  for (const token of tokens) {
    if (token === "(" || token === "[") depth++;
    else if (token === ")" || token === "]") depth--;
    if (depth === 0 && token === separator) {
      parts.push([]);
      continue;
    }
    parts[parts.length - 1]!.push(token);
  }
  return parts;
}

/** `type X a = ...` declarations, by name. Types are never renamed by the
 * module system (see `src/modules.ts`), so one table serves the program.
 * Filled once per `elaborateProgram`, like `nextTVar`. */
let synonyms = new Map<string, { parameters: string[]; target: string }>();

class TypeParser {
  private index = 0;
  constructor(
    private readonly tokens: readonly string[],
    private readonly vars: Map<string, Type>,
    /** Guards against `type T = T`; a chain longer than this is a cycle. */
    private readonly depth = 0,
  ) {}

  static tokens(source: string): string[] {
    return source.match(TYPE_TOKEN) ?? [];
  }

  /** A constraint's arguments: `MonadState s m` is two types, not the
   * application `s m`, so a class's arguments are parsed atom by atom. */
  argList(): Type[] {
    const args: Type[] = [];
    while (this.index < this.tokens.length && !["->", ")", "]", ",", "=>"].includes(this.tokens[this.index]!)) {
      args.push(this.atom());
    }
    return args;
  }

  fun(): Type {
    const left = this.application();
    if (this.tokens[this.index] === "->") {
      this.index++;
      return tfun(left, this.fun());
    }
    return left;
  }

  private application(): Type {
    const head = this.tokens[this.index];
    const synonym = head === undefined ? undefined : synonyms.get(unqualify(head));
    if (synonym && this.depth < 16) {
      this.index++;
      const bound = new Map<string, Type>();
      for (const parameter of synonym.parameters) bound.set(parameter, this.atom());
      let value = new TypeParser(TypeParser.tokens(synonym.target), bound, this.depth + 1).fun();
      // A partially applied synonym is still an application: `type Handler a =
      // a -> ()` used as `Handler Int Extra` keeps consuming arguments.
      while (this.index < this.tokens.length && !["->", ")", "]", ",", "=>"].includes(this.tokens[this.index]!)) {
        value = tapp(value, this.atom());
      }
      return value;
    }
    let value = this.atom();
    while (this.index < this.tokens.length && !["->", ")", "]", ",", "=>"].includes(this.tokens[this.index]!)) {
      value = tapp(value, this.atom());
    }
    return value;
  }

  private atom(): Type {
    const raw = this.tokens[this.index++];
    if (raw === undefined) return freshVar();
    // A qualified type constructor names the same type as the bare one: types
    // live in one global namespace here, exactly as `src/modules.ts` treats a
    // qualified constructor in an expression. Without this, `M.Map Int a` is
    // an unrelated opaque type from `Map Int a`.
    const token = unqualify(raw);
    if (token === "[") {
      // `[]` on its own is the list *constructor*, which is what an instance
      // head like `Foldable []` names; `[a]` is that constructor applied.
      if (this.tokens[this.index] === "]") {
        this.index++;
        return tcon("[]");
      }
      const item = this.fun();
      if (this.tokens[this.index] === "]") this.index++;
      return tlist(item);
    }
    if (token === "(") {
      if (this.tokens[this.index] === ")") {
        this.index++;
        return tcon("()");
      }
      const items = [this.fun()];
      while (this.tokens[this.index] === ",") {
        this.index++;
        items.push(this.fun());
      }
      if (this.tokens[this.index] === ")") this.index++;
      return items.length === 1
        ? items[0]!
        : items.reduce((acc, item) => tapp(acc, item), tcon(`(${",".repeat(items.length - 1)})`));
    }
    if (/^[a-z_]/.test(token)) {
      const existing = this.vars.get(token);
      if (existing) return existing;
      const made = freshVar();
      this.vars.set(token, made);
      return made;
    }
    // `String` is the only alias the minimal Prelude relies on; keeping it here
    // rather than in Haskell avoids declaring it.
    if (token === "String") return tString;
    // A nullary synonym is a type by itself, so it expands in argument
    // position too - `Both Count` has to reach `(Int, Int)`, not `(Count, Count)`.
    const synonym = synonyms.get(token);
    if (synonym && synonym.parameters.length === 0 && this.depth < 16) {
      return new TypeParser(TypeParser.tokens(synonym.target), new Map(), this.depth + 1).fun();
    }
    return tcon(token);
  }
}

/** A signature string, split into its context and its type. */
/** `M.Map` -> `Map`, `Data.Text.Text` -> `Text`. */
const unqualify = (name: string): string =>
  /^[A-Z][A-Za-z0-9_']*(\.[A-Z][A-Za-z0-9_']*)+$/.test(name) ? name.slice(name.lastIndexOf(".") + 1) : name;

function parseSignature(source: string, vars: Map<string, Type>): { context: Constraint[]; type: Type } {
  const tokens = TypeParser.tokens(source);
  const parts = splitTop(tokens, "=>");
  const body = parts.at(-1)!;
  const context: Constraint[] = [];
  for (const part of parts.slice(0, -1)) {
    const stripped = part[0] === "(" && part.at(-1) === ")" ? part.slice(1, -1) : part;
    for (const item of splitTop(stripped, ",")) {
      if (item.length < 2) continue;
      context.push({ cls: unqualify(item[0]!), types: new TypeParser(item.slice(1), vars).argList() });
    }
  }
  return { context, type: new TypeParser(body, vars).fun() };
}

const parseType = (source: string, vars: Map<string, Type>): Type => parseSignature(source, vars).type;

// ------------------------------------------------------------ class info ---

interface ClassMethod {
  name: string;
  /** The declared signature, with the class variable still free. */
  type: Type;
  /** `$dm<name>`, when the class body supplies a default. */
  hasDefault: boolean;
}

interface ClassInfo {
  name: string;
  /** One per class parameter, in declaration order. A method's signature and
   * every superclass constraint are written over exactly these. */
  variables: TVar[];
  /** Over `variables`, so `class Monad m => MonadState s m` remembers that its
   * superclass is `Monad m` and not `Monad s`. */
  superclasses: Constraint[];
  /** `| m -> s`, as indices into `variables`. */
  fundeps: Array<{ from: number[]; to: number[] }>;
  methods: ClassMethod[];
  span: Span;
}

interface InstanceInfo {
  cls: string;
  /** The instance head's arguments, with their own free type variables: `[a]`
   * for `instance Eq a => Eq [a]`, `[s, StateT s m]` for `instance Monad m =>
   * MonadState s (StateT s m)`. Resolution matches a wanted against all of
   * them at once. */
  targets: Type[];
  targetCons: Array<string | undefined>;
  /** `targetCons` made safe to spell inside a generated identifier. */
  emitCon: string;
  /** The instance context, over `target`'s variables. Non-empty makes the
   * instance's dictionary a *function* of the dictionaries it names. */
  context: Constraint[];
  /** The context as named parameters, shared by the dictionary CAF and by
   * every method implementation, so the two agree on argument order. */
  params: Given[];
  methods: Map<string, ValueDeclaration>;
  span: Span;
}

/** A type constructor's name as it may appear inside a generated identifier;
 * `[]` and friends are legal type constructors but not legal name fragments. */
const conKey = (con: string): string =>
  con === "[]" ? "List" : con === "->" ? "Fun" : /^\(,+\)$/.test(con) ? `Tuple${con.length - 1}` : con;

/** One-way matching: instantiate the *pattern*'s variables only, so a wanted
 * type is never mutated by trying an instance that does not apply. */
function matchType(pattern: Type, target: Type, subst: Map<TVar, Type>): boolean {
  const p = prune(pattern);
  const t = prune(target);
  if (p.tag === "var") {
    const previous = subst.get(p.v);
    if (!previous) {
      subst.set(p.v, t);
      return true;
    }
    return sameType(previous, t);
  }
  if (p.tag === "con") return t.tag === "con" && t.name === p.name;
  if (p.tag === "app") return t.tag === "app" && matchType(p.fn, t.fn, subst) && matchType(p.arg, t.arg, subst);
  return false;
}

function applySubst(t: Type, subst: ReadonlyMap<TVar, Type>): Type {
  const p = prune(t);
  if (p.tag === "var") return subst.get(p.v) ?? p;
  if (p.tag === "app") return tapp(applySubst(p.fn, subst), applySubst(p.arg, subst));
  return p;
}

/** `applySubst` for an instance's own types, giving a *fresh* variable to
 * anything the match left unbound. An instance's variables are shared by every
 * use of it, so unifying one of them directly would silently specialise the
 * instance for the whole program. */
function freshen(t: Type, subst: Map<TVar, Type>): Type {
  const p = prune(t);
  if (p.tag === "var") {
    const known = subst.get(p.v);
    if (known) return known;
    const made = freshVar();
    subst.set(p.v, made);
    return made;
  }
  if (p.tag === "app") return tapp(freshen(p.fn, subst), freshen(p.arg, subst));
  return p;
}

function showType(t: Type): string {
  const p = prune(t);
  if (p.tag === "con") return p.name;
  if (p.tag === "app") return `(${showType(p.fn)} ${showType(p.arg)})`;
  return p.tag === "var" ? `t${p.v.id}` : `g${p.index}`;
}

const dictType = (cls: string): string => `Dict_${cls}`;
const dictCon = (cls: string): string => `MkDict_${cls}`;
const dictValue = (cls: string, target: string): string => `$f${cls}${target}`;
const methodImpl = (cls: string, target: string, method: string): string => `$c${cls}${target}$${method}`;
const defaultImpl = (cls: string, method: string): string => `$dm${cls}$${method}`;
const superSelector = (cls: string, index: number): string => `$p${index}${cls}`;

// -------------------------------------------------------- elaboration -----

type EnvEntry =
  | { tag: "poly"; scheme: Scheme; emit: string }
  | { tag: "mono"; type: Type }
  /** A member of the binding group currently being inferred: its use is
   * monomorphic, but it may still need this group's dictionaries. */
  | { tag: "group"; type: Type; name: string };

type Env = Map<string, EnvEntry>;

/** A dictionary-needing occurrence, recorded during inference and turned into
 * real syntax only once constraint solving has finished. */
type Use =
  | { kind: "apply"; node: Expr; emit: string; constraints: Constraint[] }
  | { kind: "literal"; node: Expr; type: Type; cls: "Num" | "Fractional" }
  | { kind: "group"; node: Expr; target: string };

/** What a binding was told, or worked out, about its own constraints. */
interface Given {
  cls: string;
  types: Type[];
  name: string;
}

interface Binding {
  name: string;
  decl: ValueDeclaration;
  /** Present when the source (or this pass, for an instance method) declared
   * a signature; its context fixes the dictionary parameters. */
  scheme?: Scheme;
  signature?: { context: Constraint[]; type: Type };
  /** The same signature with its variables still quantifiable: what callers
   * instantiate. The skolemised copy above is what the body is checked
   * against, and its rigid variables must never escape into a call site. */
  declaredScheme?: Scheme;
  givens: Given[];
  uses: Use[];
  intPatterns: Array<{ pattern: Extract<Pattern, { tag: "int" }>; type: Type }>;
  monoType: Type;
  emitted?: Scheme;
}

class Elaborator {
  readonly diagnostics: Diagnostic[] = [];
  readonly classes = new Map<string, ClassInfo>();
  /** Keyed `Class Con...`, one entry per instance head. */
  readonly instances = new Map<string, InstanceInfo>();
  /** The same instances grouped by class: selection matches every argument, so
   * it has to consider each of a class's instances rather than index by one. */
  private readonly byClass = new Map<string, InstanceInfo[]>();
  readonly constructors = new Map<string, Scheme>();
  readonly bindings = new Map<string, Binding>();
  readonly boxedInt = new Set<Extract<Pattern, { tag: "int" }>>();
  private current?: Binding;

  constructor(private readonly file: string) {}

  report(message: string, span: Span): void {
    this.diagnostics.push(error("GHCTS-DICT", message, this.file, span.line, span.column));
  }

  // ------------------------------------------------------------ patterns --

  inferPattern(p: Pattern, env: Env): Type {
    switch (p.tag) {
      case "wild":
        return freshVar();
      case "var": {
        const t = freshVar();
        env.set(p.name, { tag: "mono", type: t });
        return t;
      }
      case "as": {
        const t = this.inferPattern(p.pattern, env);
        env.set(p.name, { tag: "mono", type: t });
        return t;
      }
      case "int": {
        const t = freshVar();
        this.current?.intPatterns.push({ pattern: p, type: t });
        return t;
      }
      case "string":
        return tString;
      case "char":
        return tcon("Char");
      case "con": {
        const scheme = this.constructors.get(p.name);
        if (!scheme) {
          this.report(`data constructor \`${p.name}\` is not in scope`, p.span);
          for (const arg of p.args) this.inferPattern(arg, env);
          return freshVar();
        }
        let type = instantiate(scheme).type;
        for (const arg of p.args) {
          const argType = this.inferPattern(arg, env);
          const result = freshVar();
          if (!unify(type, tfun(argType, result))) this.report(`constructor \`${p.name}\` applied to too many patterns`, p.span);
          type = result;
        }
        return type;
      }
      case "record":
        this.report("record patterns are not supported", p.span);
        return freshVar();
    }
  }

  // --------------------------------------------------------- expressions --

  infer(e: Expr, env: Env): Type {
    switch (e.tag) {
      case "int": {
        const t = freshVar();
        this.current?.uses.push({ kind: "literal", node: e, type: t, cls: "Num" });
        return t;
      }
      // A fractional literal wants `Fractional`, not `Num`: `0.5 :: Int` is a
      // type error in Haskell and must stay one here.
      case "double": {
        const t = freshVar();
        this.current?.uses.push({ kind: "literal", node: e, type: t, cls: "Fractional" });
        return t;
      }
      case "string":
        return tString;
      case "char":
        return tcon("Char");
      case "unit":
        return tcon("()");
      case "var":
        return this.inferVar(e, env);
      case "app": {
        const fnType = this.infer(e.fn, env);
        const argType = this.infer(e.arg, env);
        const result = freshVar();
        if (!unify(fnType, tfun(argType, result))) this.report("type mismatch in application", e.span);
        return result;
      }
      case "lambda": {
        const inner = new Map(env);
        const param = freshVar();
        inner.set(e.parameter, { tag: "mono", type: param });
        return tfun(param, this.infer(e.body, inner));
      }
      case "lambdaCase": {
        const scrutinee = freshVar();
        const result = freshVar();
        this.inferAlternatives(e.alternatives, scrutinee, result, env, e.span);
        return tfun(scrutinee, result);
      }
      case "if": {
        if (!unify(this.infer(e.condition, env), tBool)) this.report("`if` condition is not a Bool", e.span);
        const t = this.infer(e.thenBranch, env);
        if (!unify(t, this.infer(e.elseBranch, env))) this.report("`if` branches have different types", e.span);
        return t;
      }
      case "case": {
        const scrutinee = this.infer(e.subject, env);
        const result = freshVar();
        this.inferAlternatives(e.alternatives, scrutinee, result, env, e.span);
        return result;
      }
      case "let": {
        const inner = this.inferLocals(e.bindings, env);
        return this.infer(e.body, inner);
      }
      case "tuple": {
        const items = e.items.map((item) => this.infer(item, env));
        return items.reduce((acc, item) => tapp(acc, item), tcon(`(${",".repeat(items.length - 1)})`));
      }
      case "list": {
        const item = freshVar();
        for (const entry of e.items) {
          if (!unify(item, this.infer(entry, env))) this.report("list elements have different types", e.span);
        }
        return tlist(item);
      }
      case "do":
        this.report("do notation needs a Monad dictionary, which is not elaborated yet", e.span);
        return freshVar();
      case "listComp":
      case "record":
      case "recordUpdate":
      case "jsQuote":
        this.report(`\`${e.tag}\` is not supported by the dictionary frontend`, e.span);
        return freshVar();
    }
  }

  private inferVar(e: Extract<Expr, { tag: "var" }>, env: Env): Type {
    const entry = env.get(e.name);
    if (entry) {
      if (entry.tag === "mono") return entry.type;
      if (entry.tag === "group") {
        this.current?.uses.push({ kind: "group", node: e, target: entry.name });
        return entry.type;
      }
      const { type, constraints } = instantiate(entry.scheme);
      if (constraints.length || entry.emit !== e.name) {
        this.current?.uses.push({ kind: "apply", node: e, emit: entry.emit, constraints });
      }
      return type;
    }
    const con = this.constructors.get(e.name);
    if (con) return instantiate(con).type;
    this.report(`\`${e.name}\` is not in scope`, e.span);
    return freshVar();
  }

  private inferAlternatives(alts: CaseAlternative[], scrutinee: Type, result: Type, env: Env, span: Span): void {
    for (const alt of alts) {
      const inner = new Map(env);
      if (!unify(scrutinee, this.inferPattern(alt.pattern, inner))) this.report("pattern does not match the scrutinee type", span);
      if (alt.guard && !unify(this.infer(alt.guard, inner), tBool)) this.report("guard is not a Bool", span);
      if (alt.patternGuards?.length) this.report("pattern guards are not supported", span);
      if (!unify(result, this.infer(alt.body, inner))) this.report("case alternatives have different types", span);
    }
  }

  /** `let`/`where` groups are inferred monomorphically: their constraints
   * float out to the enclosing top-level binding, which is where dictionaries
   * are actually bound. */
  private inferLocals(bindings: readonly LocalBinding[], env: Env): Env {
    const inner = new Map(env);
    const types = bindings.map(() => freshVar());
    bindings.forEach((b, i) => inner.set(b.name, { tag: "mono", type: types[i]! }));
    bindings.forEach((binding, i) => {
      const scope = new Map(inner);
      let result = types[i]!;
      for (const pattern of binding.patterns) {
        const argType = this.inferPattern(pattern, scope);
        const next = freshVar();
        if (!unify(result, tfun(argType, next))) this.report("binding parameters do not match its type", binding.span);
        result = next;
      }
      this.inferGuards(binding.guards ?? [{ body: binding.value }], binding.whereBindings ?? [], result, scope, binding.span);
    });
    return inner;
  }

  private inferGuards(guards: readonly Guard[], where: readonly LocalBinding[], result: Type, env: Env, span: Span): void {
    const scope = this.inferLocals(where, env);
    for (const guard of guards) {
      if (guard.condition && !unify(this.infer(guard.condition, scope), tBool)) this.report("guard is not a Bool", span);
      if (guard.pattern) this.report("pattern guards are not supported", span);
      if (!unify(result, this.infer(guard.body, scope))) this.report("guarded bodies have different types", span);
    }
  }

  inferBinding(binding: Binding, env: Env): void {
    this.current = binding;
    for (const equation of binding.decl.equations) {
      const scope = new Map(env);
      let result = binding.monoType;
      for (const pattern of equation.patterns) {
        const argType = this.inferPattern(pattern, scope);
        const next = freshVar();
        if (!unify(result, tfun(argType, next))) this.report(`\`${binding.name}\` has inconsistent equation arities`, binding.decl.span);
        result = next;
      }
      this.inferGuards(equation.guards, equation.whereBindings, result, scope, binding.decl.span);
    }
    this.current = undefined;
  }

  // ------------------------------------------------------------- solving --

  addInstance(key: string, info: InstanceInfo): void {
    this.instances.set(key, info);
    const group = this.byClass.get(info.cls);
    if (group) group.push(info);
    else this.byClass.set(info.cls, [info]);
  }

  /** Every constraint the binding still owes, in occurrence order. */
  private wanted(binding: Binding): Constraint[] {
    return binding.uses.flatMap((use) =>
      use.kind === "apply" ? use.constraints : use.kind === "literal" ? [{ cls: use.cls, types: [use.type] }] : [],
    );
  }

  /** Functional-dependency improvement, GHC's `GHC/Tc/Instance/FunDeps.hs`.
   *
   * `class MonadState s m | m -> s` promises that `m` fixes `s`. So whenever a
   * wanted's *determining* arguments are already the same as a given's, or
   * match an instance head's, its *determined* arguments must be whatever that
   * given or instance says they are, and are unified with them. This is not
   * decoration: `get :: MonadState s m => m s` mentions `s` nowhere else, so
   * without improvement every `n <- get` leaves `s` an unsolved variable and no
   * dictionary can be selected for it.
   *
   * Improvement only ever *unifies*; it never chooses a dictionary. Selection
   * still happens in `resolve`, against the improved types. */
  private improveConstraint(
    wanted: Constraint,
    givens: readonly Constraint[],
    span: Span,
    depth: number,
  ): boolean {
    const info = this.classes.get(wanted.cls);
    if (!info || info.fundeps.length === 0 || depth > 16) return false;
    const arg = (c: Constraint, i: number): Type | undefined => c.types[i];
    let changed = false;
    const improveTo = (from: Type | undefined, to: Type): void => {
      if (from === undefined || sameType(from, to)) return;
      if (unify(from, to)) {
        changed = true;
        return;
      }
      // Two sources disagree about a determined argument. In legal Haskell the
      // instances of a class are fundep-consistent, so this is a real error in
      // the program rather than a solver limitation.
      this.report(
        `functional dependency of \`${info.name}\` makes \`${showType(from)}\` and \`${showType(to)}\` the same type`,
        span,
      );
    };
    for (const fd of info.fundeps) {
      for (const given of givens) {
        if (given.cls !== wanted.cls) continue;
        if (!fd.from.every((i) => { const g = arg(given, i); const w = arg(wanted, i); return g !== undefined && w !== undefined && sameType(g, w); })) continue;
        for (const i of fd.to) improveTo(arg(wanted, i), arg(given, i) ?? freshVar());
      }
      for (const instance of this.byClass.get(wanted.cls) ?? []) {
        // One-way matching: the instance's variables are instantiated, the
        // wanted's are not. A wanted whose determining argument is still an
        // unsolved variable therefore matches nothing and stays unimproved,
        // which is what stops improvement from inventing a type.
        const subst = new Map<TVar, Type>();
        if (!fd.from.every((i) => { const t = instance.targets[i]; const w = arg(wanted, i); return t !== undefined && w !== undefined && matchType(t, w, subst); })) continue;
        for (const i of fd.to) {
          const target = instance.targets[i];
          if (target) improveTo(arg(wanted, i), freshen(target, subst));
        }
        // A lifting instance determines nothing on its own: `MonadState s
        // (ReaderT r m)` learns its `s` from its own context, so improvement
        // continues into that context under the same substitution - which is
        // what carries the fundep down through a transformer stack.
        for (const c of instance.context) {
          if (this.improveConstraint({ cls: c.cls, types: c.types.map((t) => freshen(t, subst)) }, givens, span, depth + 1))
            changed = true;
        }
      }
    }
    return changed;
  }

  private improve(binding: Binding): void {
    const givens = binding.signature?.context ?? [];
    // Improving one constraint can expose another (a determined argument may
    // be some other wanted's determining one), so this runs to a fixed point.
    for (let round = 0; round < 8; round++) {
      let changed = false;
      for (const wanted of this.wanted(binding)) {
        if (this.improveConstraint(wanted, givens, binding.decl.span, 0)) changed = true;
      }
      if (!changed) return;
    }
  }

  /** Discharge one constraint, producing the expression that names its
   * dictionary. A given wins over an instance, and a superclass field of a
   * given wins over nothing at all. */
  resolve(cls: string, types: readonly Type[], givens: readonly Given[], span: Span, depth = 0): Expr | undefined {
    const queue: Array<{ cls: string; types: Type[]; expr: Expr }> = givens.map((g) => ({
      cls: g.cls,
      types: g.types,
      expr: variable(g.name, span),
    }));
    const seen = new Set(queue.map((item) => showConstraint(item.cls, item.types)));
    while (queue.length) {
      const item = queue.shift()!;
      if (item.cls === cls && sameTypes(item.types, types)) return item.expr;
      const info = this.classes.get(item.cls);
      if (!info) continue;
      // A superclass constraint is written over the class's own variables, so
      // reaching it means instantiating them at the arguments in hand:
      // `class Monad m => MonadState s m` gives `Monad m`, never `Monad s`.
      const at = new Map<TVar, Type>(info.variables.map((v, i) => [v, item.types[i] ?? varType(v)]));
      info.superclasses.forEach((parent, index) => {
        const parentTypes = parent.types.map((t) => applySubst(t, at));
        const key = showConstraint(parent.cls, parentTypes);
        if (seen.has(key)) return;
        seen.add(key);
        queue.push({
          cls: parent.cls,
          types: parentTypes,
          expr: apply(variable(superSelector(item.cls, index), span), item.expr),
        });
      });
    }
    const con = types.length === 1 ? headCon(types[0]!) : undefined;
    // `IntPrim` is the machine integer itself, so a `Num IntPrim` wanted is
    // discharged by the literal staying raw; there is no dictionary to name.
    if (con === "IntPrim" && cls === "Num") return undefined;
    // Likewise `DoublePrim`: a fractional literal at the machine type stays a
    // raw `LitDouble`, so there is no `Fractional` dictionary to name.
    if (con === "DoublePrim" && cls === "Fractional") return undefined;
    // A constrained instance is a function from dictionaries to a dictionary,
    // so selecting it is recursive. The depth bound is what turns a
    // non-terminating instance chain into a diagnostic instead of a hang.
    if (depth > 32) {
      this.report(`instance resolution for \`${showConstraint(cls, types)}\` did not terminate`, span);
      return undefined;
    }
    for (const instance of this.byClass.get(cls) ?? []) {
      const subst = new Map<TVar, Type>();
      if (!types.every((t, i) => { const target = instance.targets[i]; return target !== undefined && matchType(target, t, subst); })) continue;
      const self = variable(dictValue(cls, instance.emitCon), span);
      if (instance.context.length === 0) return self;
      return applyAll(
        self,
        instance.context.map(
          (c) => this.resolve(c.cls, c.types.map((t) => applySubst(t, subst)), givens, span, depth + 1) ?? errorExpr(span),
        ),
      );
    }
    // Nothing matched. A constraint still entirely on unsolved variables is
    // reported by whatever left it ambiguous, not here; one that names a type
    // constructor genuinely has no instance.
    if (types.some((t) => headCon(t) !== undefined)) this.report(`no instance for \`${showConstraint(cls, types)}\``, span);
    return undefined;
  }

  /** Ambiguous numeric constraints default to `Int`, which is what makes
   * `main = show (1 + 2)` a program rather than a type error. */
  private applyDefaulting(binding: Binding): void {
    const wanted = this.wanted(binding);
    for (const c of wanted) {
      // Defaulting is a numeric-class rule, and both `Num` and `Fractional`
      // take one argument; a multi-parameter constraint is never defaulted.
      if (c.types.length !== 1) continue;
      const t = prune(c.types[0]!);
      if (t.tag !== "var") continue;
      // A variable the binding is quantified over is not ambiguous: it is a
      // dictionary parameter, and defaulting it would erase the polymorphism.
      if (binding.givens.some((g) => g.types.some((gt) => sameType(gt, t)))) continue;
      const classes = wanted.filter((other) => other.types.length === 1 && sameType(other.types[0]!, t)).map((other) => other.cls);
      // Haskell's `default (Integer, Double)`: a `Fractional` wanted rules
      // `Int` out, so the same ambiguous variable defaults to `Double`.
      if (classes.includes("Fractional")) unify(t, tcon("Double"));
      else if (classes.includes("Num")) unify(t, tInt);
    }
  }

  /** Fix each integer pattern's representation. Doing it here, once the
   * binding is fully inferred, is what lets `f 0 = ...` stay a structural
   * match on `I 0` while a pattern on an unboxed scrutinee stays raw. */
  private solveIntPatterns(binding: Binding): void {
    for (const { pattern, type } of binding.intPatterns) {
      const t = prune(type);
      if (t.tag === "var") unify(t, tInt);
      const con = headCon(type);
      if (con === "IntPrim") continue;
      if (con === "Int") {
        this.boxedInt.add(pattern);
        continue;
      }
      this.report(`integer pattern at type \`${con ?? "?"}\`: literal patterns are only supported at Int`, pattern.span);
    }
  }

  /** Turn a fully inferred binding into its dictionary parameters and scheme,
   * then rewrite every occurrence inside it. */
  finish(binding: Binding): void {
    // Improvement first: it only refines types, and everything below - which
    // constraints are generalised, what defaults, which dictionary is selected
    // - reads those types.
    this.improve(binding);
    this.solveIntPatterns(binding);

    if (binding.signature) {
      binding.givens = binding.signature.context.map((c, i) => ({ cls: c.cls, types: c.types, name: `$d${i}` }));
    } else if (binding.decl.equations[0]?.patterns.length) {
      // No signature but genuine parameters: generalise, and every wanted
      // constraint on a generalised variable becomes a dictionary parameter.
      const quantified = typeVars(binding.monoType);
      const params: Given[] = [];
      for (const c of this.wanted(binding)) {
        const ts = c.types.map(prune);
        // A constraint counts as generalised when it *mentions* a quantified
        // variable, not only when it is one: `Eq [a]` is as much a dictionary
        // parameter as `Eq a`, and dropping it would leave it unsolvable.
        const vars = ts.flatMap((t) => typeVars(t));
        if (vars.length === 0 || !vars.some((v) => quantified.includes(v))) continue;
        if (params.some((p) => p.cls === c.cls && sameTypes(p.types, ts))) continue;
        params.push({ cls: c.cls, types: ts, name: `$d${params.length}` });
      }
      binding.givens = params;
    }

    this.applyDefaulting(binding);

    binding.emitted =
      binding.declaredScheme ??
      quantify(
        binding.signature ? [] : typeVars(binding.monoType),
        binding.signature?.type ?? binding.monoType,
        binding.givens.map((g) => ({ cls: g.cls, types: g.types })),
      );
  }

  /** The dictionaries a use needs, in the order its callee expects them. */
  dictionariesFor(use: Use, binding: Binding): Expr[] {
    const span = spanOf(use.node);
    if (use.kind === "group") {
      const target = this.bindings.get(use.target);
      return (target?.givens ?? []).map((g) => this.resolve(g.cls, g.types, binding.givens, span) ?? errorExpr(span));
    }
    if (use.kind === "literal" && headCon(use.type) === "IntPrim") return [];
    if (use.kind === "literal" && headCon(use.type) === "DoublePrim") return [];
    const constraints: Constraint[] =
      use.kind === "literal" ? [{ cls: use.cls, types: [use.type] }] : use.constraints;
    return constraints.map((c) => this.resolve(c.cls, c.types, binding.givens, span) ?? errorExpr(span));
  }
}

// ------------------------------------------------------- syntax builders ---

const NOWHERE: Span = { start: 0, end: 0, line: 0, column: 0 };
const variable = (name: string, span: Span = NOWHERE): Expr => ({ tag: "var", name, span });
const apply = (fn: Expr, arg: Expr): Expr => ({ tag: "app", fn, arg, span: spanOf(fn) });
const applyAll = (fn: Expr, args: Expr[]): Expr => args.reduce(apply, fn);
const errorExpr = (span: Span): Expr => ({ tag: "var", name: "$dictionaryNotFound", span });
const spanOf = (e: Expr): Span => e.span;
const varType = (v: TVar): Type => ({ tag: "var", v });

const valueDecl = (name: string, patterns: Pattern[], body: Expr, span: Span = NOWHERE): ValueDeclaration => ({
  tag: "value",
  name,
  equations: [{ patterns, guards: [{ body }], whereBindings: [] }],
  span,
});

// --------------------------------------------------------------- driver ----

export function elaborateModule(user: Module, file = `${user.name}.hs`): ElaborateResult {
  return elaborateProgram(new Map([[user.name, user]]), user.name, file);
}

/** Compile a set of modules as one program, rooted at `root`.  The modules are
 * ordered by their imports and merged into the single flat declaration pile
 * this pass has always worked on, each module's uses first rewritten through
 * its own scope by `src/modules.ts`. */
export function elaborateProgram(
  modules: ReadonlyMap<string, Module>,
  root: string,
  file = `${root}.hs`,
): ElaborateResult {
  nextTVar = 0;
  const user = modules.get(root) ?? { name: root, imports: [], exports: [], reexports: [], declarations: [] };
  // The compiler's own library modules join the program before resolution, so
  // they are ordered, renamed and scoped exactly like any other module - and a
  // project module of the same name shadows them.
  const resolved = resolveProgram(withLibraryModules(modules), root);
  const elaborator = new Elaborator(file);
  const prelude = parseModule(PRELUDE_SOURCE, "GHCTS/Prelude.hs");
  if (!prelude.module || prelude.diagnostics.some((d) => d.severity === "error")) {
    return { module: user, diagnostics: prelude.diagnostics };
  }
  elaborator.diagnostics.push(...resolved.diagnostics);
  if (resolved.diagnostics.some((d) => d.severity === "error"))
    return { module: user, diagnostics: elaborator.diagnostics };
  // Instance and class declarations keep their members as unparsed source, so
  // the scope they were written in has to survive until those members are
  // parsed, further down.
  const scopeOf = new Map<Declaration, Scope>();
  const declarations: Declaration[] = [...prelude.module.ast.declarations];
  for (const module of resolved.order) {
    const scope = resolved.scopes.get(module.name)!;
    for (const decl of renameDeclarations(module, scope, module.name === root)) {
      scopeOf.set(decl, scope);
      declarations.push(decl);
    }
  }
  const env: Env = new Map();

  // --- type synonyms ----------------------------------------------------
  // Expanded wherever a type is parsed, so `MisoString` and `Text` are one
  // type and an instance written at either head is found from both.
  synonyms = new Map();
  for (const decl of declarations) {
    if (decl.tag !== "typeAlias" || !/^[A-Z]/.test(decl.name)) continue;
    synonyms.set(decl.name, { parameters: decl.parameters, target: decl.target });
  }

  // --- data constructors -----------------------------------------------
  const datas = declarations.filter((d): d is DataDeclaration => d.tag === "data");
  for (const decl of datas) {
    for (const con of decl.constructors) {
      const vars = new Map<string, Type>();
      const result = decl.parameters.reduce<Type>((acc, name) => {
        const v = freshVar();
        vars.set(name, v);
        return tapp(acc, v);
      }, tcon(decl.name));
      const fields = (con.fieldTypes ?? Array.from({ length: con.arity }, () => "_field")).map((f) => parseType(f, vars));
      const type = fields.reduceRight((acc, field) => tfun(field, acc), result);
      elaborator.constructors.set(con.name, quantify(typeVars(type), type, []));
    }
  }
  const listVar = freshVar();
  elaborator.constructors.set("[]", quantify(typeVars(tlist(listVar)), tlist(listVar), []));
  const consVar = freshVar();
  elaborator.constructors.set(
    ":",
    quantify(typeVars(tfun(consVar, tfun(tlist(consVar), tlist(consVar)))), tfun(consVar, tfun(tlist(consVar), tlist(consVar))), []),
  );
  // Tuple constructors. `(x, y)` reaches this pass as a `tuple` expression but
  // as a `con` *pattern* named `(,)`, and `(,)` is also a legal value; all
  // three want the same scheme. `src/desugar.ts` invents the matching DataCon
  // on demand, so the two ends agree without a declaration anywhere.
  elaborator.constructors.set("()", { gens: 0, constraints: [], type: tcon("()") });
  for (let arity = 2; arity <= 7; arity++) {
    const name = `(${",".repeat(arity - 1)})`;
    const fields = Array.from({ length: arity }, () => freshVar());
    const type = fields.reduceRight((acc, field) => tfun(field, acc), fields.reduce<Type>(tapp, tcon(name)));
    elaborator.constructors.set(name, quantify(typeVars(type), type, []));
  }

  // --- primitives -------------------------------------------------------
  for (const [name, signature] of Object.entries(PRIMITIVE_TYPES)) {
    env.set(name, { tag: "poly", scheme: { gens: 0, constraints: [], type: parseType(signature, new Map()) }, emit: name });
  }

  // --- classes ----------------------------------------------------------
  const classDecls = declarations.filter((d): d is ClassDeclaration => d.tag === "class");
  const defaults = new Map<string, ValueDeclaration>();
  for (const decl of classDecls) {
    if (decl.parameters.length === 0) {
      elaborator.report(`class \`${decl.name}\`: a class must have at least one parameter`, decl.span);
      continue;
    }
    const vars = new Map<string, Type>();
    const variables: TVar[] = [];
    for (const parameter of decl.parameters) {
      const made = freshVar();
      if (made.tag !== "var") continue;
      vars.set(parameter, made);
      variables.push(made.v);
    }
    // Parsed against the same variable map as the methods, so `m` in
    // `class Monad m => MonadState s m` is the class's own second parameter.
    const supers = superclassesOf(decl, vars);
    const fundeps = decl.fundeps.flatMap((fd) => {
      const index = (name: string): number => decl.parameters.indexOf(name);
      const from = fd.from.map(index);
      const to = fd.to.map(index);
      if ([...from, ...to].some((i) => i < 0)) {
        elaborator.report(`class \`${decl.name}\`: a functional dependency names a parameter it does not have`, decl.span);
        return [];
      }
      return [{ from, to }];
    });
    const own = new Map<string, ValueDeclaration>();
    const classScope = scopeOf.get(decl);
    for (const value of instanceMethodValues(
      { tag: "instance", head: decl.name, members: [], rawMembers: decl.rawMembers, span: decl.span },
      file,
    )) {
      own.set(value.name, classScope ? renameValue(value, classScope) : value);
    }
    const methods: ClassMethod[] = [];
    for (const member of decl.members) {
      if (member.tag !== "signature") continue;
      methods.push({ name: member.name, type: parseType(member.type, vars), hasDefault: own.has(member.name) });
      if (own.has(member.name)) defaults.set(defaultImpl(decl.name, member.name), own.get(member.name)!);
    }
    elaborator.classes.set(decl.name, { name: decl.name, variables, superclasses: supers, fundeps, methods, span: decl.span });
  }

  // A method's scheme is its declared signature plus its own class constraint,
  // quantified over the class variable first so the dictionary is argument
  // zero at every call site.
  for (const info of elaborator.classes.values()) {
    for (const method of info.methods) {
      const ordered = [...info.variables, ...typeVars(method.type).filter((v) => !info.variables.includes(v))];
      env.set(method.name, {
        tag: "poly",
        scheme: quantify(ordered, method.type, [{ cls: info.name, types: info.variables.map(varType) }]),
        emit: method.name,
      });
    }
  }

  // --- instances --------------------------------------------------------
  const instanceDecls = declarations.filter((d): d is InstanceDeclaration => d.tag === "instance");
  for (const decl of instanceDecls) {
    const parsed = instanceHead(decl.head);
    if (!parsed) {
      elaborator.report(`instance \`${decl.head}\`: unrecognised head`, decl.span);
      continue;
    }
    const info = elaborator.classes.get(parsed.className);
    if (!info) {
      elaborator.report(`instance for unknown class \`${parsed.className}\``, decl.span);
      continue;
    }
    // Head and context are parsed against one variable map, so `a` in
    // `Eq a => Eq [a]` is the same type variable in both.
    const vars = new Map<string, Type>();
    const context = parseSignature(decl.head, vars).context;
    const targets = new TypeParser(TypeParser.tokens(parsed.target), vars).argList();
    const targetCons = targets.map((t) => headCon(t));
    if (targets.length !== info.variables.length) {
      elaborator.report(`instance \`${decl.head}\`: \`${info.name}\` takes ${info.variables.length} argument(s)`, decl.span);
      continue;
    }
    if (targetCons.every((con) => con === undefined)) {
      elaborator.report(`instance \`${decl.head}\`: the instance head must have a type constructor`, decl.span);
      continue;
    }
    const methods = new Map<string, ValueDeclaration>();
    const instanceScope = scopeOf.get(decl);
    for (const value of instanceMethodValues(decl, file))
      methods.set(value.name, instanceScope ? renameValue(value, instanceScope) : value);
    elaborator.addInstance(`${parsed.className} ${targetCons.map((c) => c ?? "_").join(" ")}`, {
      cls: parsed.className,
      targets,
      targetCons,
      // A variable argument contributes `v`, so the two heads of a
      // multi-parameter class still name two different dictionaries.
      emitCon: targetCons.map((con) => (con === undefined ? "v" : conKey(con))).join(""),
      context,
      params: context.map((c, i) => ({ cls: c.cls, types: c.types, name: `$d${i}` })),
      methods,
      span: decl.span,
    });
  }

  // `deriving Eq` is an instance like any other: one constrained by `Eq` at
  // each type parameter, whose `==` is the structural comparison.
  for (const decl of datas) {
    if (!decl.deriving.includes("Eq") || elaborator.instances.has(`Eq ${decl.name}`)) continue;
    const vars = decl.parameters.map(() => freshVar());
    const context = vars.map((type) => ({ cls: "Eq", types: [type] }));
    elaborator.addInstance(`Eq ${decl.name}`, {
      cls: "Eq",
      targets: [vars.reduce<Type>(tapp, tcon(decl.name))],
      targetCons: [decl.name],
      emitCon: conKey(decl.name),
      context,
      params: context.map((c, i) => ({ cls: c.cls, types: c.types, name: `$d${i}` })),
      methods: new Map([["==", derivedEqMethod(decl)]]),
      span: decl.span,
    });
  }

  // --- bindings to infer -------------------------------------------------
  const signatures = new Map(
    declarations.filter((d): d is SignatureDeclaration => d.tag === "signature").map((d) => [d.name, d.type]),
  );
  // Record selectors are ordinary top-level functions; a user binding of the
  // same name wins, exactly as a hand-written selector would.
  const cons = constructorTable(datas);
  const bound = new Set(declarations.flatMap((d) => (d.tag === "value" || d.tag === "foreign" ? [d.name] : [])));
  declarations.push(...fieldSelectors(datas, bound));

  const bindings: Binding[] = [];
  const addBinding = (
    name: string,
    original: ValueDeclaration,
    signature?: { context: Constraint[]; type: Type },
    declared?: { context: Constraint[]; type: Type },
  ): void => {
    // `do`, records and record patterns are expanded here, at the one point
    // every value - top level, instance method and class default - passes.
    const decl = expandSugar(original, cons, (message, span) => elaborator.report(message, span));
    const binding: Binding = {
      name,
      decl,
      signature,
      declaredScheme: declared
        ? quantify(
            [...typeVars(declared.type), ...declared.context.flatMap((c) => c.types.flatMap((t) => typeVars(t)))],
            declared.type,
            declared.context,
          )
        : undefined,
      givens: [],
      uses: [],
      intPatterns: [],
      monoType: signature ? signature.type : freshVar(),
    };
    bindings.push(binding);
    elaborator.bindings.set(name, binding);
  };

  for (const decl of declarations) {
    if (decl.tag !== "value") continue;
    const signature = signatures.get(decl.name);
    // Parsed twice on purpose: the two copies must not share type variables,
    // since one is skolemised and the other is generalised.
    addBinding(
      decl.name,
      decl,
      signature ? skolemise(parseSignature(signature, new Map())) : undefined,
      signature ? parseSignature(signature, new Map()) : undefined,
    );
  }
  for (const decl of declarations) {
    if (decl.tag !== "foreign") continue;
    const vars = new Map<string, Type>();
    const type = decl.signature.map((part) => parseType(part, vars)).reduceRight((acc, part) => tfun(part, acc));
    env.set(decl.name, { tag: "poly", scheme: quantify(typeVars(type), type, []), emit: decl.name });
  }

  // Instance methods and class defaults are ordinary bindings with a
  // synthesised signature: the class method's type at the instance's type, and
  // the class method's type under its own class constraint respectively.
  for (const instance of elaborator.instances.values()) {
    const info = elaborator.classes.get(instance.cls)!;
    for (const method of info.methods) {
      const decl = instance.methods.get(method.name);
      if (!decl) {
        if (!method.hasDefault) elaborator.report(`instance \`${instance.cls} ${instance.targetCons.join(" ")}\` has no \`${method.name}\` and the class has no default`, instance.span);
        continue;
      }
      // The instance context becomes the method's givens, so a method of
      // `instance Eq a => Eq [a]` takes the same `$d0` the dictionary does.
      const at = skolemise({
        context: instance.context,
        type: substituteVars(method.type, info.variables, instance.targets),
      });
      const implName = methodImpl(instance.cls, instance.emitCon, method.name);
      addBinding(implName, { ...decl, name: implName }, at);
    }
  }
  for (const info of elaborator.classes.values()) {
    for (const method of info.methods) {
      if (!method.hasDefault) continue;
      const decl = defaults.get(defaultImpl(info.name, method.name))!;
      const skolems = info.variables.map((_, i) => tcon(`%${info.name}${i}`));
      addBinding(
        defaultImpl(info.name, method.name),
        { ...decl, name: defaultImpl(info.name, method.name) },
        skolemise({
          context: [{ cls: info.name, types: skolems }],
          type: substituteVars(method.type, info.variables, skolems),
        }),
      );
    }
  }

  // --- inference, in dependency order ------------------------------------
  const order = orderBindings(bindings);
  for (const group of order) {
    const groupEnv = new Map(env);
    // A signature makes a binding usable *polymorphically* inside its own
    // recursive group, as in GHC. Without it two mutually recursive signatured
    // functions each see the other's skolemised type, whose rigid variables
    // cannot unify with their own - a type error in code that is well typed.
    for (const binding of group)
      groupEnv.set(
        binding.name,
        binding.declaredScheme
          ? { tag: "poly", scheme: binding.declaredScheme, emit: binding.name }
          : { tag: "group", type: binding.monoType, name: binding.name },
      );
    for (const binding of group) elaborator.inferBinding(binding, groupEnv);
    for (const binding of group) elaborator.finish(binding);
    for (const binding of group) {
      env.set(binding.name, { tag: "poly", scheme: binding.emitted!, emit: binding.name });
    }
  }

  // --- rewrite ------------------------------------------------------------
  // GHC declares `data [] a = [] | a : [a]` in GHC.Types; the parser has no
  // syntax for it, so it is supplied here. Without a declaration the desugarer
  // only learns the list constructors from the first expression that happens
  // to mention a list, which leaves `x : xs` in a *prefix* position - the shape
  // the parser gives every infix `:` - resolvable or not depending on
  // declaration order. The tags and arities are the ones it invents anyway.
  const listData: DataDeclaration = {
    tag: "data",
    name: "[]",
    parameters: ["a"],
    constructors: [
      { name: "[]", arity: 0 },
      { name: ":", arity: 2 },
    ],
    deriving: [],
    span: NOWHERE,
  };
  const out: Declaration[] = [listData, ...declarations.filter((d) => d.tag === "data" || d.tag === "foreign")];
  for (const info of elaborator.classes.values()) out.push(...classDeclarations(info));
  for (const instance of elaborator.instances.values()) {
    const built = instanceDeclaration(elaborator, instance);
    if (built) out.push(built);
  }
  // GHC's entry is `:Main.main = runMainIO Main.main`, and the JS backend's
  // `h$main` does nothing but *enter* that closure. An `IO` action here is a
  // function of a state token, so entering it would only yield the function;
  // the same wrapper GHC emits is what makes entry mean "run".
  const mainBinding = elaborator.bindings.get("main");
  const wrapMain = mainBinding !== undefined && headCon(mainBinding.monoType) === "IO";
  for (const binding of bindings) {
    const decl = rewriteBinding(elaborator, binding);
    if (binding !== mainBinding || !wrapMain) {
      out.push(decl);
      continue;
    }
    out.push({ ...decl, name: "$mainIO" });
    out.push(valueDecl("main", [], apply(variable("runMainIO", decl.span), variable("$mainIO", decl.span)), decl.span));
  }

  const roots = new Set(
    declarations
      .slice(prelude.module.ast.declarations.length)
      .flatMap((d) => (d.tag === "value" || d.tag === "foreign" ? [d.name] : [])),
  );
  return {
    module: { ...user, declarations: reachable(out, roots) },
    diagnostics: elaborator.diagnostics,
  };
}

/** Emit only what the program can reach from the user's own declarations.
 *
 * The Prelude is prepended to every module, and its dictionaries, selectors,
 * defaults and helpers are all real bindings; shipping the unused ones is not
 * only waste but a hard limit, because `src/js/optimizer.ts` recurses once per
 * statement in a block and overflows the stack on a few hundred closures.
 * GHC's linker keeps the reachable closure for the same reason, so this is
 * where that decision belongs rather than in a smaller Prelude.
 *
 * Data declarations are kept unconditionally: they emit no code, and the
 * desugarer needs every constructor a pattern might name. */
function reachable(out: readonly Declaration[], roots: ReadonlySet<string>): Declaration[] {
  const byName = new Map<string, ValueDeclaration[]>();
  for (const d of out) {
    if (d.tag !== "value") continue;
    const list = byName.get(d.name);
    if (list) list.push(d);
    else byName.set(d.name, [d]);
  }
  const seen = new Set<string>();
  const queue = [...roots];
  while (queue.length) {
    const name = queue.pop()!;
    if (seen.has(name)) continue;
    seen.add(name);
    for (const decl of byName.get(name) ?? []) for (const ref of referencedNames(decl)) queue.push(ref);
  }
  return out.filter((d) => (d.tag === "value" || d.tag === "foreign" ? seen.has(d.name) : true));
}

/** Primitive operations, typed over the unboxed types only. The comparisons
 * return `Bool` because the desugarer wraps their 0/1 machine result into the
 * real constructor - see `src/desugar.ts`. */
const PRIMITIVE_TYPES: Record<string, string> = {
  primIntAdd: "IntPrim -> IntPrim -> IntPrim",
  primIntSub: "IntPrim -> IntPrim -> IntPrim",
  primIntMul: "IntPrim -> IntPrim -> IntPrim",
  primIntQuot: "IntPrim -> IntPrim -> IntPrim",
  primIntRem: "IntPrim -> IntPrim -> IntPrim",
  primIntNeg: "IntPrim -> IntPrim",
  primIntEq: "IntPrim -> IntPrim -> Bool",
  primIntNe: "IntPrim -> IntPrim -> Bool",
  primIntLt: "IntPrim -> IntPrim -> Bool",
  primIntLe: "IntPrim -> IntPrim -> Bool",
  primIntGt: "IntPrim -> IntPrim -> Bool",
  primIntGe: "IntPrim -> IntPrim -> Bool",
  primChr: "IntPrim -> CharPrim",
  primCharOrd: "CharPrim -> IntPrim",
  primCharEq: "CharPrim -> CharPrim -> Bool",
  primCharLt: "CharPrim -> CharPrim -> Bool",
  primDoubleAdd: "DoublePrim -> DoublePrim -> DoublePrim",
  primDoubleSub: "DoublePrim -> DoublePrim -> DoublePrim",
  primDoubleMul: "DoublePrim -> DoublePrim -> DoublePrim",
  primDoubleDiv: "DoublePrim -> DoublePrim -> DoublePrim",
  primDoubleNeg: "DoublePrim -> DoublePrim",
  primDoubleAbs: "DoublePrim -> DoublePrim",
  primDoubleEq: "DoublePrim -> DoublePrim -> Bool",
  primDoubleLt: "DoublePrim -> DoublePrim -> Bool",
  primDoubleLe: "DoublePrim -> DoublePrim -> Bool",
  primDoubleGt: "DoublePrim -> DoublePrim -> Bool",
  primDoubleGe: "DoublePrim -> DoublePrim -> Bool",
  primDoubleSqrt: "DoublePrim -> DoublePrim",
  primDoubleLog: "DoublePrim -> DoublePrim",
  primDoubleExp: "DoublePrim -> DoublePrim",
  primDoublePower: "DoublePrim -> DoublePrim -> DoublePrim",
  primIntToDouble: "IntPrim -> DoublePrim",
  primDoubleToInt: "DoublePrim -> IntPrim",
  // `MutVarPrim`/`MVarPrim`/`VoidPrim` are opaque: nothing in Haskell may
  // scrutinise them, which is exactly the unlifted primitive types they stand
  // for. `VoidPrim` is the absent result of a primop that only has an effect;
  // the `case` that names it is what sequences the effect, and its binder is
  // never read.
  primNewMutVar: "a -> MutVarPrim a",
  primReadMutVar: "MutVarPrim a -> a",
  primWriteMutVar: "MutVarPrim a -> a -> VoidPrim",
  primNewMVar: "RealWorld -> MVarPrim a",
  primTakeMVar: "MVarPrim a -> a",
  primPutMVar: "MVarPrim a -> a -> VoidPrim",
  primReadMVar: "MVarPrim a -> a",
  primTryPutMVar: "MVarPrim a -> a -> Bool",
  primIsEmptyMVar: "MVarPrim a -> Bool",
  primFork: "a -> ThreadIdPrim",
  primDelay: "IntPrim -> VoidPrim",
};

/** `class Eq a => Ord a where` keeps only its name and parameters in the
 * surface AST, so the context is recovered from the class header the parser
 * preserved. */
function superclassesOf(decl: ClassDeclaration, vars: Map<string, Type>): Constraint[] {
  return decl.context.flatMap((item) => {
    const tokens = TypeParser.tokens(item);
    const cls = tokens[0];
    if (cls === undefined || !/^[A-Z]/.test(cls)) return [];
    return [{ cls: unqualify(cls), types: new TypeParser(tokens.slice(1), vars).argList() }];
  });
}

function substituteVar(type: Type, from: Type, to: Type): Type {
  const target = prune(from);
  const go = (t: Type): Type => {
    const p = prune(t);
    if (p.tag === "var" && target.tag === "var" && p.v === target.v) return to;
    if (p.tag === "app") return tapp(go(p.fn), go(p.arg));
    return p;
  };
  return go(type);
}

/** A class method's type at an instance's arguments: every class variable is
 * replaced at once, so `put :: s -> m ()` at `MonadState s (StateT s m)`
 * becomes `s -> StateT s m ()` and not a half-substituted type. */
function substituteVars(type: Type, from: readonly TVar[], to: readonly Type[]): Type {
  const subst = new Map<TVar, Type>(from.map((v, i) => [v, to[i] ?? varType(v)]));
  return applySubst(type, subst);
}

/** A declared signature's variables are rigid: the binding must work for every
 * instantiation, so they become opaque constructors and its constraints become
 * the only dictionaries available. */
function skolemise(signature: { context: Constraint[]; type: Type }): { context: Constraint[]; type: Type } {
  let type = signature.type;
  let context = signature.context;
  for (const v of [...typeVars(signature.type), ...signature.context.flatMap((c) => c.types.flatMap((t) => typeVars(t)))]) {
    const skolem = tcon(`%${v.id}`);
    const from: Type = { tag: "var", v };
    type = substituteVar(type, from, skolem);
    context = context.map((c) => ({ cls: c.cls, types: c.types.map((t) => substituteVar(t, from, skolem)) }));
  }
  return { context, type };
}

/** Dependency order, so a binding's scheme (and therefore its dictionary
 * parameters) is known before anything that calls it is inferred. Mutually
 * recursive bindings are inferred together and monomorphically. */
function orderBindings(bindings: readonly Binding[]): Binding[][] {
  const index = new Map(bindings.map((b, i) => [b.name, i]));
  const edges = bindings.map((b) => [...referencedNames(b.decl)].flatMap((name) => {
    const target = index.get(name);
    return target === undefined ? [] : [target];
  }));
  // Tarjan, iterative order not needed at this size.
  const lowlink = new Array<number>(bindings.length).fill(-1);
  const number = new Array<number>(bindings.length).fill(-1);
  const onStack = new Array<boolean>(bindings.length).fill(false);
  const stack: number[] = [];
  const groups: Binding[][] = [];
  let counter = 0;
  const strongconnect = (v: number): void => {
    number[v] = counter;
    lowlink[v] = counter;
    counter++;
    stack.push(v);
    onStack[v] = true;
    for (const w of edges[v]!) {
      if (number[w] === -1) {
        strongconnect(w);
        lowlink[v] = Math.min(lowlink[v]!, lowlink[w]!);
      } else if (onStack[w]) {
        lowlink[v] = Math.min(lowlink[v]!, number[w]!);
      }
    }
    if (lowlink[v] === number[v]) {
      const group: Binding[] = [];
      for (;;) {
        const w = stack.pop()!;
        onStack[w] = false;
        group.push(bindings[w]!);
        if (w === v) break;
      }
      groups.push(group);
    }
  };
  for (let v = 0; v < bindings.length; v++) if (number[v] === -1) strongconnect(v);
  return groups;
}

function referencedNames(decl: ValueDeclaration): Set<string> {
  const names = new Set<string>();
  const expr = (e: Expr): void => {
    switch (e.tag) {
      case "var":
        names.add(e.name);
        return;
      case "app":
        expr(e.fn);
        expr(e.arg);
        return;
      case "lambda":
        expr(e.body);
        return;
      case "lambdaCase":
        for (const alt of e.alternatives) alternative(alt);
        return;
      case "if":
        expr(e.condition);
        expr(e.thenBranch);
        expr(e.elseBranch);
        return;
      case "case":
        expr(e.subject);
        for (const alt of e.alternatives) alternative(alt);
        return;
      case "let":
        for (const b of e.bindings) local(b);
        expr(e.body);
        return;
      case "tuple":
      case "list":
        for (const item of e.items) expr(item);
        return;
      case "record":
        for (const field of e.fields) expr(field.value);
        return;
      case "recordUpdate":
        expr(e.base);
        for (const field of e.fields) expr(field.value);
        return;
      case "listComp":
        expr(e.body);
        return;
      case "do":
        for (const statement of e.statements) {
          if (statement.tag === "expr") expr(statement.expr);
          else if (statement.tag === "bind") expr(statement.source);
          else for (const b of statement.bindings) local(b);
        }
        return;
      default:
        return;
    }
  };
  const alternative = (alt: CaseAlternative): void => {
    if (alt.guard) expr(alt.guard);
    expr(alt.body);
  };
  const local = (b: LocalBinding): void => {
    for (const guard of b.guards ?? [{ body: b.value }]) {
      if (guard.condition) expr(guard.condition);
      expr(guard.body);
    }
    for (const w of b.whereBindings ?? []) local(w);
  };
  for (const equation of decl.equations) {
    for (const guard of equation.guards) {
      if (guard.condition) expr(guard.condition);
      expr(guard.body);
    }
    for (const w of equation.whereBindings) local(w);
  }
  return names;
}

// ------------------------------------------------------------- emission ----

function classDeclarations(info: ClassInfo): Declaration[] {
  const fields = [...info.superclasses.map((_, i) => `sup${i}`), ...info.methods.map((m, i) => `mth${i}`)];
  const data: DataDeclaration = {
    tag: "data",
    name: dictType(info.name),
    parameters: [],
    constructors: [{ name: dictCon(info.name), arity: fields.length }],
    deriving: [],
    span: info.span,
  };
  const selector = (name: string, at: number): ValueDeclaration => {
    const dictionary = variable("$dict", info.span);
    return valueDecl(
      name,
      [{ tag: "var", name: "$dict", span: info.span }],
      {
        tag: "case",
        subject: dictionary,
        alternatives: [
          {
            pattern: {
              tag: "con",
              name: dictCon(info.name),
              args: fields.map((field, i): Pattern =>
                i === at ? { tag: "var", name: field, span: info.span } : { tag: "wild", span: info.span },
              ),
              span: info.span,
            },
            body: variable(fields[at]!, info.span),
          },
        ],
        span: info.span,
      },
      info.span,
    );
  };
  return [
    data,
    ...info.superclasses.map((_, i) => selector(superSelector(info.name, i), i)),
    ...info.methods.map((method, i) => selector(method.name, info.superclasses.length + i)),
  ];
}

function instanceDeclaration(elaborator: Elaborator, instance: InstanceInfo): ValueDeclaration | undefined {
  const info = elaborator.classes.get(instance.cls);
  if (!info) return undefined;
  const args = instance.params.map((p) => variable(p.name, instance.span));
  // With a context the dictionary is a function, so "itself" - what a default
  // method is handed - is this binding applied to its own parameters.
  const self = applyAll(variable(dictValue(instance.cls, instance.emitCon), instance.span), args);
  const at = new Map<TVar, Type>(info.variables.map((v, i) => [v, instance.targets[i] ?? varType(v)]));
  const supers = info.superclasses.map(
    (parent) =>
      elaborator.resolve(parent.cls, parent.types.map((t) => applySubst(t, at)), instance.params, instance.span) ??
      errorExpr(instance.span),
  );
  const methods = info.methods.map((method) =>
    instance.methods.has(method.name)
      ? applyAll(variable(methodImpl(instance.cls, instance.emitCon, method.name), instance.span), args)
      : // The default is a function of this very dictionary, which is why the
        // instance binding is a genuinely self-referential CAF. It terminates
        // because the field is a thunk, never a forced value.
        apply(variable(defaultImpl(instance.cls, method.name), instance.span), self),
  );
  return valueDecl(
    dictValue(instance.cls, instance.emitCon),
    instance.params.map((p): Pattern => ({ tag: "var", name: p.name, span: instance.span })),
    applyAll(variable(dictCon(instance.cls), instance.span), [...supers, ...methods]),
    instance.span,
  );
}

function rewriteBinding(elaborator: Elaborator, binding: Binding): ValueDeclaration {
  const dicts = new Map<Expr, Expr[]>();
  const renames = new Map<Expr, string>();
  for (const use of binding.uses) {
    dicts.set(use.node, elaborator.dictionariesFor(use, binding));
    if (use.kind === "apply") renames.set(use.node, use.emit);
  }
  const rewriteExpr = (e: Expr): Expr => {
    const args = dicts.get(e);
    switch (e.tag) {
      case "var": {
        const name = renames.get(e) ?? e.name;
        return args && args.length ? applyAll(variable(name, e.span), args) : variable(name, e.span);
      }
      case "int": {
        // A raw literal survives only under `fromInteger`; at `IntPrim` there
        // is no dictionary, and the literal stands for the machine integer.
        if (!args) return e;
        return args.length ? applyAll(variable("fromInteger", e.span), [...args, e]) : e;
      }
      case "double": {
        if (!args) return e;
        return args.length ? applyAll(variable("fromRational", e.span), [...args, e]) : e;
      }
      case "app":
        return { ...e, fn: rewriteExpr(e.fn), arg: rewriteExpr(e.arg) };
      case "lambda":
        return { ...e, body: rewriteExpr(e.body) };
      case "lambdaCase":
        return { ...e, alternatives: e.alternatives.map(rewriteAlt) };
      case "if":
        return { ...e, condition: rewriteExpr(e.condition), thenBranch: rewriteExpr(e.thenBranch), elseBranch: rewriteExpr(e.elseBranch) };
      case "case":
        return { ...e, subject: rewriteExpr(e.subject), alternatives: e.alternatives.map(rewriteAlt) };
      case "let":
        return { ...e, bindings: e.bindings.map(rewriteLocal), body: rewriteExpr(e.body) };
      case "tuple":
      case "list":
        return { ...e, items: e.items.map(rewriteExpr) };
      default:
        return e;
    }
  };
  const rewriteAlt = (alt: CaseAlternative): CaseAlternative => ({
    ...alt,
    pattern: rewritePattern(elaborator, alt.pattern),
    guard: alt.guard ? rewriteExpr(alt.guard) : undefined,
    body: rewriteExpr(alt.body),
  });
  const rewriteGuard = (guard: Guard): Guard => ({
    ...guard,
    condition: guard.condition ? rewriteExpr(guard.condition) : undefined,
    body: rewriteExpr(guard.body),
  });
  const rewriteLocal = (b: LocalBinding): LocalBinding => ({
    ...b,
    patterns: b.patterns.map((p) => rewritePattern(elaborator, p)),
    value: rewriteExpr(b.value),
    guards: b.guards?.map(rewriteGuard),
    whereBindings: b.whereBindings?.map(rewriteLocal),
  });

  const parameters: Pattern[] = binding.givens.map((g) => ({ tag: "var", name: g.name, span: binding.decl.span }));
  return {
    ...binding.decl,
    name: binding.name,
    equations: binding.decl.equations.map((equation) => ({
      patterns: [...parameters, ...equation.patterns.map((p) => rewritePattern(elaborator, p))],
      guards: equation.guards.map(rewriteGuard),
      whereBindings: equation.whereBindings.map(rewriteLocal),
    })),
  };
}

function rewritePattern(elaborator: Elaborator, p: Pattern): Pattern {
  switch (p.tag) {
    case "int":
      return elaborator.boxedInt.has(p) ? { tag: "con", name: "I", args: [p], span: p.span } : p;
    // A `Char` is `C CharPrim`, so matching one is matching that constructor
    // and then the machine code point - the same two steps `I 0` takes for an
    // `Int` literal pattern. The inner `char` pattern is the raw one.
    case "char":
      return { tag: "con", name: "C", args: [p], span: p.span };
    case "as":
      return { ...p, pattern: rewritePattern(elaborator, p.pattern) };
    case "con":
      // `src/desugar.ts` represents `()` as the machine integer 0, so matching
      // it is matching that literal - strict, as GHC's `()` pattern is, and on
      // the representation the value side already produces.
      return p.name === "()" && p.args.length === 0
        ? { tag: "int", value: 0, span: p.span }
        : { ...p, args: p.args.map((arg) => rewritePattern(elaborator, arg)) };
    default:
      return p;
  }
}
