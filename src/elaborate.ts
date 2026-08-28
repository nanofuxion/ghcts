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
  GuardQualifier,
  InstanceDeclaration,
  LocalBinding,
  Module,
  Pattern,
  SignatureDeclaration,
  Span,
  ValueDeclaration,
} from "./ast.js";
import { instanceHead, instanceMethodValues } from "./dictionary.js";
import { classMethodNames, renameDeclarations, renameValue, resolveProgram, type Scopes } from "./modules.js";
import { error } from "./diagnostics.js";
import { constructorTable, derivedEqMethod, derivedGenericSource, derivedStockSource, expandSugar, fieldSelectors } from "./sugar.js";
import { PRELUDE_SOURCE } from "./prelude.js";
import { libraryModuleNames, withLibraryModules } from "./library.js";
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
const tDouble = tcon("Double");
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

/** `given` supplies the images of the *leading* quantified variables, in the
 * order `quantify` fixed - which for a class method is the class variable
 * first.  That is exactly what a visible type application writes, so `@T`
 * lands on `gen 0`, `@T @U` on `gen 0` and `gen 1`, and the rest stay fresh. */
function instantiate(scheme: Scheme, given: readonly Type[] = []): { type: Type; constraints: Constraint[] } {
  const images = Array.from({ length: scheme.gens }, (_, i) => given[i] ?? freshVar());
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

// A type *operator* is a constructor like any other - `f :*: g` is `(:*:) f g`
// - and `GHC.Generics` names two of the four things a `Rep` is built from that
// way, so an instance head that drops the operator has no head constructor at
// all. `::` is matched only so a kind signature can be recognised and skipped;
// it is not a type constructor.
// A lone `.` is matched only so that `forall a b . t` can be recognised and
// dropped; the identifier rule already swallows the commoner `forall a b. t`
// spelling into the token `b.`.
// A `"..."` alternative comes first so a type-level string literal survives as
// one token. Without it `Path "users"` tokenised as `Path` `users`, and the
// lower-case `users` became a fresh type *variable*, so every `Path` literal
// was the same type and `symbolVal` had nothing to read.
const TYPE_TOKEN = /"(?:[^"\\]|\\.)*"|->|=>|::|:[!#$%&*+./<=>?@\\^|~:-]+|[A-Za-z_][A-Za-z0-9_'.]*|[[\](),]|\./g;

/** A type constructor written infix. `::` is a kind ascription, not one. */
const isTypeOperator = (token: string | undefined): boolean => token !== undefined && token !== "::" && /^:/.test(token);

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

/** Constraints met while expanding a type synonym whose right-hand side has a
 * context of its own - miso's `type Lens' s a = forall f. Functor f => ...`.
 * They belong to whatever signature mentioned the synonym, so the expansion
 * parks them here and `parseSignature` picks them up. Parsing the right-hand
 * side as one type instead stopped at the `=>` and yielded the *constraint*
 * as the type, so `toVL :: ... -> Lens' r f` had result type `Functor f`. */
let expandedContext: Constraint[] = [];

class TypeParser {
  private index = 0;
  constructor(
    private readonly tokens: readonly string[],
    private readonly vars: Map<string, Type>,
    /** Guards against `type T = T`; a chain longer than this is a cycle. */
    private readonly depth = 0,
  ) {}

  /** Every variable a type mentions is quantified here anyway, so an explicit
   * `forall a b.` says nothing this inference does not already assume - but
   * left in place it is read as a *class*, and `forall f a. C f => t` then
   * contributes the constraint `forall f a C f` instead of `C f`, silently
   * dropping the given the body relies on. Drop the quantifier wherever it
   * appears, which also covers the rank-2 `(forall a. a -> a) -> t`. */
  static tokens(source: string): string[] {
    const raw: string[] = source.match(TYPE_TOKEN) ?? [];
    if (!raw.includes("forall")) return raw;
    const kept: string[] = [];
    for (let i = 0; i < raw.length; i++) {
      if (raw[i] !== "forall") {
        kept.push(raw[i]!);
        continue;
      }
      // Skip the bound variables and the `.` that ends them, whether the dot
      // stands alone or is glued to the last variable (`b.`).
      while (++i < raw.length && !raw[i]!.endsWith(".")) continue;
    }
    return kept;
  }

  /** A constraint's arguments: `MonadState s m` is two types, not the
   * application `s m`, so a class's arguments are parsed atom by atom. */
  argList(): Type[] {
    const args: Type[] = [];
    while (this.more()) args.push(this.atom());
    return args;
  }

  /** Is another *atom* of an application still to come? A type operator ends
   * one and starts the next, so it stops an application just as `->` does. */
  private more(): boolean {
    const token = this.tokens[this.index];
    return token !== undefined && !["->", ")", "]", ",", "=>", "::"].includes(token) && !isTypeOperator(token);
  }

  fun(): Type {
    const left = this.operators();
    if (this.tokens[this.index] === "->") {
      this.index++;
      return tfun(left, this.fun());
    }
    return left;
  }

  /** `f :*: g` is `(:*:) f g`. Right-associative, as `GHC.Generics` declares
   * both of its operators; a type operator binds tighter than `->`. */
  private operators(): Type {
    const left = this.application();
    const token = this.tokens[this.index];
    if (!isTypeOperator(token)) return left;
    this.index++;
    return tapp(tapp(tcon(token!), left), this.operators());
  }

  /** Are at least `n` argument atoms available after the head token? Counted
   * by parsing them and rewinding, since a bracketed argument spans an
   * unknown number of tokens. Parsing is idempotent here: an atom's only
   * lasting effect is a type variable registered in `vars`, and re-parsing the
   * same token returns that same variable. */
  private countsAtLeast(n: number): boolean {
    if (n === 0) return true;
    const saved = this.index;
    this.index++;
    let seen = 0;
    while (seen < n && this.more()) {
      this.atom();
      seen++;
    }
    this.index = saved;
    return seen >= n;
  }

  private application(): Type {
    const head = this.tokens[this.index];
    const synonym = head === undefined ? undefined : synonyms.get(unqualify(head));
    // A synonym has to be *saturated* to be expanded, as in GHC. Types share
    // one global namespace here (see `src/modules.ts`), so miso's
    // `type Parser token a` and its unrelated `newtype Parser a` are one name:
    // reading arity is what keeps `Parser (f a)` the newtype and
    // `Parser token a` the alias, and what stops a genuinely under-applied
    // synonym from quietly padding itself out with a fresh variable.
    if (synonym && this.depth < 16 && this.countsAtLeast(synonym.parameters.length)) {
      this.index++;
      const bound = new Map<string, Type>();
      for (const parameter of synonym.parameters) bound.set(parameter, this.atom());
      let value = expandTarget(synonym.target, bound, this.depth + 1);
      // A partially applied synonym is still an application: `type Handler a =
      // a -> ()` used as `Handler Int Extra` keeps consuming arguments.
      while (this.more()) value = tapp(value, this.atom());
      return value;
    }
    let value = this.atom();
    while (this.more()) value = tapp(value, this.atom());
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
      // `(,)` is the pair *constructor*, the way `[]` is the list one, and
      // `instance Bifunctor (,)` is how base writes it. Falling through to the
      // element parser read the comma as a type named `,`, so the instance head
      // and the `(a, c)` in its own method body were different types.
      if (this.tokens[this.index] === ",") {
        let commas = 0;
        while (this.tokens[this.index] === ",") (commas++, this.index++);
        if (this.tokens[this.index] === ")") this.index++;
        return tcon(`(${",".repeat(commas)})`);
      }
      const items = [this.fun()];
      while (this.tokens[this.index] === ",") {
        this.index++;
        items.push(this.fun());
      }
      // `(f :: Type -> Type)` is `f` with its kind written out. There are no
      // kinds here, so the ascription is skipped rather than mistaken for an
      // application - it is the *type* that names the instance.
      if (this.tokens[this.index] === "::") {
        let depth = 1;
        while (this.index < this.tokens.length && depth > 0) {
          const token_ = this.tokens[this.index];
          if (token_ === "(" || token_ === "[") depth++;
          if (token_ === ")" || token_ === "]") depth--;
          if (depth > 0) this.index++;
        }
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
      return expandTarget(synonym.target, new Map(), this.depth + 1);
    }
    return tcon(token);
  }
}

/** A signature string, split into its context and its type. */
/** `M.Map` -> `Map`, `Data.Text.Text` -> `Text`. */
const unqualify = (name: string): string =>
  /^[A-Z][A-Za-z0-9_']*(\.[A-Z][A-Za-z0-9_']*)+$/.test(name) ? name.slice(name.lastIndexOf(".") + 1) : name;

/** A synonym's right-hand side, with any context it carries lifted out to the
 * signature being parsed. */
function expandTarget(target: string, bound: Map<string, Type>, depth: number): Type {
  const parts = splitTop(TypeParser.tokens(target), "=>");
  for (const part of parts.slice(0, -1)) {
    const stripped = part[0] === "(" && part.at(-1) === ")" ? part.slice(1, -1) : part;
    for (const item of splitTop(stripped, ",")) {
      if (item.length < 2) continue;
      expandedContext.push({ cls: unqualify(item[0]!), types: new TypeParser(item.slice(1), bound, depth).argList() });
    }
  }
  return new TypeParser(parts.at(-1)!, bound, depth).fun();
}

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
  // A synonym expanded anywhere in the body contributes its own context; the
  // save/restore keeps a nested `parseSignature` from stealing it.
  const outer = expandedContext;
  expandedContext = [];
  const type = new TypeParser(body, vars).fun();
  context.push(...expandedContext);
  expandedContext = outer;
  return resolveGenericRep(context, type);
}

/** `Rep a`, GHC's associated type family, read as the class parameter its
 * functional dependency determines.
 *
 * `class Generic a where type Rep a` cannot be written here - there are no
 * type families - but `class Generic a rep | a -> rep` says the same thing
 * about the same two types, and the improvement pass already solves `rep` from
 * `a`. So a written
 *
 *   (Generic a, GToJSON (Rep a)) => a -> Value
 *
 * becomes `(Generic a r, GToJSON r) => a -> Value`, with one `r` per distinct
 * argument of `Rep` across the whole signature - which is what makes the two
 * constraints talk about the same representation.
 *
 * The limit of the reading is that `Rep a` is *solved for* and never
 * *computed*: it is only meaningful where a constraint can be added to carry
 * it, so a `Rep a` outside a signature has nowhere to put its `Generic`. */
function resolveGenericRep(context: Constraint[], type: Type): { context: Constraint[]; type: Type } {
  const key = (t: Type): string => {
    const p = prune(t);
    if (p.tag === "var") return `v${p.v}`;
    if (p.tag === "app") return `(${key(p.fn)} ${key(p.arg)})`;
    return p.tag === "con" ? `c${p.name}` : `g${p.index}`;
  };
  const reps = new Map<string, { arg: Type; rep: Type }>();
  const repOf = (arg: Type): Type => {
    const k = key(arg);
    const seen = reps.get(k);
    if (seen) return seen.rep;
    const rep = freshVar();
    reps.set(k, { arg, rep });
    return rep;
  };
  const rewrite = (t: Type): Type => {
    const p = prune(t);
    if (p.tag !== "app") return p;
    const fn = prune(p.fn);
    if (fn.tag === "con" && fn.name === "Rep") return repOf(rewrite(p.arg));
    return tapp(rewrite(p.fn), rewrite(p.arg));
  };
  const rewritten = context.map((c) => ({ cls: c.cls, types: c.types.map(rewrite) }));
  const body = rewrite(type);
  if (reps.size === 0) return { context: rewritten, type: body };
  // A written `Generic a` names one argument; the second is the `rep` that the
  // `Rep a`s in the same signature asked for.
  const out = rewritten.map((c) =>
    c.cls === "Generic" && c.types.length === 1 && reps.has(key(c.types[0]!))
      ? { cls: c.cls, types: [c.types[0]!, repOf(c.types[0]!)] }
      : c,
  );
  // A signature may mention `Rep a` and never say `Generic a`; the constraint
  // is implied, and appending it keeps the order every call site agrees on.
  for (const { arg, rep } of reps.values()) {
    if (out.some((c) => c.cls === "Generic" && c.types.length === 2 && key(c.types[0]!) === key(arg))) continue;
    out.push({ cls: "Generic", types: [arg, rep] });
  }
  return { context: out, type: body };
}

const parseType = (source: string, vars: Map<string, Type>): Type => parseSignature(source, vars).type;

// ------------------------------------------------------------ class info ---

interface ClassMethod {
  name: string;
  /** The name the declaring module wrote, for matching an instance's binder. */
  surfaceName: string;
  /** The declared signature, with the class variable still free. */
  type: Type;
  /** The method's *own* context, over and above the class's:
   * `traverse :: Applicative f => (a -> f b) -> t a -> f (t b)` constrains an
   * `f` the class knows nothing about. It is not part of the dictionary - the
   * field holds a function that takes it - so it appears after the class
   * constraint in the method's scheme, and after the instance context in the
   * signature synthesised for each instance's implementation. Dropping it (as
   * this did) left an instance body wanting `Applicative` at a rigid variable
   * with no given to discharge it, which is why `Traversable` could not be a
   * class here. */
  ownContext: Constraint[];
  /** `$dm<name>`, when the class body supplies a default. */
  hasDefault: boolean;
  /** GHC's DefaultSignatures `default f :: ty`: the *extra* constraints the
   * default implementation may assume, over the class's own. They become
   * dictionary parameters of `$dm<name>`, supplied at each instance. */
  defaultContext?: Constraint[];
  /** The default implementation's own type, when it differs. */
  defaultType?: Type;
}

interface ClassInfo {
  name: string;
  /** The parameter names as written, positionally matching `variables`: what a
   * default method's body may name in an expression ascription. */
  parameters: string[];
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
  /** The head's type variables by their written names. With
   * ScopedTypeVariables - which miso uses - these scope over the method
   * bodies, so `selName (M1 undefined :: S1 m f ())` inside
   * `instance Selector m => GToFields (S1 m f)` means *this* instance's `m`. */
  vars: ReadonlyMap<string, Type>;
  methods: Map<string, ValueDeclaration>;
  span: Span;
}

/** A type constructor's name as it may appear inside a generated identifier;
 * `[]` and friends are legal type constructors but not legal name fragments. */
const conKey = (con: string): string =>
  con === "[]"
    ? "List"
    : con === "->"
      ? "Fun"
      : /^\(,+\)$/.test(con)
        ? `Tuple${con.length - 1}`
        : /^[A-Za-z_]/.test(con)
          ? con
          : `Op${[...con].map((c) => c.charCodeAt(0).toString(16)).join("")}`;

/** The name an instance's dictionary is emitted under.
 *
 * This is every type constructor the head mentions, not only the outermost
 * one. `GToFields (S1 m f)` and `GToFields (S1 m (Rec0 (Maybe a)))` have the
 * same head constructor and are two different instances; naming both `$fGToFieldsM1`
 * would silently emit one dictionary and use it for both. Variables contribute
 * nothing, so `Eq [a]` is still `$fEqList` whatever `a` turns out to be. */
function instanceKey(targets: readonly Type[]): string {
  const parts: string[] = [];
  const walk = (t: Type): void => {
    const p = prune(t);
    if (p.tag === "con") parts.push(conKey(p.name));
    else if (p.tag === "app") {
      walk(p.fn);
      walk(p.arg);
    }
  };
  for (const t of targets) {
    const before = parts.length;
    walk(t);
    if (parts.length === before) parts.push("v");
  }
  return parts.join("");
}

/** GHC's overlap rule, and the only part of it this needs: when more than one
 * instance matches a wanted, the one every other match is a *substitution
 * instance of* wins.
 *
 * `GToFields (S1 m f)` and `GToFields (S1 m (Rec0 (Maybe a)))` both match a
 * `Maybe` field; the second is the answer because the first matches it but not
 * the other way round. Declaration order decides nothing - miso writes the two
 * pairs it has in opposite orders - so it is not used. Two matches neither of
 * which is more specific are genuinely ambiguous, and taking the first would be
 * a coin toss, so `undefined` lets the caller report no instance.
 *
 * The comparison is on heads only. GHC's is too: an instance's context is not
 * consulted when choosing between overlapping instances. */
function mostSpecific(
  matches: ReadonlyArray<{ instance: InstanceInfo; subst: Map<TVar, Type> }>,
): { instance: InstanceInfo; subst: Map<TVar, Type> } | undefined {
  if (matches.length <= 1) return matches[0];
  const generalises = (a: InstanceInfo, b: InstanceInfo): boolean => {
    // One substitution across all of a multi-parameter head's arguments: `C a a`
    // does not generalise `C Int Bool`.
    const subst = new Map<TVar, Type>();
    return a.targets.length === b.targets.length && a.targets.every((t, i) => matchType(t, b.targets[i]!, subst));
  };
  // Drop every match that another match is *strictly* more specific than. What
  // survives is the maximal one; several survive only when they are equally
  // specific - which here means the same head twice, because `Data.Text.Text`
  // and `MisoString` are one type - and then the first is as good as the last.
  const survivors = matches.filter(
    (m) =>
      !matches.some(
        (other) => other !== m && generalises(m.instance, other.instance) && !generalises(other.instance, m.instance),
      ),
  );
  return survivors[0];
}

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
type Use = { locals?: readonly Given[] } & (
  | { kind: "apply"; node: Expr; emit: string; constraints: Constraint[] }
  | { kind: "literal"; node: Expr; type: Type; cls: "Num" | "Fractional" | "IsString" }
  | { kind: "group"; node: Expr; target: string }
);

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
  /** Type variables an expression ascription in this body may name, already
   * skolemised. Empty for an ordinary top-level binding: without an explicit
   * `forall` a signature's variables do not scope over its body in GHC either. */
  tyvars: ReadonlyMap<string, Type>;
  givens: Given[];
  /** Every dictionary a constructor pattern in this body brought into scope,
   * flattened.  Scoping is per `Use` (see `Use.locals`); this list exists only
   * so defaulting knows those types are already spoken for. */
  patternGivens: Given[];
  uses: Use[];
  /** Every numeric literal pattern, with the type it was matched at.  The
   * representation is settled only once the binding is fully inferred. */
  intPatterns: Array<{ pattern: Extract<Pattern, { tag: "int" | "double" }>; type: Type }>;
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
  /** Numeric literal patterns whose type turned out to be `Double`/`Float`,
   * with the box the match goes through. */
  readonly doubleLit = new Map<Extract<Pattern, { tag: "int" | "double" }>, "Double" | "Float">();
  /** Every binder this pass gave a type to, so `isVoidRep` can ask afterwards
   * whether that type turned out to be the state token. Inference is the only
   * place a type exists, and the answer is only final once unification has
   * finished, so the *type* is recorded here and pruned at rewrite time. */
  private readonly binderTypes = new Map<Pattern | Expr, Type>();
  /** How many dictionary fields a constructor carries ahead of its declared
   * ones.  Read back when the data declarations are handed to `desugar`, which
   * is what keeps the constructor's arity and this pass's view of it in step. */
  readonly conDictFields = new Map<string, number>();
  /** The binder names a constructor *pattern* gives those fields, so
   * `rewritePattern` can put them back as the pattern's leading arguments. */
  readonly conPatternDicts = new Map<Pattern, string[]>();
  /** Dictionaries in scope from the constructor patterns enclosing whatever is
   * being inferred right now.  A stack, because a given from one alternative's
   * pattern must not discharge a constraint in a sibling's body. */
  private patternGivens: Given[] = [];
  private nextPatternDict = 0;
  private current?: Binding;

  /** Run `f` with whatever constructor patterns it matches in scope, and drop
   * them again afterwards. */
  private scoped<T>(f: () => T): T {
    const depth = this.patternGivens.length;
    try {
      return f();
    } finally {
      this.patternGivens.length = depth;
    }
  }

  private addUse(use: Use): void {
    if (!this.current) return;
    this.current.uses.push(this.patternGivens.length ? { ...use, locals: [...this.patternGivens] } : use);
  }

  /** Is this binder's type the erased state token? See `Pattern.voidRep`. */
  isVoidRep(node: Pattern | Expr): boolean {
    const t = this.binderTypes.get(node);
    return t !== undefined && headCon(t) === "RealWorld";
  }

  private recordBinder<T extends Pattern | Expr>(node: T, type: Type): Type {
    this.binderTypes.set(node, type);
    return type;
  }

  constructor(private readonly file: string) {}

  report(message: string, span: Span): void {
    // The whole program is one flat declaration pile by the time this pass runs,
    // so a span alone cannot say which module a failure came from. The binding
    // under check can - its name is `Module_name` after `renameDeclarations` -
    // and that is what makes a hundred reports groupable by cause.
    const where = this.current ? ` (in \`${this.current.name}\`)` : "";
    this.diagnostics.push(error("GHCTS-DICT", message + where, this.file, span.line, span.column));
  }

  // ------------------------------------------------------------ patterns --

  inferPattern(p: Pattern, env: Env): Type {
    switch (p.tag) {
      case "wild":
        return this.recordBinder(p, freshVar());
      case "var": {
        const t = this.recordBinder(p, freshVar());
        env.set(p.name, { tag: "mono", type: t });
        return t;
      }
      case "as": {
        const t = this.inferPattern(p.pattern, env);
        env.set(p.name, { tag: "mono", type: t });
        return t;
      }
      case "double":
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
        const instance = instantiate(scheme);
        let type = instance.type;
        // The mirror image of building one: the dictionary fields are matched
        // out and become *givens* for whatever this pattern scopes over, which
        // is the only reason a body can call a class method at the existential
        // type the pattern just unpacked.
        if (instance.constraints.length) {
          const names = instance.constraints.map(() => `$dx${this.nextPatternDict++}`);
          this.conPatternDicts.set(p, names);
          const bound = instance.constraints.map((c, i) => ({ cls: c.cls, types: c.types, name: names[i]! }));
          this.patternGivens.push(...bound);
          this.current?.patternGivens.push(...bound);
        }
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
        this.addUse({ kind: "literal", node: e, type: t, cls: "Num" });
        return t;
      }
      // A fractional literal wants `Fractional`, not `Num`: `0.5 :: Int` is a
      // type error in Haskell and must stay one here.
      case "double": {
        const t = freshVar();
        this.addUse({ kind: "literal", node: e, type: t, cls: "Fractional" });
        return t;
      }
      // OverloadedStrings. `[Char]` is not a *default* GHC could write down -
      // base spells it `instance a ~ Char => IsString [a]`, and there are no
      // equality constraints here - so it is one instead: an `IsString` wanted
      // that inference never pins defaults to `[Char]`, exactly as an
      // unresolved `Num` defaults to `Int`, and at `[Char]` the literal *is*
      // its own value and needs no dictionary.
      case "string": {
        const t = freshVar();
        this.addUse({ kind: "literal", node: e, type: t, cls: "IsString" });
        return t;
      }
      case "char":
        return tcon("Char");
      case "unit":
        return tcon("()");
      case "var":
        return this.inferVar(e, env);
      // `e :: ty`. The written type is unified with the inferred one, which is
      // the whole point of the form in generic code: `conName (undefined ::
      // C1 m f ())` never forces its argument and exists only so that the
      // ascription picks the `Constructor m` dictionary.
      //
      // Variables the enclosing instance or class does not bind are fresh, and
      // fresh per ascription - that is what instantiating the signature's
      // implicit `forall` amounts to here. A context on the ascription is not
      // turned into a local given; a constraint that only it could discharge
      // therefore fails loudly at the use site rather than being assumed.
      // `f @T`.  For a term whose type is `forall a. C a => t` this binds
      // `a := T` in *this* instantiation, which is the only thing that can
      // make the `C a` wanted resolvable when `a` appears nowhere in the
      // arguments or the result - `gAllNullary :: forall f. GAllNullary f =>
      // Bool` in miso's `Miso.JSON` is exactly that shape.
      case "typeApp": {
        const written: string[] = [];
        let head: Expr = e;
        // The parser nests later arguments outermost, so peeling recovers the
        // written left-to-right order the `forall` quantifies in.
        while (head.tag === "typeApp") {
          written.unshift(head.type);
          head = head.expr;
        }
        // One variable map for the whole chain, so `@f @f` names one variable,
        // and seeded with the enclosing instance's skolems so `@f` inside
        // `instance (C f, C g) => C (f :+: g)` is *that* `f`.
        const vars = new Map(this.current?.tyvars ?? []);
        const types = written.map((t) => parseType(t, vars));
        // Anything but a plain name - a constructor is instantiated here too,
        // since `this.constructors` schemes quantify in declaration order -
        // keeps the pre-existing behaviour of erasing the argument rather than
        // failing: this elaborator has no higher-rank types to apply one to.
        if (head.tag !== "var") return this.infer(head, env);
        return this.inferVar(head, env, types);
      }
      case "annot": {
        const written = parseSignature(e.type, new Map(this.current?.tyvars ?? []));
        const t = this.infer(e.expr, env);
        if (!unify(t, written.type))
          this.report(`expression does not have the ascribed type \`${showType(written.type)}\``, e.span);
        return t;
      }
      case "app": {
        const fnType = this.infer(e.fn, env);
        const argType = this.infer(e.arg, env);
        const result = freshVar();
        if (!unify(fnType, tfun(argType, result))) this.report(`type mismatch in application: \`${showType(fnType)}\` applied to \`${showType(argType)}\``, e.span);
        return result;
      }
      case "lambda": {
        const inner = new Map(env);
        const param = this.recordBinder(e, freshVar());
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

  private inferVar(e: Extract<Expr, { tag: "var" }>, env: Env, typeArgs: readonly Type[] = []): Type {
    const entry = env.get(e.name);
    if (entry) {
      if (entry.tag === "mono") return entry.type;
      if (entry.tag === "group") {
        this.addUse({ kind: "group", node: e, target: entry.name });
        return entry.type;
      }
      const { type, constraints } = instantiate(entry.scheme, typeArgs);
      if (constraints.length || entry.emit !== e.name) {
        this.addUse({ kind: "apply", node: e, emit: entry.emit, constraints });
      }
      return type;
    }
    const con = this.constructors.get(e.name);
    if (con) {
      // Building a constructor that has a context *stores* the dictionaries the
      // construction site solved, so the occurrence takes them as its leading
      // arguments exactly as an overloaded function's would.
      const { type, constraints } = instantiate(con, typeArgs);
      if (constraints.length) this.addUse({ kind: "apply", node: e, emit: e.name, constraints });
      return type;
    }
    this.report(`\`${e.name}\` is not in scope`, e.span);
    return freshVar();
  }

  private inferAlternatives(alts: CaseAlternative[], scrutinee: Type, result: Type, env: Env, span: Span): void {
    for (const alt of alts)
      this.scoped(() => {
        const inner = new Map(env);
        if (!unify(scrutinee, this.inferPattern(alt.pattern, inner))) this.report("pattern does not match the scrutinee type", span);
        this.inferQualifiers(alt.qualifiers, inner, span);
        const body = this.infer(alt.body, inner);
        if (!unify(result, body)) this.report(`case alternatives have different types: \`${showType(result)}\` vs \`${showType(body)}\``, span);
      });
  }

  /** A `let`/`where` group, in dependency order, generalising as it goes.
   *
   * Let-polymorphism, but only over the variables no dictionary depends on: a
   * local binding's constraints float out to the enclosing top-level binding,
   * which is where dictionaries are actually bound, so a variable a constraint
   * still mentions has to stay monomorphic or that constraint would be left
   * with nothing to solve it at. Everything else generalises, and because the
   * scheme carries no constraints the use site instantiates it and emits
   * exactly the variable it already wrote - there is nothing for `desugar` to
   * do differently.
   *
   * Without this, miso's `Miso.JSON.Lexer` could not typecheck: its
   * `escaped = (char '\\' *>)` is used at `Lexer Char` and at `Lexer Int`, and
   * one monomorphic type cannot be both. */
  private inferLocals(bindings: readonly LocalBinding[], env: Env): Env {
    if (bindings.length === 0) return env;
    const inner = new Map(env);
    // Only these entries can hold a free type variable: a `poly` scheme has
    // had its own quantified over. A variable one of them mentions belongs to
    // something still being inferred, so it is not this group's to generalise.
    const monomorphic = new Set<TVar>();
    for (const entry of env.values())
      if (entry.tag === "mono" || entry.tag === "group") for (const v of typeVars(entry.type)) monomorphic.add(v);
    const types = new Map<LocalBinding, Type>();
    const groups = dependencyGroups(
      bindings.map((b) => b.name),
      bindings.map((b) => referencedNames(localAsDeclaration(b))),
    );
    for (const group of groups) {
      const members = group.map((i) => bindings[i]!);
      for (const b of members) {
        const t = freshVar();
        types.set(b, t);
        inner.set(b.name, { tag: "mono", type: t });
        // A local signature is *checked*, not skolemised: a rigid variable
        // would need the binding to abstract over dictionaries, which a
        // `let` here cannot do. Parsed in the enclosing signature's variable
        // scope, so `commit :: ComponentId -> Seq action -> ...` inside a
        // `forall action.` names that `action` and not a new one - which is
        // the whole reason miso's `Miso.Runtime` typechecks under GHC.
        // A signature with a context is ignored: honouring it would promise
        // dictionaries nothing binds.
        if (b.signature === undefined) continue;
        const written = parseSignature(b.signature, new Map(this.current?.tyvars ?? []));
        if (written.context.length) continue;
        if (!unify(t, written.type))
          this.report(`\`${b.name}\` does not have its declared type \`${showType(written.type)}\``, b.span);
      }
      for (const binding of members)
        this.scoped(() => {
          const scope = new Map(inner);
          let result = types.get(binding)!;
          for (const pattern of binding.patterns) {
            const argType = this.inferPattern(pattern, scope);
            const next = freshVar();
            if (!unify(result, tfun(argType, next))) this.report("binding parameters do not match its type", binding.span);
            result = next;
          }
          this.inferGuards(binding.guards ?? [{ body: binding.value }], binding.whereBindings ?? [], result, scope, binding.span);
        });
      const constrained = new Set<TVar>();
      for (const use of this.current?.uses ?? [])
        if (use.kind === "apply")
          for (const c of use.constraints) for (const t of c.types) for (const v of typeVars(t)) constrained.add(v);
      for (const b of members) {
        const type = types.get(b)!;
        const gens = typeVars(type).filter((v) => !monomorphic.has(v) && !constrained.has(v));
        if (gens.length) inner.set(b.name, { tag: "poly", scheme: quantify(gens, type, []), emit: b.name });
        // What stayed monomorphic is monomorphic for every later group too.
        for (const v of typeVars(type)) if (!gens.includes(v)) monomorphic.add(v);
      }
    }
    return inner;
  }

  /** `| p <- e, cond`: the qualifiers are checked left to right in one scope,
   * so a pattern's binders are available to everything after it. */
  private inferQualifiers(qualifiers: readonly GuardQualifier[] | undefined, scope: Env, span: Span): void {
    for (const q of qualifiers ?? []) {
      if (q.tag === "bool") {
        if (!unify(this.infer(q.condition, scope), tBool)) this.report("guard is not a Bool", span);
      } else if (!unify(this.infer(q.source, scope), this.inferPattern(q.pattern, scope)))
        this.report("pattern guard does not match the type of its source", span);
    }
  }

  private inferGuards(guards: readonly Guard[], where: readonly LocalBinding[], result: Type, env: Env, span: Span): void {
    const scope = this.inferLocals(where, env);
    for (const guard of guards) {
      // Each guard gets its own copy: a `p <- e` binds for the rest of *this*
      // guard's qualifiers and its body, and for nothing after it.
      this.scoped(() => {
        const inner = new Map(scope);
        this.inferQualifiers(guard.qualifiers, inner, span);
        // The two types are in the message on purpose. "different types" alone
        // says nothing a reader can act on, and every fix in this file's
        // vicinity - `(,)` read as a type named `,`, a synonym's context handed
        // back as its type, a `String` pattern pinning a `MisoString` scrutinee -
        // was found by reading the pair.
        const body = this.infer(guard.body, inner);
        if (!unify(result, body)) this.report(`guarded bodies have different types: \`${showType(result)}\` vs \`${showType(body)}\``, span);
      });
    }
  }

  inferBinding(binding: Binding, env: Env): void {
    this.current = binding;
    for (const equation of binding.decl.equations)
      this.scoped(() => {
        const scope = new Map(env);
        let result = binding.monoType;
        for (const pattern of equation.patterns) {
          const argType = this.inferPattern(pattern, scope);
          const next = freshVar();
          if (!unify(result, tfun(argType, next))) this.report(`\`${binding.name}\` has inconsistent equation arities`, binding.decl.span);
          result = next;
        }
        this.inferGuards(equation.guards, equation.whereBindings, result, scope, binding.decl.span);
      });
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
    // The `a ~ Char` half of base's `instance a ~ Char => IsString [a]`. Only
    // improvement can supply it: `"a" ++ "b"` leaves the literal's type as
    // `[t]`, which is neither ambiguous enough to default nor concrete enough
    // to match the `IsString [Char]` instance.
    if (wanted.cls === "IsString" && wanted.types.length === 1) {
      const t = prune(wanted.types[0]!);
      if (t.tag === "app" && headCon(t.fn) === "[]" && !sameType(t.arg, tChar)) return unify(t.arg, tChar);
    }
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

  /** Improvement for a caller outside inference: an instance declaration's
   * default-signature constraints need the same fundep pass a call site's do,
   * and there is no binding there to run one. */
  improveOne(wanted: Constraint, givens: readonly Constraint[], span: Span): void {
    for (let round = 0; round < 8; round++) if (!this.improveConstraint(wanted, givens, span, 0)) return;
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
    // `KnownSymbol "users"`. A type-level string literal is `tcon("\"users\"")`
    // - quotes included, so it can never collide with a written type - and its
    // dictionary is *the literal itself*: one field, `symbolVal`, ignoring its
    // proxy and returning the characters. Building it here rather than as a
    // generated instance is what makes the set of solvable symbols exactly the
    // set that appears in the program, with nothing to enumerate beforehand:
    // by the time a `KnownSymbol` is wanted, the type it is wanted at has
    // already been unified with the literal that a signature, a type
    // application or a `deriving Generic` metadata type wrote.
    if (cls === "KnownSymbol" && con !== undefined && con.startsWith('"'))
      return apply(
        variable(dictCon(cls), span),
        { tag: "lambda", parameter: "$sym", body: { tag: "string", value: JSON.parse(con) as string, span }, span },
      );
    // A constrained instance is a function from dictionaries to a dictionary,
    // so selecting it is recursive. The depth bound is what turns a
    // non-terminating instance chain into a diagnostic instead of a hang.
    if (depth > 32) {
      this.report(`instance resolution for \`${showConstraint(cls, types)}\` did not terminate`, span);
      return undefined;
    }
    const matches: Array<{ instance: InstanceInfo; subst: Map<TVar, Type> }> = [];
    for (const instance of this.byClass.get(cls) ?? []) {
      const subst = new Map<TVar, Type>();
      if (!types.every((t, i) => { const target = instance.targets[i]; return target !== undefined && matchType(target, t, subst); })) continue;
      matches.push({ instance, subst });
    }
    const chosen = mostSpecific(matches);
    if (chosen) {
      const { instance, subst } = chosen;
      const self = variable(dictValue(cls, instance.emitCon), span);
      if (instance.context.length === 0) return self;
      return applyAll(
        self,
        instance.context.map(
          (c) => this.resolve(c.cls, c.types.map((t) => applySubst(t, subst)), givens, span, depth + 1) ?? errorExpr(span),
        ),
      );
    }
    // Nothing matched. A constraint that names a type constructor genuinely
    // has no instance; one still entirely on unsolved variables is ambiguous -
    // there is no type to look an instance up at, and no later phase will
    // supply one. Both used to reach `desugar` as `$dictionaryNotFound`, and
    // only the first was reported, so the ambiguous ones were invisible to
    // every count of how far this is from compiling miso.
    this.report(
      types.some((t) => headCon(t) !== undefined)
        ? `no instance for \`${showConstraint(cls, types)}\``
        : `ambiguous type variable in \`${showConstraint(cls, types)}\``,
      span,
    );
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
      // Nor is a variable a constructor pattern unpacked: it is existential,
      // and a dictionary matched out of the value already stands for it.
      if ([...binding.givens, ...binding.patternGivens].some((g) => g.types.some((gt) => sameType(gt, t)))) continue;
      const classes = wanted.filter((other) => other.types.length === 1 && sameType(other.types[0]!, t)).map((other) => other.cls);
      // Haskell's `default (Integer, Double)`: a `Fractional` wanted rules
      // `Int` out, so the same ambiguous variable defaults to `Double`.
      if (classes.includes("Fractional")) unify(t, tcon("Double"));
      else if (classes.includes("Num")) unify(t, tInt);
      else if (classes.includes("IsString")) unify(t, tString);
    }
  }

  /** Fix each integer pattern's representation. Doing it here, once the
   * binding is fully inferred, is what lets `f 0 = ...` stay a structural
   * match on `I 0` while a pattern on an unboxed scrutinee stays raw. */
  private solveIntPatterns(binding: Binding): void {
    for (const { pattern, type } of binding.intPatterns) {
      const fractional = pattern.tag === "double";
      const t = prune(type);
      if (t.tag === "var") unify(t, fractional ? tDouble : tInt);
      const con = headCon(type);
      // `Double` and `Float` are one-field boxes over a JS number, so a
      // numeric literal pattern at either is the same shape as `Int`'s - the
      // box, then the raw literal. miso writes `\case 1 -> ...` on a JSON
      // number, which is a `Double`, seven times over.
      if (con === "Double" || con === "Float") {
        this.doubleLit.set(pattern, con);
        continue;
      }
      if (con === "DoublePrim" || con === "FloatPrim") continue;
      if (fractional) {
        this.report(`fractional pattern at type \`${con ?? "?"}\`: only Double and Float are supported`, pattern.span);
        continue;
      }
      if (con === "IntPrim") continue;
      if (con === "Int") {
        this.boxedInt.add(pattern);
        continue;
      }
      // `\case 1 -> ...` on a JSON number is an integer literal at `Double`,
      // which miso writes seven times. `Double` is a one-field box over a
      // `Double#`, so the match is the same shape as `Int`'s - only the
      // literal's own representation differs, and an integer literal at
      // `Double` is exactly the double of that whole number.
      if (con === "Double" || con === "Float") {
        this.doubleLit.set(pattern, con);
        continue;
      }
      this.report(`integer pattern at type \`${con ?? "?"}\`: literal patterns are only supported at Int, Double and Float`, pattern.span);
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
    // A dictionary unpacked by an enclosing constructor pattern comes first: it
    // is the more local given, and for an existential type it is the only one.
    const givens = use.locals ? [...use.locals, ...binding.givens] : binding.givens;
    if (use.kind === "group") {
      const target = this.bindings.get(use.target);
      return (target?.givens ?? []).map((g) => this.resolve(g.cls, g.types, givens, span) ?? errorExpr(span));
    }
    if (use.kind === "literal" && headCon(use.type) === "IntPrim") return [];
    if (use.kind === "literal" && headCon(use.type) === "DoublePrim") return [];
    // At `[Char]` a string literal is already the value it denotes, so there is
    // no `fromString` to apply and no dictionary to find.
    if (use.kind === "literal" && use.cls === "IsString" && sameType(use.type, tString)) return [];
    const constraints: Constraint[] =
      use.kind === "literal" ? [{ cls: use.cls, types: [use.type] }] : use.constraints;
    return constraints.map((c) => this.resolve(c.cls, c.types, givens, span) ?? errorExpr(span));
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

/** A type's top-level arrow spine. */
function splitFun(t: Type): { args: Type[]; result: Type } {
  const args: Type[] = [];
  let cursor = prune(t);
  for (;;) {
    if (cursor.tag !== "app") break;
    const fn = prune(cursor.fn);
    if (fn.tag !== "app") break;
    const head = prune(fn.fn);
    if (head.tag !== "con" || head.name !== "->") break;
    args.push(fn.arg);
    cursor = prune(cursor.arg);
  }
  return { args, result: cursor };
}

/** One method of a `deriving newtype` instance.
 *
 * A newtype is a real single-field data type here - nothing erases the
 * constructor - so GND's `coerce` does not exist to be used. What does exist is
 * the wrapper that GND's coercion stands for: the wrapped type's method with
 * the constructor taken off the arguments and put back on the result.
 *
 * A *coercible* position is one holding a value of this very newtype: the class
 * variable itself for a class over kind `*` (`Num`, `ToJSON`), or the class
 * variable applied to arguments that do not mention it for a class over
 * `* -> *` (`f a` in `fmap`, `f (a -> b)` in `<*>`). Either way the value is
 * `N x` and unwraps to the wrapped type. A function argument whose *result* is
 * coercible - `(a -> m b)` in `>>=` - is handled by unwrapping under a lambda.
 * `undefined` (and a diagnostic from the caller) is the answer anywhere else,
 * since moving a newtype through `[a]` or `g (f a)` needs a coercion this
 * compiler cannot perform.
 *
 * The divergence from GHC is strictness, and only that: unwrapping is a `case`,
 * so a method that would not have forced its own argument becomes strict in it.
 */
/** Is `v` ever *applied* in this type? That is what makes a class variable
 * higher-kinded, and there is no kind inference here to ask instead. */
function appliesVar(t: Type, v: TVar): boolean {
  const p = prune(t);
  if (p.tag !== "app") return false;
  const head = prune(p.fn);
  return (head.tag === "var" && head.v === v) || appliesVar(p.fn, v) || appliesVar(p.arg, v);
}

function newtypeMethod(
  method: ClassMethod,
  classVar: TVar,
  con: string,
  wrapped: string,
  span: Span,
): ValueDeclaration | undefined {
  const { args, result } = splitFun(method.type);
  const mentions = (t: Type): boolean => typeVars(t).includes(classVar);
  /** Does this type hold a value of the newtype being derived through? */
  const coercible = (t: Type): boolean => {
    let head = prune(t);
    while (head.tag === "app") {
      if (mentions(head.arg)) return false;
      head = prune(head.fn);
    }
    return head.tag === "var" && head.v === classVar;
  };
  const unwrapExpr = (subject: Expr, name: string): Expr => ({
    tag: "case",
    subject,
    alternatives: [
      {
        pattern: { tag: "con", name: con, args: [{ tag: "var", name: `${name}$w`, span }], span },
        body: variable(`${name}$w`, span),
      },
    ],
    span,
  });
  const names = args.map((_, i) => `$n${i}`);
  // How each argument reaches the wrapped type: `no` passes it through
  // untouched, `here` unwraps it, `under` unwraps what it returns.
  /** `[a]` with the class variable as the element: a list is the one type
   * constructor this pass can move a coercion through honestly, because `map`
   * is exactly that coercion. `Show`'s `showList` and miso's `toJSONList` are
   * both this shape, and both are what GHC's `coerce` walks straight past. */
  const listOfVar = (t: Type): boolean => {
    const p = prune(t);
    return p.tag === "app" && prune(p.fn).tag === "con" && (prune(p.fn) as { tag: "con"; name: string }).name === "[]" && coercible(p.arg);
  };
  const how = args.map((t): "no" | "here" | "under" | "list" | "bad" => {
    if (coercible(t)) return "here";
    if (!mentions(t)) return "no";
    if (listOfVar(t)) return "list";
    const { args: inner, result: innerResult } = splitFun(t);
    return inner.length > 0 && !inner.some(mentions) && coercible(innerResult) ? "under" : "bad";
  });
  if (how.includes("bad")) return undefined;
  /** `Parser a`, `Either String a`: the class variable is the *last argument*
   * of the result, and nothing else in it mentions the variable. GHC coerces
   * straight through such a result for free; here the newtype is a real
   * one-field constructor, so the only way through is `fmap`, which costs a
   * `Functor` constraint GHC does not need and an allocation GHC does not
   * make. For a lawful `Functor` it is the same value, and the alternative is
   * no instance at all - `newtype KeyCode = KeyCode Int deriving FromJSON`
   * needs exactly this. Where the `Functor` instance is missing, the ordinary
   * missing-instance diagnostic says so, which is no worse than refusing. */
  const underFunctor = ((): boolean => {
    const p = prune(result);
    return p.tag === "app" && !mentions(p.fn) && coercible(p.arg);
  })();
  const wrapResult = coercible(result);
  if (!wrapResult && !underFunctor && mentions(result)) return undefined;
  // Nothing to move: the class variable is not in this method's type at all,
  // so there is no way to say which instance the inner call should use.
  if (!how.some((h) => h !== "no") && !wrapResult && !underFunctor) return undefined;
  const inner = applyAll(
    variable(method.name, span),
    names.map((name, i): Expr => {
      if (how[i] === "here") return unwrapExpr(variable(name, span), name);
      if (how[i] === "list")
        return applyAll(variable("map", span), [
          { tag: "lambda", parameter: `${name}$e`, body: unwrapExpr(variable(`${name}$e`, span), `${name}$e`), span },
          variable(name, span),
        ]);
      if (how[i] !== "under") return variable(name, span);
      // `\x -> unwrap (k x)`: the argument is a function into the newtype, and
      // the inner call needs one into the wrapped type.
      const parameter = `${name}$x`;
      return {
        tag: "lambda",
        parameter,
        body: unwrapExpr(apply(variable(name, span), variable(parameter, span)), name),
        span,
      };
    }),
  );
  // No ascription is needed in the `fmap` case: the constructor's own field
  // type is what fixes the inner call's instance, so `fmap KeyCode (parseJSON
  // v)` already reads `parseJSON` at `Int`.
  const body = underFunctor
    ? applyAll(variable("fmap", span), [variable(con, span), inner])
    : wrapResult
      ? apply(
          variable(con, span),
          // With no argument at the wrapped type, only the ascription says
          // which instance the inner call means - otherwise it selects this
          // very instance and loops.
          how.some((h) => h !== "no") ? inner : { tag: "annot", expr: inner, type: wrapped, span },
        )
      : inner;
  return valueDecl(method.name, names.map((name): Pattern => ({ tag: "var", name, span })), body, span);
}

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
  const resolved = resolveProgram(withLibraryModules(modules), root, libraryModuleNames);
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
  const scopeOf = new Map<Declaration, Scopes>();
  const declarations: Declaration[] = [...prelude.module.ast.declarations];
  for (const module of resolved.order) {
    const scopes: Scopes = {
      values: resolved.scopes.get(module.name)!,
      types: resolved.typeScopes.get(module.name)!,
    };
    for (const decl of renameDeclarations(module, scopes, module.name === root, !libraryModuleNames.has(module.name), resolved.fields)) {
      scopeOf.set(decl, scopes);
      declarations.push(decl);
    }
  }
  // `deriving Generic` is generated as Haskell and parsed with everything
  // else; see `derivedGenericSource`. It joins the pile *after* the modules so
  // a hand-written `Generic` instance for the same type is seen first, and
  // wins the overlap comparison by being identical.
  const derivedDatas = declarations.filter((d): d is DataDeclaration => d.tag === "data");
  // `deriving Show` and `deriving Enum` are generated as Haskell too, and need
  // no scope at all: they name the flat constructors they were built from and
  // the Prelude's own `showsPrec`/`showString`/`showParen`/`error`, which are
  // never renamed.
  const showSource = derivedStockSource(derivedDatas);
  if (showSource) {
    const parsed = parseModule(showSource, "GHCTS/DerivedStock.hs");
    if (parsed.module && !parsed.diagnostics.some((d) => d.severity === "error"))
      declarations.push(...parsed.module.ast.declarations);
    else elaborator.diagnostics.push(...parsed.diagnostics);
  }
  const derivedSource = derivedGenericSource(derivedDatas);
  if (derivedSource) {
    const parsed = parseModule(derivedSource, "GHCTS/Derived.hs");
    if (parsed.module && !parsed.diagnostics.some((d) => d.severity === "error")) {
      // It writes `from`/`to`/`datatypeName` as `GHC.Generics` sees them, so it
      // is scoped as if it were inside that module - class methods are
      // module-scoped, and these instances have to name the same ones.
      const generics = resolved.scopes.get("GHC.Generics");
      const genericTypes = resolved.typeScopes.get("GHC.Generics");
      for (const decl of parsed.module.ast.declarations) {
        if (generics && genericTypes) scopeOf.set(decl, { values: generics, types: genericTypes });
        declarations.push(decl);
      }
    } else elaborator.diagnostics.push(...parsed.diagnostics);
  }
  const env: Env = new Map();

  // --- type synonyms ----------------------------------------------------
  // Expanded wherever a type is parsed, so `MisoString` and `Text` are one
  // type and an instance written at either head is found from both.
  synonyms = new Map();
  // Types share one global namespace here (see `src/modules.ts`), so a `type`
  // in one module and a `data`/`newtype` of the same name in another collide -
  // miso has two of each (`Parser`, `Object`). Where the synonym takes
  // parameters, arity tells the two apart at every use (see
  // `TypeParser.application`); where it is nullary nothing can, and the
  // declared type wins, because its constructors, patterns and instances all
  // key on `tcon(name)` and would otherwise be unreachable.
  const declaredTypes = new Set(declarations.flatMap((d) => (d.tag === "data" ? [d.name] : [])));
  for (const decl of declarations) {
    if (decl.tag !== "typeAlias" || !/^[A-Z]/.test(decl.name)) continue;
    if (decl.parameters.length === 0 && declaredTypes.has(decl.name)) continue;
    synonyms.set(decl.name, { parameters: decl.parameters, target: decl.target });
  }

  // --- data constructors -----------------------------------------------
  const datas = declarations.filter((d): d is DataDeclaration => d.tag === "data");
  for (const decl of datas) {
    for (const con of decl.constructors) {
      const vars = new Map<string, Type>();
      const params: TVar[] = [];
      const result = decl.parameters.reduce<Type>((acc, name) => {
        const v = freshVar();
        if (v.tag === "var") params.push(v.v);
        vars.set(name, v);
        return tapp(acc, v);
      }, tcon(decl.name));
      const fields = (con.fieldTypes ?? Array.from({ length: con.arity }, () => "_field")).map((f) => parseType(f, vars));
      const type = fields.reduceRight((acc, field) => tfun(field, acc), result);
      // A constructor's context is parsed one constraint at a time, and each
      // one contributes exactly one dictionary field whether it parsed or not:
      // the field count is a *layout* fact, shared with `desugar` through the
      // arity below, so it can never depend on how well a constraint read.
      const context = (con.context ?? []).map(
        (source, i): Constraint =>
          parseSignature(`${source} => Int`, vars).context[0] ?? { cls: `?${i}`, types: [freshVar()] },
      );
      // The datatype's own parameters are quantified first, in declaration
      // order, so `Proxy @flag` binds what GHC binds. Occurrence order - which
      // is the order the fields mention them in - would put `MkPair @a @b` of
      // `data Pair a b = MkPair b a` the wrong way round.  A variable only the
      // context mentions is quantified too, or it would be one shared variable
      // for every use of the constructor in the program.
      const ordered = [...params, ...typeVars(type).filter((v) => !params.includes(v))];
      for (const c of context)
        for (const t of c.types) for (const v of typeVars(t)) if (!ordered.includes(v)) ordered.push(v);
      elaborator.constructors.set(con.name, quantify(ordered, type, context));
      if (context.length === 0) continue;
      // GHC refuses to derive for a constructor with existentials or a context
      // ("Constructor `MkShowable' has existentials or constraints in its
      // type"), and the derived code here would be built at the declared arity
      // and silently miss the dictionary fields.
      const strategies = [...decl.deriving, ...(decl.derivingAnyclass ?? []), ...(decl.derivingNewtype ?? [])];
      if (strategies.length)
        elaborator.report(`cannot derive \`${strategies.join(", ")}\` for \`${decl.name}\`: \`${con.name}\` has a constructor context`, decl.span);
      elaborator.conDictFields.set(con.name, context.length);
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
  for (let arity = 2; arity <= 8; arity++) {
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
    // An associated type is an extra class parameter the class's own
    // parameters determine - `class At at where type Index at` says exactly
    // what `class At at index | at -> index` says - and the fundep solver
    // already improves such a parameter from the others. This is the same
    // reading `Rep`/`Generic` gets in `src/library.ts`, applied to whatever a
    // class actually declares.
    const families = decl.associatedTypes.map((a) => a.name);
    const parameters = [...decl.parameters, ...families.map((f) => `$assoc$${f}`)];
    const vars = new Map<string, Type>();
    const variables: TVar[] = [];
    for (const parameter of parameters) {
      const made = freshVar();
      if (made.tag !== "var") continue;
      vars.set(parameter, made);
      variables.push(made.v);
    }
    // `Index at` in a method's type *is* that extra parameter; the family is
    // never computed, only solved for, which is the whole of what this reading
    // can do and all miso asks of it.
    const familyVars = new Map(families.map((f) => [f, vars.get(`$assoc$${f}`)!]));
    const deFamily = (t: Type): Type => {
      const p = prune(t);
      if (p.tag !== "app") return p;
      const fn = prune(p.fn);
      if (fn.tag === "con") {
        const found = familyVars.get(fn.name);
        if (found) return found;
      }
      return tapp(deFamily(p.fn), deFamily(p.arg));
    };
    // Parsed against the same variable map as the methods, so `m` in
    // `class Monad m => MonadState s m` is the class's own second parameter.
    const supers = superclassesOf(decl, vars).map((c) => ({ cls: c.cls, types: c.types.map(deFamily) }));
    const fundeps = decl.fundeps.flatMap((fd) => {
      const index = (name: string): number => parameters.indexOf(name);
      const from = fd.from.map(index);
      const to = fd.to.map(index);
      if ([...from, ...to].some((i) => i < 0)) {
        elaborator.report(`class \`${decl.name}\`: a functional dependency names a parameter it does not have`, decl.span);
        return [];
      }
      return [{ from, to }];
    });
    for (let i = 0; i < families.length; i++)
      fundeps.push({ from: decl.parameters.map((_, j) => j), to: [decl.parameters.length + i] });
    const own = new Map<string, ValueDeclaration>();
    const classScope = scopeOf.get(decl);
    // A method body names the method it defines as it was *written*; the
    // signature above it has already been rewritten to the module-scoped name.
    const methodNames = new Set(classMethodNames(decl));
    const asMethod = (written: string, scope: Scopes | undefined): string => {
      const flat = scope?.values.get(written);
      return flat !== undefined && methodNames.has(flat) ? flat : written;
    };
    for (const value of instanceMethodValues(
      { tag: "instance", head: decl.name, associatedTypes: [], members: [], rawMembers: decl.rawMembers, span: decl.span },
      file,
    )) {
      const name = asMethod(value.name, classScope);
      own.set(name, classScope ? renameValue(value, classScope, name, resolved.fields) : { ...value, name });
    }
    const methods: ClassMethod[] = [];
    // Parsed against the same variable map as the methods, so the `a` of
    // `default toJSON :: (Generic a, GToJSON (Rep a)) => a -> Value` is the
    // class's own parameter and not a second one.
    const defaultSignatures = new Map<string, { context: Constraint[]; type: Type }>();
    for (const member of decl.members) {
      if (member.tag !== "signature" || member.isDefault !== true) continue;
      const parsed = parseSignature(member.type, vars);
      defaultSignatures.set(member.name, {
        context: parsed.context.map((c) => ({ cls: c.cls, types: c.types.map(deFamily) })),
        type: deFamily(parsed.type),
      });
    }
    for (const member of decl.members) {
      if (member.tag !== "signature" || member.isDefault === true) continue;
      const declared = defaultSignatures.get(member.name);
      const signature = parseSignature(member.type, vars);
      methods.push({
        name: member.name,
        surfaceName: member.surfaceName ?? member.name,
        type: deFamily(signature.type),
        // A constraint already mentioning only the class's own variables is the
        // class constraint over again, not an extra dictionary parameter.
        ownContext: signature.context
          .filter((c) => c.types.some((t) => typeVars(t).some((v) => !variables.includes(v))))
          .map((c) => ({ cls: c.cls, types: c.types.map(deFamily) })),
        hasDefault: own.has(member.name),
        ...(declared ? { defaultContext: declared.context, defaultType: declared.type } : {}),
      });
      if (own.has(member.name)) defaults.set(defaultImpl(decl.name, member.name), own.get(member.name)!);
    }
    elaborator.classes.set(decl.name, {
      name: decl.name,
      parameters,
      variables,
      superclasses: supers,
      fundeps,
      methods,
      span: decl.span,
    });
  }

  // A method's scheme is its declared signature plus its own class constraint,
  // quantified over the class variable first so the dictionary is argument
  // zero at every call site.
  for (const info of elaborator.classes.values()) {
    for (const method of info.methods) {
      const extra = [method.type, ...method.ownContext.flatMap((c) => c.types)].flatMap((t) => typeVars(t));
      const ordered = [...info.variables, ...extra.filter((v) => !info.variables.includes(v))];
      env.set(method.name, {
        tag: "poly",
        scheme: quantify(ordered, method.type, [
          { cls: info.name, types: info.variables.map(varType) },
          ...method.ownContext,
        ]),
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
    // An instance's `type Index (Map k v) = k` supplies the extra parameter
    // the class's associated type became. It is parsed against the head's own
    // variable map, so the `k` on the right is the `k` in `Map k v`.
    for (const family of info.parameters.slice(targets.length)) {
      const name = family.startsWith("$assoc$") ? family.slice("$assoc$".length) : family;
      const written = decl.associatedTypes.find((a) => a.name === name);
      if (!written?.rhs) {
        elaborator.report(`instance \`${decl.head}\`: no \`type ${name}\` for the class's associated type`, decl.span);
        break;
      }
      targets.push(parseType(written.rhs, vars));
    }
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
    // The instance writes the method under the name its own module sees it by;
    // the class knows it by its module-scoped name.  Only a scope answer that
    // really is a method of *this* class counts, so a top-level binding that
    // happens to share a method's name cannot capture the definition.
    const isMethod = new Set(info.methods.map((m) => m.name));
    // An instance's method binder is resolved against the *class*, not the
    // value namespace: `import Miso.String (ToMisoString)` brings in the class
    // without `toMisoString`, and `instance ToMisoString Value where
    // toMisoString = ...` is still legal. So when the scope has no answer, the
    // name the class was declared under is one.
    const bySurface = new Map(info.methods.map((m) => [m.surfaceName, m.name]));
    for (const value of instanceMethodValues(decl, file)) {
      const flat = instanceScope?.values.get(value.name) ?? bySurface.get(value.name);
      const name = flat !== undefined && isMethod.has(flat) ? flat : value.name;
      methods.set(name, instanceScope ? renameValue(value, instanceScope, name, resolved.fields) : { ...value, name });
    }
    // Two instances at the same head are not an error here the way they are in
    // GHC: `Data.Text.Text`, `Data.Text.Lazy.Text` and `MisoString` are all the
    // one `JSString`, so a library that writes an instance for each has written
    // the same instance three times, not three conflicting ones.
    const emitCon = instanceKey(targets);
    elaborator.addInstance(`${parsed.className} ${emitCon}`, {
      cls: parsed.className,
      targets,
      targetCons,
      emitCon,
      context,
      params: context.map((c, i) => ({ cls: c.cls, types: c.types, name: `$d${i}` })),
      vars,
      methods,
      span: decl.span,
    });
  }

  // --- deriving ----------------------------------------------------------
  /** One derived instance, in whichever strategy asked for it. A hand-written
   * instance at the same head wins; `build` returning `undefined` means the
   * strategy could not produce one, and has said why. */
  const deriveInstance = (
    cls: string,
    decl: DataDeclaration,
    build: (vars: Type[]) => { context: Constraint[]; methods: Map<string, ValueDeclaration> } | undefined,
    /** Parameters the instance head keeps. A class over `* -> *` is derived at
     * `C N`, not `C (N a)`, so its last parameter is abstracted away rather
     * than named - and must not scope over the methods either. */
    headArity = decl.parameters.length,
  ): void => {
    const vars = decl.parameters.map(() => freshVar());
    const target = vars.slice(0, headArity).reduce<Type>(tapp, tcon(decl.name));
    const emitCon = instanceKey([target]);
    if (elaborator.instances.has(`${cls} ${emitCon}`)) return;
    const built = build(vars);
    if (!built) return;
    elaborator.addInstance(`${cls} ${emitCon}`, {
      cls,
      targets: [target],
      targetCons: [decl.name],
      emitCon,
      context: built.context,
      params: built.context.map((c, i) => ({ cls: c.cls, types: c.types, name: `$d${i}` })),
      vars: new Map(decl.parameters.slice(0, headArity).map((p, i) => [p, vars[i]!])),
      methods: built.methods,
      span: decl.span,
    });
  };

  for (const decl of datas) {
    // `deriving Eq` is an instance like any other: one constrained by `Eq` at
    // each type parameter, whose `==` is the structural comparison.
    if (decl.deriving.includes("Eq"))
      deriveInstance("Eq", decl, (vars) => ({
        context: vars.map((type) => ({ cls: "Eq", types: [type] })),
        methods: new Map([["==", derivedEqMethod(decl)]]),
      }));

    // `deriving anyclass C` is the *empty* instance: every method comes from
    // the class's own default, which is how `deriving anyclass (ToJSON)` picks
    // up a `default toJSON` written over `Generic`.
    for (const cls of decl.derivingAnyclass ?? []) {
      const info = elaborator.classes.get(cls);
      if (!info || info.variables.length !== 1) {
        elaborator.report(
          `\`deriving anyclass ${cls}\`: ${info ? "only a single-parameter class can be derived" : "unknown class"}`,
          decl.span,
        );
        continue;
      }
      deriveInstance(cls, decl, (vars) => ({
        // GHC infers this context from the default methods' own signatures. A
        // constraint on each parameter is the same answer wherever the default
        // is the `Generic` one - the case the strategy exists for - because
        // that default reaches every field through the representation.
        context: vars.map((type) => ({ cls, types: [type] })),
        methods: new Map(),
      }));
    }

    // GeneralizedNewtypeDeriving. A bare `deriving` clause on a newtype means
    // the coercion strategy for every class GHC has no stock rule for - which
    // is what miso's `newtype Parser a = ... deriving (Functor, Applicative,
    // Monad)` says. The stock-derivable classes are excluded because their
    // stock instance is *not* the wrapped type's: `deriving Show` on a newtype
    // prints the constructor. `Functor` is the exception GHC also makes - for a
    // newtype the two strategies agree - and it is the one this needs.
    const STOCK = ["Eq", "Ord", "Show", "Read", "Enum", "Bounded", "Ix", "Generic", "Data", "Lift"];
    const byCoercion = [
      ...(decl.derivingNewtype ?? []),
      ...(decl.newtype === true ? decl.deriving.filter((c) => !STOCK.includes(c)) : []),
    ];
    for (const cls of new Set(byCoercion)) {
      const info = elaborator.classes.get(cls);
      const con = decl.constructors[0];
      const wrapped = con?.fieldTypes?.[0]?.replace(/^\s*!/, "").trim();
      if (!info || info.variables.length !== 1 || decl.newtype !== true || decl.constructors.length !== 1 || con?.arity !== 1 || !wrapped) {
        elaborator.report(
          `\`deriving newtype ${cls}\`: needs a single-parameter class and a newtype whose wrapped type is written out`,
          decl.span,
        );
        continue;
      }
      // A class over `* -> *` - one whose variable is *applied* in a method's
      // type - is derived at the newtype's head: `Functor Parser`, from
      // `Functor (Either MisoString)`. That needs the newtype's own last
      // parameter to be the wrapped type's last argument, so that `Parser x`
      // and `Either MisoString x` are the same values one constructor apart.
      const classVar = info.variables[0]!;
      const higherKinded = info.methods.some((m) => appliesVar(m.type, classVar));
      const headArity = decl.parameters.length - (higherKinded ? 1 : 0);
      if (headArity < 0) {
        elaborator.report(`\`deriving newtype ${cls}\`: \`${decl.name}\` has no parameter to abstract`, decl.span);
        continue;
      }
      deriveInstance(
        cls,
        decl,
        (vars) => {
          const scope = new Map(decl.parameters.map((p, i) => [p, vars[i]!] as const));
          let underlying = parseType(wrapped, scope);
          if (higherKinded) {
            const applied = prune(underlying);
            const last = vars[decl.parameters.length - 1]!;
            if (applied.tag !== "app" || !sameType(applied.arg, last)) {
              elaborator.report(
                `\`deriving newtype ${cls}\`: \`${wrapped}\` does not end in \`${decl.parameters.at(-1)}\`, so the constructor cannot be moved through it`,
                decl.span,
              );
              return undefined;
            }
            underlying = applied.fn;
          }
          const methods = new Map<string, ValueDeclaration>();
          for (const method of info.methods) {
            const built = newtypeMethod(method, classVar, con.name, wrapped, decl.span);
            if (!built) {
              elaborator.report(
                `\`deriving newtype ${cls}\`: \`${method.name}\` mentions the class variable somewhere the newtype's constructor cannot be moved through`,
                decl.span,
              );
              return undefined;
            }
            methods.set(method.name, built);
          }
          // GND's context is the constraint on the wrapped type, not on the
          // parameters: `instance C (Maybe a) => C (Wrap a)`.
          return { context: [{ cls, types: [underlying] }], methods };
        },
        headArity,
      );
    }
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
    tyvars: ReadonlyMap<string, Type> = new Map(),
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
      tyvars,
      givens: [],
      patternGivens: [],
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
    //
    // The skolemised copy's variables are kept by name, which is
    // ScopedTypeVariables: a `forall p .` in the signature puts `p` in scope
    // for the body, so `symbolVal (Proxy :: Proxy p)` names the *rigid* `p`
    // its `KnownSymbol p` given is about. Without it the annotation invented a
    // fresh variable and the given matched nothing.
    const named = new Map<string, Type>();
    addBinding(
      decl.name,
      decl,
      signature ? skolemise(parseSignature(signature, named)) : undefined,
      signature ? parseSignature(signature, new Map()) : undefined,
      skolemNames(named),
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
      const own = method.ownContext.map((c) => ({
        cls: c.cls,
        types: c.types.map((t) => substituteVars(t, info.variables, instance.targets)),
      }));
      const at = skolemise({
        // Instance context first, then the method's own: the same order the
        // call site applies them in, since selecting the field discharges the
        // class constraint and leaves the method's own to be applied on top.
        context: [...instance.context, ...own],
        type: substituteVars(method.type, info.variables, instance.targets),
      });
      const implName = methodImpl(instance.cls, instance.emitCon, method.name);
      addBinding(implName, { ...decl, name: implName }, at, undefined, skolemNames(instance.vars));
    }
  }
  for (const info of elaborator.classes.values()) {
    for (const method of info.methods) {
      if (!method.hasDefault) continue;
      const decl = defaults.get(defaultImpl(info.name, method.name))!;
      const skolems = info.variables.map((_, i) => tcon(`%${info.name}${i}`));
      const at = (t: Type): Type => substituteVars(t, info.variables, skolems);
      addBinding(
        defaultImpl(info.name, method.name),
        { ...decl, name: defaultImpl(info.name, method.name) },
        // The class's own dictionary first - the default is a function of the
        // instance being built - then whatever a `default f ::` signature asks
        // for on top, in the order it wrote them. `instanceDeclaration` passes
        // them in the same order.
        skolemise({
          context: [
            { cls: info.name, types: skolems },
            ...(method.defaultContext ?? []).map((c) => ({ cls: c.cls, types: c.types.map(at) })),
            // Last, because `instanceDeclaration` supplies the two above when
            // it builds the dictionary and only the call site can supply this.
            ...method.ownContext.map((c) => ({ cls: c.cls, types: c.types.map(at) })),
          ],
          type: at(method.defaultType ?? method.type),
        }),
        undefined,
        // The class's own parameters scope over its default methods' bodies,
        // at the same skolems the synthesised signature above uses.
        new Map(info.parameters.map((p, i) => [p, skolems[i] ?? freshVar()])),
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
  // A constructor with a context is one field wider per constraint, and
  // `desugar` builds its `DataCon` straight from `arity`.  Widening here rather
  // than in the parser keeps the count identical to the one this pass actually
  // parsed a constraint for, and leaves a context-free constructor's
  // declaration byte-for-byte the object it always was.
  const withDictFields = (d: Declaration): Declaration =>
    d.tag === "data" && d.constructors.some((c) => elaborator.conDictFields.has(c.name))
      ? {
          ...d,
          constructors: d.constructors.map((c) => ({ ...c, arity: c.arity + (elaborator.conDictFields.get(c.name) ?? 0) })),
        }
      : d;
  const out: Declaration[] = [
    listData,
    ...declarations.filter((d) => d.tag === "data" || d.tag === "foreign").map(withDictFields),
  ];
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
  // Every `static e` the program contains, in the order the parser floated
  // them out (`$static0`, or `Miso_Types_$static0` once a non-root module's
  // names are flattened).
  const staticEntries = bindings.map((b) => b.name).filter((n) => /(?:^|_)\$static\d+$/.test(n));
  for (const binding of bindings) {
    const decl = rewriteBinding(elaborator, binding);
    if (binding !== mainBinding || !wrapMain) {
      out.push(decl);
      continue;
    }
    out.push({ ...decl, name: "$mainIO" });
    // GHC registers the static pointer table from module initialisers, which
    // run before `main`. The JS backend's initialisers are emitted by the
    // *code generator*, which this frontend does not reach, so the same
    // "before anything else" is bought by sequencing the registrations in
    // front of `main` itself - the earliest point a Haskell program has.
    // `sptRegisterThen`, not `>>`: this declaration is built *after*
    // elaboration, so it may not name a class method - there is no dictionary
    // left to pass one.
    const body = staticEntries.reduceRight<Expr>(
      (rest, name) =>
        apply(apply(variable("sptRegisterThen", decl.span), variable(name, decl.span)), rest),
      variable("$mainIO", decl.span),
    );
    out.push(valueDecl("main", [], apply(variable("runMainIO", decl.span), body), decl.span));
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
  primFloatAdd: "FloatPrim -> FloatPrim -> FloatPrim",
  primFloatSub: "FloatPrim -> FloatPrim -> FloatPrim",
  primFloatMul: "FloatPrim -> FloatPrim -> FloatPrim",
  primFloatDiv: "FloatPrim -> FloatPrim -> FloatPrim",
  primFloatNeg: "FloatPrim -> FloatPrim",
  primFloatAbs: "FloatPrim -> FloatPrim",
  primFloatEq: "FloatPrim -> FloatPrim -> Bool",
  primFloatLt: "FloatPrim -> FloatPrim -> Bool",
  primFloatLe: "FloatPrim -> FloatPrim -> Bool",
  primFloatGt: "FloatPrim -> FloatPrim -> Bool",
  primFloatGe: "FloatPrim -> FloatPrim -> Bool",
  primFloatToDouble: "FloatPrim -> DoublePrim",
  primDoubleToFloat: "DoublePrim -> FloatPrim",
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
  // GHC's `realWorld# :: State# RealWorld`. It is a value of a void type, so
  // it is not an operation at all: `src/desugar.ts` resolves it to a binder
  // that occupies no JS value, and every reference to it disappears.
  primRealWorld: "RealWorld",
  primNewMVar: "RealWorld -> MVarPrim a",
  primTakeMVar: "MVarPrim a -> a",
  primPutMVar: "MVarPrim a -> a -> VoidPrim",
  primReadMVar: "MVarPrim a -> a",
  primTryPutMVar: "MVarPrim a -> a -> Bool",
  primIsEmptyMVar: "MVarPrim a -> Bool",
  primWordAdd: "WordPrim -> WordPrim -> WordPrim",
  primWordSub: "WordPrim -> WordPrim -> WordPrim",
  primWordMul: "WordPrim -> WordPrim -> WordPrim",
  primWordQuot: "WordPrim -> WordPrim -> WordPrim",
  primWordRem: "WordPrim -> WordPrim -> WordPrim",
  primWordEq: "WordPrim -> WordPrim -> Bool",
  primWordLt: "WordPrim -> WordPrim -> Bool",
  primWordLe: "WordPrim -> WordPrim -> Bool",
  primWordGt: "WordPrim -> WordPrim -> Bool",
  primWordGe: "WordPrim -> WordPrim -> Bool",
  primIntToWord: "IntPrim -> WordPrim",
  primWordToDouble: "WordPrim -> DoublePrim",
  primMakeStableName: "a -> StableNamePrim",
  primStableNameInt: "StableNamePrim -> IntPrim",
  primFork: "a -> ThreadIdPrim",
  primDelay: "IntPrim -> VoidPrim",
  // GHC's `catch#`, `raiseIO#` and `killThread#`, at their real types. The
  // action and the handler are functions of the state token, which is what
  // makes them closures the RTS can enter with `h$ap_1_0`/`h$ap_2_1`.
  primCatch: "(RealWorld -> IOResult a) -> (JSValPrim -> RealWorld -> IOResult a) -> RealWorld -> IOResult a",
  primRaiseIO: "JSValPrim -> RealWorld -> IOResult a",
  primKillThread: "ThreadIdPrim -> JSValPrim -> RealWorld -> VoidPrim",
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

/** The same substitution `skolemise` performs, read off by name. Both spell a
 * skolem `%${v.id}`, so a scope's variables and the signature they were parsed
 * with stay the same types without threading a substitution through. */
function skolemNames(vars: ReadonlyMap<string, Type>): Map<string, Type> {
  const out = new Map<string, Type>();
  for (const [name, t] of vars) {
    const p = prune(t);
    if (p.tag === "var") out.set(name, tcon(`%${p.v.id}`));
  }
  return out;
}

/** Dependency order, so a binding's scheme (and therefore its dictionary
 * parameters) is known before anything that calls it is inferred. Mutually
 * recursive bindings are inferred together and monomorphically. */
function orderBindings(bindings: readonly Binding[]): Binding[][] {
  return dependencyGroups(
    bindings.map((b) => b.name),
    bindings.map((b) => referencedNames(b.decl)),
  ).map((group) => group.map((i) => bindings[i]!));
}

/** Tarjan's strongly connected components over "this binding names that one",
 * yielding indices in dependency order. Shared by the top level and by
 * `let`/`where` groups, which need the same answer for the same reason: a
 * binding's scheme has to exist before anything that calls it is inferred. */
function dependencyGroups(names: readonly string[], refs: readonly ReadonlySet<string>[]): number[][] {
  const index = new Map(names.map((name, i) => [name, i]));
  const edges = refs.map((set) => [...set].flatMap((name) => {
    const target = index.get(name);
    return target === undefined ? [] : [target];
  }));
  // Tarjan, iterative order not needed at this size.
  const lowlink = new Array<number>(names.length).fill(-1);
  const number = new Array<number>(names.length).fill(-1);
  const onStack = new Array<boolean>(names.length).fill(false);
  const stack: number[] = [];
  const groups: number[][] = [];
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
      const group: number[] = [];
      for (;;) {
        const w = stack.pop()!;
        onStack[w] = false;
        group.push(w);
        if (w === v) break;
      }
      groups.push(group);
    }
  };
  for (let v = 0; v < names.length; v++) if (number[v] === -1) strongconnect(v);
  return groups;
}

/** A `let`/`where` binding read as the one-equation declaration it is, so the
 * free-variable walk the top level uses serves the local groups too. */
function localAsDeclaration(b: LocalBinding): ValueDeclaration {
  return {
    tag: "value",
    name: b.name,
    equations: [{ patterns: b.patterns, guards: b.guards ?? [{ body: b.value }], whereBindings: b.whereBindings ?? [] }],
    span: b.span,
  };
}

function referencedNames(decl: ValueDeclaration): Set<string> {
  const names = new Set<string>();
  const expr = (e: Expr): void => {
    switch (e.tag) {
      case "var":
        names.add(e.name);
        return;
      case "annot":
      case "typeApp":
        expr(e.expr);
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
  const qualifiers = (qs: readonly GuardQualifier[] | undefined): void => {
    for (const q of qs ?? []) expr(q.tag === "bool" ? q.condition : q.source);
  };
  const alternative = (alt: CaseAlternative): void => {
    qualifiers(alt.qualifiers);
    expr(alt.body);
  };
  const local = (b: LocalBinding): void => {
    for (const guard of b.guards ?? [{ body: b.value }]) {
      qualifiers(guard.qualifiers);
      expr(guard.body);
    }
    for (const w of b.whereBindings ?? []) local(w);
  };
  for (const equation of decl.equations) {
    for (const guard of equation.guards) {
      qualifiers(guard.qualifiers);
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
  const methods = info.methods.map((method) => {
    if (instance.methods.has(method.name))
      return applyAll(variable(methodImpl(instance.cls, instance.emitCon, method.name), instance.span), args);
    // The default is a function of this very dictionary, which is why the
    // instance binding is a genuinely self-referential CAF. It terminates
    // because the field is a thunk, never a forced value.
    //
    // A `default f ::` signature adds constraints on top, at this instance's
    // own types: `default toJSON :: (Generic a, GToJSON (Rep a)) => ...` used
    // at `instance ToJSON Colour` needs `Generic Colour rep` and `GToJSON rep`.
    // `rep` is not written anywhere, so the fundep has to supply it first -
    // improvement, then selection, exactly as an ordinary call site does.
    //
    // `freshen`, not `applySubst`: a `Rep a` in the default's context became a
    // variable that `ClassInfo` holds *once*, so every instance deriving this
    // method would otherwise improve the same variable and the second would
    // report a fundep conflict with the first. Seeding the substitution with
    // the class variables keeps `Generic a rep` and `GToJSON rep` sharing one
    // `rep` within this instance while giving each instance its own.
    const fresh = new Map(at);
    const extra = (method.defaultContext ?? []).map((c) => {
      const at_ = c.types.map((t) => freshen(t, fresh));
      elaborator.improveOne({ cls: c.cls, types: at_ }, instance.params, instance.span);
      return elaborator.resolve(c.cls, at_, instance.params, instance.span) ?? errorExpr(instance.span);
    });
    return applyAll(variable(defaultImpl(instance.cls, method.name), instance.span), [self, ...extra]);
  });
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
      // Only a literal with a written non-`[Char]` type has a dictionary; a
      // plain `[Char]` literal is left exactly as it was.
      case "string":
        return args?.length ? applyAll(variable("fromString", e.span), [...args, e]) : e;
      case "annot":
      case "typeApp":
        return { ...e, expr: rewriteExpr(e.expr) };
      case "app":
        return { ...e, fn: rewriteExpr(e.fn), arg: rewriteExpr(e.arg) };
      case "lambda":
        return elaborator.isVoidRep(e)
          ? { ...e, voidRep: true, body: rewriteExpr(e.body) }
          : { ...e, body: rewriteExpr(e.body) };
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
  const rewriteQualifiers = (qs: GuardQualifier[] | undefined): GuardQualifier[] | undefined =>
    qs?.map((q) =>
      q.tag === "bool"
        ? { ...q, condition: rewriteExpr(q.condition) }
        : { ...q, pattern: rewritePattern(elaborator, q.pattern), source: rewriteExpr(q.source) },
    );
  const rewriteAlt = (alt: CaseAlternative): CaseAlternative => ({
    ...alt,
    pattern: rewritePattern(elaborator, alt.pattern),
    qualifiers: rewriteQualifiers(alt.qualifiers),
    body: rewriteExpr(alt.body),
  });
  const rewriteGuard = (guard: Guard): Guard => ({
    ...guard,
    qualifiers: rewriteQualifiers(guard.qualifiers),
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

/** A numeric literal pattern at `Double`/`Float` matches the one-field box and
 * then the raw JS number, exactly as an `Int` literal matches `I` and then its
 * machine word.  An integer literal at `Double` is the double of that whole
 * number, which is what the literal alternative has to carry. */
function boxedDouble(elaborator: Elaborator, p: Extract<Pattern, { tag: "int" | "double" }>): Pattern {
  const box = elaborator.doubleLit.get(p);
  if (!box) return p;
  return {
    tag: "con",
    name: box === "Double" ? "DoubleBox" : "FloatBox",
    args: [{ tag: "double", value: p.value, span: p.span }],
    span: p.span,
  };
}

function rewritePattern(elaborator: Elaborator, p: Pattern): Pattern {
  switch (p.tag) {
    case "double":
      return boxedDouble(elaborator, p);
    case "int":
      if (elaborator.boxedInt.has(p)) return { tag: "con", name: "I", args: [p], span: p.span };
      return boxedDouble(elaborator, p);
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
      if (p.name === "()" && p.args.length === 0) return { tag: "int", value: 0, span: p.span };
      // The dictionary fields are stored ahead of the declared ones, so the
      // match binds them ahead of them too - which is exactly what makes the
      // rewritten pattern as wide as the constructor's real arity.
      return {
        ...p,
        args: [
          ...(elaborator.conPatternDicts.get(p) ?? []).map((name): Pattern => ({ tag: "var", name, span: p.span })),
          ...p.args.map((arg) => rewritePattern(elaborator, arg)),
        ],
      };
    // The state token is the one type with no runtime value at all, so a
    // binder at that type has to say so before types are erased.
    case "var":
    case "wild":
      return elaborator.isVoidRep(p) ? { ...p, voidRep: true } : p;
    default:
      return p;
  }
}
