/** Surface AST (`src/ast.ts`) to Core (`src/core.ts`).
 *
 * Scope. This pass deliberately targets the class-free fragment of Haskell:
 * literals, arithmetic, data types, constructors, pattern matching, `case`,
 * `let`/`where`, guards, lambdas, saturated application and `foreign import
 * javascript`. Anything that would need a dictionary - a class method, an
 * instance, `do` notation, a list comprehension - produces a diagnostic and
 * an expression that raises, so one unsupported construct never silently
 * corrupts the rest of the module.
 *
 * Representation choices that follow from having no classes:
 *
 *   - an integer literal IS an `Int#`. With no `Num` dictionary there is
 *     nothing to select an instance from, so `+` is `IntAddOp` directly and
 *     `Int` never gets boxed into `I#`. This is the same shape the terms in
 *     `scripts/stg-run.mjs` already run on.
 *   - `Bool` is an `Int#`: `False` is 0, `True` is 1. That is exactly what
 *     the comparison primops return in the JS backend (`IntEqOp` yields 1 or
 *     0), so `if x == y` needs no conversion at all, and pattern matching on
 *     `True`/`False` is literal matching.
 */
import type {
  CaseAlternative,
  Declaration,
  Expr,
  Guard,
  LocalBinding,
  Module,
  Pattern,
  Span,
} from "./ast.js";
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "./core.js";
import { coreFreeVars, mkApps, mkLams } from "./core.js";
import { error } from "./diagnostics.js";
import type { Binder, DataCon, Literal, StgOp } from "./stg.js";
import { mkBinder, mkDataCon } from "./stg.js";
import type { Diagnostic } from "./types.js";

export interface DesugarResult {
  program: CoreProgram;
  diagnostics: Diagnostic[];
}

const int = (value: number): Literal => ({ tag: "LitNumInt", value: BigInt(Math.trunc(value)) });

/** Source name to primop. Every entry is binary except `negate`/`not`.
 * Only ops the JS backend implements appear here (see src/stg-js/prim.ts). */
const primOps: Record<string, { op: string; arity: number }> = {
  "+": { op: "IntAddOp", arity: 2 },
  "-": { op: "IntSubOp", arity: 2 },
  "*": { op: "IntMulOp", arity: 2 },
  div: { op: "IntQuotOp", arity: 2 },
  quot: { op: "IntQuotOp", arity: 2 },
  mod: { op: "IntRemOp", arity: 2 },
  rem: { op: "IntRemOp", arity: 2 },
  "==": { op: "IntEqOp", arity: 2 },
  "/=": { op: "IntNeOp", arity: 2 },
  "<": { op: "IntLtOp", arity: 2 },
  "<=": { op: "IntLeOp", arity: 2 },
  ">": { op: "IntGtOp", arity: 2 },
  ">=": { op: "IntGeOp", arity: 2 },
  negate: { op: "IntNegOp", arity: 1 },
};

/** What a name resolves to. Locals shadow top levels, which shadow
 * constructors, which shadow primops. */
type Scope = ReadonlyMap<string, Binder>;

class Desugarer {
  readonly diagnostics: Diagnostic[] = [];
  readonly cons = new Map<string, DataCon>();
  readonly top = new Map<string, Binder>();
  /** Names introduced by a `class` declaration, so a use of one can say
   * "dictionary elaboration" instead of "not in scope". */
  readonly classMethods = new Set<string>();

  constructor(private readonly file: string) {}

  fail(feature: string, span: Span): CoreExpr {
    this.diagnostics.push(
      error("GHCTS-DESUGAR", `${feature} is not supported by the STG frontend yet`, this.file, span.line, span.column),
    );
    return raise();
  }

  /** Constructors are looked up by name across the module; tuples and list
   * cells are synthesised on demand so class-free code can still build them. */
  lookupCon(name: string, arity: number): DataCon {
    const found = this.cons.get(name);
    if (found) return found;
    const made =
      name === "[]"
        ? mkDataCon("[]", 1, 0, "[]")
        : name === ":"
          ? mkDataCon(":", 2, 2, "[]")
          : mkDataCon(name, 1, arity, name);
    this.cons.set(name, made);
    return made;
  }

  expr(e: Expr, scope: Scope): CoreExpr {
    switch (e.tag) {
      case "int":
        return { tag: "Lit", lit: int(e.value) };
      case "string":
        return { tag: "Lit", lit: { tag: "LitString", value: e.value } };
      case "unit":
        return { tag: "Lit", lit: int(0) };
      case "var":
        return this.varRef(e.name, scope, e.span);
      case "app": {
        const [head, args] = flattenApp(e);
        return this.application(head, args, scope);
      }
      case "lambda": {
        const binder = mkBinder(e.parameter);
        return { tag: "Lam", binder, body: this.expr(e.body, extend(scope, [[e.parameter, binder]])) };
      }
      case "lambdaCase": {
        const binder = mkBinder("lcase");
        return {
          tag: "Lam",
          binder,
          body: this.alternatives({ tag: "Var", binder }, e.alternatives, scope, e.span),
        };
      }
      case "if": {
        // False is 0, so the literal alternative is the else branch and
        // DEFAULT catches every non-zero value, matching what the comparison
        // primops produce.
        const binder = mkBinder("cond");
        return {
          tag: "Case",
          scrutinee: this.expr(e.condition, scope),
          binder,
          alts: [
            { con: { tag: "LitAlt", lit: int(0) }, binders: [], body: this.expr(e.elseBranch, scope) },
            { con: { tag: "DEFAULT" }, binders: [], body: this.expr(e.thenBranch, scope) },
          ],
        };
      }
      case "case": {
        const scrutinee = this.expr(e.subject, scope);
        return this.alternatives(scrutinee, e.alternatives, scope, e.span);
      }
      case "let": {
        const [binds, inner] = this.localGroup(e.bindings, scope);
        return binds.reduceRight<CoreExpr>((body, bind) => ({ tag: "Let", bind, body }), this.expr(e.body, inner));
      }
      case "tuple": {
        const con = this.lookupCon(`(${",".repeat(e.items.length - 1)})`, e.items.length);
        return { tag: "Con", con, args: e.items.map((item) => this.expr(item, scope)) };
      }
      case "list":
        return e.items.reduceRight<CoreExpr>(
          (tail, item) => ({ tag: "Con", con: this.lookupCon(":", 2), args: [this.expr(item, scope), tail] }),
          { tag: "Con", con: this.lookupCon("[]", 0), args: [] },
        );
      case "do":
        return this.fail("do notation (it needs a Monad dictionary)", e.span);
      case "listComp":
        return this.fail("list comprehensions", e.span);
      case "record":
      case "recordUpdate":
        return this.fail("record syntax", e.span);
      case "jsQuote":
        return this.fail("JS quotation", e.span);
    }
  }

  varRef(name: string, scope: Scope, span: Span): CoreExpr {
    const local = scope.get(name);
    if (local) return { tag: "Var", binder: local };
    if (name === "True" || name === "otherwise") return { tag: "Lit", lit: int(1) };
    if (name === "False") return { tag: "Lit", lit: int(0) };
    const con = this.cons.get(name);
    if (con) return this.saturateCon(con, []);
    const prim = primOps[name];
    if (prim) return this.saturateOp(prim, []);
    if (this.classMethods.has(name)) {
      return this.fail(`class method \`${name}\` (dictionary elaboration)`, span);
    }
    return this.fail(`\`${name}\` is not in scope`, span);
  }

  /** Con and Op nodes must come out saturated (see src/core.ts). An
   * under-applied occurrence becomes a lambda that supplies the rest. */
  saturateCon(con: DataCon, args: CoreExpr[]): CoreExpr {
    if (args.length === con.arity) return { tag: "Con", con, args };
    if (args.length > con.arity) {
      // Over-application of a constructor cannot happen in well-typed code.
      return mkApps({ tag: "Con", con, args: args.slice(0, con.arity) }, args.slice(con.arity));
    }
    const extra = Array.from({ length: con.arity - args.length }, (_, i) => mkBinder(`${con.name}_${i}`));
    return mkLams(extra, { tag: "Con", con, args: [...args, ...extra.map(varOf)] });
  }

  saturateOp(prim: { op: string; arity: number }, args: CoreExpr[]): CoreExpr {
    const op: StgOp = { tag: "StgPrimOp", op: prim.op };
    if (args.length >= prim.arity) {
      return mkApps({ tag: "Op", op, arity: prim.arity, args: args.slice(0, prim.arity) }, args.slice(prim.arity));
    }
    const extra = Array.from({ length: prim.arity - args.length }, (_, i) => mkBinder(`p${i}`));
    return mkLams(extra, { tag: "Op", op, arity: prim.arity, args: [...args, ...extra.map(varOf)] });
  }

  application(head: Expr, args: Expr[], scope: Scope): CoreExpr {
    const lowered = args.map((arg) => this.expr(arg, scope));
    if (head.tag === "var" && !scope.has(head.name)) {
      const con = this.cons.get(head.name);
      if (con) return this.saturateCon(con, lowered);
      const prim = primOps[head.name];
      if (prim) return this.saturateOp(prim, lowered);
    }
    return mkApps(this.expr(head, scope), lowered);
  }

  /** `case` and `\case` alternatives; guards inside an alternative fall
   * through to the next alternative when none succeeds. */
  alternatives(scrutinee: CoreExpr, alts: CaseAlternative[], scope: Scope, span: Span): CoreExpr {
    const subject = mkBinder("scrut");
    const rows = alts.map((alt) => ({
      patterns: [alt.pattern],
      guards: alt.guard ? [{ condition: alt.guard, body: alt.body }] : [{ body: alt.body }],
      whereBindings: [] as LocalBinding[],
      hasPatternGuards: (alt.patternGuards?.length ?? 0) > 0,
    }));
    for (const row of rows) if (row.hasPatternGuards) this.fail("pattern guards", span);
    return {
      tag: "Case",
      scrutinee,
      binder: subject,
      alts: [
        {
          con: { tag: "DEFAULT" },
          binders: [],
          body: this.match([subject], rows, scope, raise()),
        },
      ],
    };
  }

  /** The pattern-match compiler, in the classic left-to-right form. Rows are
   * tried in order; the first column that actually discriminates becomes a
   * `case`, and every other column is deferred by recursion. */
  match(subjects: Binder[], rows: MatchRow[], scope: Scope, fallback: CoreExpr): CoreExpr {
    if (rows.length === 0) return fallback;
    if (subjects.length === 0) return this.guardedBody(rows[0]!, scope, () => this.match([], rows.slice(1), scope, fallback));

    const column = subjects.findIndex((_, i) => rows.some((row) => isRefutable(row.patterns[i]!)));
    if (column < 0) {
      // Every remaining pattern binds or ignores; bind the first row's names.
      const row = rows[0]!;
      const inner = extend(scope, bindingsOf(subjects, row.patterns));
      return this.guardedBody(row, inner, () => this.match(subjects, rows.slice(1), scope, fallback));
    }

    const subject = subjects[column]!;
    const groups = new Map<string, MatchRow[]>();
    const order: Array<{ key: string; pattern: Pattern }> = [];
    const defaults: MatchRow[] = [];
    for (const row of rows) {
      const pattern = row.patterns[column]!;
      if (!isRefutable(pattern)) {
        defaults.push(row);
        // A variable row also matches every constructor seen so far and any
        // seen later, so it joins each group as well.
        for (const [, group] of groups) group.push(row);
        continue;
      }
      const key = patternKey(pattern);
      if (!groups.has(key)) {
        groups.set(key, [...defaults]);
        order.push({ key, pattern });
      }
      groups.get(key)!.push(row);
    }

    // The default rows keep every column, including this one: their pattern
    // there is a variable that still has to bind the scrutinee's name. The
    // recursion terminates anyway because the row set strictly shrinks.
    const defaultBody = (): CoreExpr => this.match(subjects, defaults, scope, fallback);

    const alts: CoreAlt[] = order.map(({ key, pattern }) => {
      const group = groups.get(key)!;
      if (pattern.tag === "int") {
        return {
          con: { tag: "LitAlt", lit: int(pattern.value) },
          binders: [],
          body: this.matchGroup(subjects, group, column, [], scope, fallback),
        };
      }
      if (pattern.tag === "con" && (pattern.name === "True" || pattern.name === "False")) {
        return {
          con: { tag: "LitAlt", lit: int(pattern.name === "True" ? 1 : 0) },
          binders: [],
          body: this.matchGroup(subjects, group, column, [], scope, fallback),
        };
      }
      const con = this.lookupCon(patternConName(pattern), patternArity(pattern));
      const fields = Array.from({ length: con.arity }, (_, i) => mkBinder(`${con.name}_f${i}`));
      return {
        con: { tag: "DataAlt", con },
        binders: fields,
        body: this.matchGroup(subjects, group, column, fields, scope, fallback),
      };
    });

    return {
      tag: "Case",
      scrutinee: { tag: "Var", binder: subject },
      binder: mkBinder("c"),
      alts: [{ con: { tag: "DEFAULT" }, binders: [], body: defaultBody() }, ...alts],
    };
  }

  /** Inside one alternative, prepend the constructor's fields as new columns.
   *
   * The matched column is KEPT rather than dropped: a row that reached this
   * alternative through the fall-through path still has a variable pattern
   * there, and that variable has to go on binding the scrutinee. Its pattern
   * is only rewritten to a wildcard for the rows the alternative actually
   * discriminated on, which is also what stops `match` picking the same
   * column again and looping. */
  matchGroup(
    subjects: Binder[],
    group: MatchRow[],
    column: number,
    fields: Binder[],
    scope: Scope,
    fallback: CoreExpr,
  ): CoreExpr {
    const rows = group.map((row) => {
      const pattern = row.patterns[column]!;
      const matched = isRefutable(pattern);
      const sub: Pattern[] =
        pattern.tag === "con" && matched
          ? pattern.args
          : fields.map<Pattern>(() => ({ tag: "wild", span: pattern.span }));
      const columns = row.patterns.map((p, i) =>
        i === column && matched ? ({ tag: "wild", span: p.span } as Pattern) : p,
      );
      return { ...row, patterns: [...sub, ...columns] };
    });
    return this.match([...fields, ...subjects], rows, scope, fallback);
  }

  /** One equation's guards, `where` bindings and body. */
  guardedBody(row: MatchRow, scope: Scope, next: () => CoreExpr): CoreExpr {
    const [binds, inner] = this.localGroup(row.whereBindings, scope);
    const wrap = (body: CoreExpr): CoreExpr =>
      binds.reduceRight<CoreExpr>((b, bind) => ({ tag: "Let", bind, body: b }), body);
    const chain = row.guards.reduceRight<CoreExpr>(
      (rest, guard) =>
        guard.condition === undefined
          ? this.expr(guard.body, inner)
          : {
              tag: "Case",
              scrutinee: this.expr(guard.condition, inner),
              binder: mkBinder("g"),
              alts: [
                { con: { tag: "LitAlt", lit: int(0) }, binders: [], body: rest },
                { con: { tag: "DEFAULT" }, binders: [], body: this.expr(guard.body, inner) },
              ],
            },
      next(),
    );
    return wrap(chain);
  }

  /** A `let`/`where` group. Bindings with parameters become functions; the
   * group is `Rec` only when a right-hand side actually mentions the group. */
  localGroup(bindings: readonly LocalBinding[], scope: Scope): [CoreBind[], Scope] {
    if (bindings.length === 0) return [[], scope];
    const binders = bindings.map((b) => mkBinder(b.name));
    const inner = extend(scope, bindings.map((b, i) => [b.name, binders[i]!] as [string, Binder]));
    const rhss = bindings.map((binding) => {
      const params = binding.patterns.map((p) => mkBinder(patternName(p) ?? "arg"));
      const bodyScope = extend(
        inner,
        binding.patterns.flatMap((p, j) => {
          const name = patternName(p);
          return name ? [[name, params[j]!] as [string, Binder]] : [];
        }),
      );
      const row: MatchRow = {
        patterns: binding.patterns,
        guards: binding.guards ?? [{ body: binding.value }],
        whereBindings: binding.whereBindings ?? [],
      };
      const body =
        binding.patterns.every((p) => !isRefutable(p))
          ? this.guardedBody(row, bodyScope, () => raise())
          : this.match(params, [row], inner, raise());
      return mkLams(params, body);
    });
    const groupSet = new Set(binders);
    const recursive = rhss.some((rhs) => [...coreFreeVars(rhs)].some((v) => groupSet.has(v)));
    return recursive
      ? [[{ tag: "Rec", pairs: binders.map((b, i) => [b, rhss[i]!] as [Binder, CoreExpr]) }], inner]
      : [binders.map((b, i): CoreBind => ({ tag: "NonRec", binder: b, rhs: rhss[i]! })), inner];
  }
}

interface MatchRow {
  patterns: Pattern[];
  guards: Guard[];
  whereBindings: LocalBinding[];
  hasPatternGuards?: boolean;
}

const varOf = (binder: Binder): CoreExpr => ({ tag: "Var", binder });

/** Pattern-match failure. `RaiseDivZeroOp` is the only nullary raising primop
 * the JS backend implements; a real `PatternMatchFail` needs an exception
 * closure, which needs `Control.Exception`, which needs classes. */
const raise = (): CoreExpr => ({ tag: "Op", op: { tag: "StgPrimOp", op: "RaiseDivZeroOp" }, arity: 0, args: [] });

const extend = (scope: Scope, entries: Array<[string, Binder]>): Scope =>
  entries.length === 0 ? scope : new Map([...scope, ...entries]);

function flattenApp(e: Expr): [Expr, Expr[]] {
  const args: Expr[] = [];
  let head: Expr = e;
  while (head.tag === "app") {
    args.unshift(head.arg);
    head = head.fn;
  }
  return [head, args];
}

const isRefutable = (p: Pattern): boolean =>
  p.tag === "int" || p.tag === "string" || p.tag === "con" || p.tag === "record";

const patternName = (p: Pattern): string | undefined =>
  p.tag === "var" ? p.name : p.tag === "as" ? p.name : undefined;

const patternSpan = (p: Pattern): Span => p.span;
const patternConName = (p: Pattern): string => (p.tag === "con" ? p.name : p.tag === "record" ? p.name : "?");
const patternArity = (p: Pattern): number => (p.tag === "con" ? p.args.length : 0);
const patternKey = (p: Pattern): string =>
  p.tag === "int" ? `#${p.value}` : p.tag === "string" ? `s${p.value}` : `c${patternConName(p)}`;

function bindingsOf(subjects: Binder[], patterns: Pattern[]): Array<[string, Binder]> {
  const out: Array<[string, Binder]> = [];
  patterns.forEach((p, i) => {
    const name = patternName(p);
    if (name) out.push([name, subjects[i]!]);
  });
  return out;
}

export function desugarModule(module: Module, file = `${module.name}.hs`): DesugarResult {
  const d = new Desugarer(file);

  for (const decl of module.declarations) {
    if (decl.tag === "data") {
      decl.constructors.forEach((con, i) => {
        d.cons.set(con.name, mkDataCon(con.name, i + 1, con.arity, decl.name));
      });
    } else if (decl.tag === "class") {
      for (const member of decl.members) if ("name" in member) d.classMethods.add(member.name);
      d.diagnostics.push(
        error(
          "GHCTS-DESUGAR",
          `class \`${decl.name}\`: dictionary elaboration is not implemented yet`,
          file,
          decl.span.line,
          decl.span.column,
        ),
      );
    } else if (decl.tag === "instance") {
      d.diagnostics.push(
        error(
          "GHCTS-DESUGAR",
          `instance \`${decl.head}\`: dictionary elaboration is not implemented yet`,
          file,
          decl.span.line,
          decl.span.column,
        ),
      );
    }
  }

  const values = module.declarations.filter(isValue);
  const foreigns = module.declarations.filter(isForeign);
  for (const decl of [...values, ...foreigns]) d.top.set(decl.name, mkBinder(decl.name, { exported: true }));

  const binds: CoreBind[] = [];

  for (const decl of foreigns) {
    // A foreign import is a saturated foreign call under enough lambdas to
    // consume its declared arguments; `arity` comes from the signature's
    // top-level arrows.
    const params = Array.from({ length: decl.arity }, (_, i) => mkBinder(`ffi${i}`));
    const op: StgOp = {
      tag: "StgFCallOp",
      target: { javascript: decl.javascript, safety: "unsafe" },
    };
    binds.push({
      tag: "NonRec",
      binder: d.top.get(decl.name)!,
      rhs: mkLams(params, { tag: "Op", op, arity: decl.arity, args: params.map(varOf) }),
    });
  }

  for (const decl of values) {
    const arity = decl.equations[0]?.patterns.length ?? 0;
    const params = Array.from({ length: arity }, (_, i) => mkBinder(`a${i}`));
    const rows: MatchRow[] = decl.equations.map((eq) => ({
      patterns: eq.patterns,
      guards: eq.guards,
      whereBindings: eq.whereBindings,
    }));
    const body = d.match(params, rows, d.top, raise());
    binds.push({ tag: "NonRec", binder: d.top.get(decl.name)!, rhs: mkLams(params, body) });
  }

  return {
    program: { name: module.name, binds, dataCons: [...d.cons.values()] },
    diagnostics: d.diagnostics,
  };
}

const isValue = (d: Declaration): d is Extract<Declaration, { tag: "value" }> => d.tag === "value";
const isForeign = (d: Declaration): d is Extract<Declaration, { tag: "foreign" }> => d.tag === "foreign";
