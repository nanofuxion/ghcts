/** Surface AST (`src/ast.ts`) to Core (`src/core.ts`).
 *
 * Scope. This pass targets class-free Haskell, which is what it now receives:
 * `src/elaborate.ts` runs first and has already turned classes, instances and
 * constrained call sites into data types, values and explicit dictionary
 * arguments. Anything still unsupported here - `do` notation, list
 * comprehensions, records - produces a diagnostic and an expression that
 * raises, so one unsupported construct never silently corrupts the rest of
 * the module.
 *
 * Representation, now that dictionaries exist:
 *
 *   - an integer literal is an `Int#` ONLY under `fromInteger`. `Int` itself
 *     is the ordinary boxed `I Int#` the Prelude declares, so arithmetic goes
 *     through `$fNumInt` and an `Int` argument can be a thunk again.
 *   - `Bool` is an ordinary two-constructor data type. The comparison primops
 *     still yield a 0/1 machine value, so each one is wrapped here into a
 *     real `False`/`True` - GHC's `tagToEnum# (<# a b)`, applied once, at the
 *     only place the machine value is visible.
 *   - the `prim*` names below are the only primitives. They are typed over the
 *     unboxed `IntPrim`/`CharPrim`, never over `Int`, so no builtin can be
 *     mistaken for a class method.
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

/** Primitive name to primop. `bool` marks the ones whose 0/1 machine result
 * is wrapped into a real `Bool` constructor. Only ops the JS backend
 * implements appear here (see src/stg-js/prim.ts). */
interface Prim {
  op: string | StgOp;
  arity: number;
  bool?: true;
}

const primOps: Record<string, Prim> = {
  primIntAdd: { op: "IntAddOp", arity: 2 },
  primIntSub: { op: "IntSubOp", arity: 2 },
  primIntMul: { op: "IntMulOp", arity: 2 },
  primIntQuot: { op: "IntQuotOp", arity: 2 },
  primIntRem: { op: "IntRemOp", arity: 2 },
  primIntNeg: { op: "IntNegOp", arity: 1 },
  primIntEq: { op: "IntEqOp", arity: 2, bool: true },
  primIntNe: { op: "IntNeOp", arity: 2, bool: true },
  primIntLt: { op: "IntLtOp", arity: 2, bool: true },
  primIntLe: { op: "IntLeOp", arity: 2, bool: true },
  primIntGt: { op: "IntGtOp", arity: 2, bool: true },
  primIntGe: { op: "IntGeOp", arity: 2, bool: true },
  primChr: { op: "ChrOp", arity: 1 },
  primCharOrd: { op: "OrdOp", arity: 1 },
  primCharEq: { op: "CharEqOp", arity: 2, bool: true },
  primCharLt: { op: "CharLtOp", arity: 2, bool: true },
  primDoubleAdd: { op: "DoubleAddOp", arity: 2 },
  primDoubleSub: { op: "DoubleSubOp", arity: 2 },
  primDoubleMul: { op: "DoubleMulOp", arity: 2 },
  primDoubleDiv: { op: "DoubleDivOp", arity: 2 },
  primDoubleNeg: { op: "DoubleNegOp", arity: 1 },
  primDoubleAbs: { op: "DoubleFabsOp", arity: 1 },
  primDoubleEq: { op: "DoubleEqOp", arity: 2, bool: true },
  primDoubleLt: { op: "DoubleLtOp", arity: 2, bool: true },
  primDoubleLe: { op: "DoubleLeOp", arity: 2, bool: true },
  primDoubleGt: { op: "DoubleGtOp", arity: 2, bool: true },
  primDoubleGe: { op: "DoubleGeOp", arity: 2, bool: true },
  primDoubleSqrt: { op: "DoubleSqrtOp", arity: 1 },
  primDoubleLog: { op: "DoubleLogOp", arity: 1 },
  primDoubleExp: { op: "DoubleExpOp", arity: 1 },
  primDoublePower: { op: "DoublePowerOp", arity: 2 },
  primIntToDouble: { op: "IntToDoubleOp", arity: 1 },
  // Truncates towards zero, as GHC's `double2Int#` does.
  primDoubleToInt: { op: "DoubleToIntOp", arity: 1 },
  // `IORef` is GHC's `MutVar#`: a one-field JS object whose read and write are
  // a property read and a property write (rts/js/mem.js). Writing this in
  // Haskell instead would be a slower cell with identical semantics.
  primNewMutVar: { op: "NewMutVarOp", arity: 1 },
  primReadMutVar: { op: "ReadMutVarOp", arity: 1 },
  primWriteMutVar: { op: "WriteMutVarOp", arity: 2 },
  // `MVar` is NOT a cell: `takeMVar` on an empty one blocks the *thread*, and
  // only the RTS can do that (rts/js/thread.js). These map onto the same
  // primops GHC's `Control.Concurrent.MVar` uses, so a take that must block
  // does block instead of silently reading a hole.
  //
  // `NewMVarOp` ignores its argument slot; the argument is the state token, and
  // it is there only so the call is not a CAF - a nullary primop would be one
  // top-level `MVar` shared by every `newEmptyMVar` in the program.
  primNewMVar: { op: "NewMVarOp", arity: 1 },
  primTakeMVar: { op: "TakeMVarOp", arity: 1 },
  primPutMVar: { op: "PutMVarOp", arity: 2 },
  primReadMVar: { op: "ReadMVarOp", arity: 1 },
  primTryPutMVar: { op: "TryPutMVarOp", arity: 2, bool: true },
  primIsEmptyMVar: { op: "IsEmptyMVarOp", arity: 1, bool: true },
  primFork: { op: "ForkOp", arity: 1 },
  primDelay: { op: "DelayOp", arity: 1 },
};

/** What a name resolves to. Locals shadow top levels, which shadow
 * constructors, which shadow primops. */
type Scope = ReadonlyMap<string, Binder>;

class Desugarer {
  readonly diagnostics: Diagnostic[] = [];
  readonly cons = new Map<string, DataCon>();
  /** How many constructors each data type has, so an alternative list that
   * covers all of them can drop its unreachable DEFAULT. Codegen emits no tag
   * test for a single-constructor type, and would then see two defaults. */
  readonly conCount = new Map<string, number>([["[]", 2]]);
  readonly top = new Map<string, Binder>();
  /** Names introduced by a `class` declaration, so a use of one can say
   * "dictionary elaboration" instead of "not in scope". */
  readonly classMethods = new Set<string>();
  /** Foreign imports, by name, so a *saturated* call becomes the foreign call
   * itself rather than a call to the wrapper closure.
   *
   * This is not an optimisation. A `foreign import javascript unsafe` consumes
   * machine values, and the wrapper is an ordinary Haskell function whose
   * arguments are therefore thunks: `len (hello 0)` handed the JS function a
   * thunk object instead of the string. Inlining the call puts the argument in
   * a primop's strict position, where `src/core-to-stg.ts` binds it with a
   * `case` - which is exactly what GHC does by inlining the same wrapper. */
  readonly foreignOps = new Map<string, Prim>();

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
      case "double":
        return { tag: "Lit", lit: { tag: "LitDouble", value: e.value } };
      case "char":
        return { tag: "Con", con: this.lookupCon("C", 1), args: [{ tag: "Lit", lit: { tag: "LitChar", value: e.value } }] };
      case "string":
        // A `String` is `[Char]`, so a literal is the list it denotes. The
        // backend's `LitString` is an address, which is a different type.
        return [...e.value].reduceRight<CoreExpr>(
          (tail, character) => ({
            tag: "Con",
            con: this.lookupCon(":", 2),
            args: [
              { tag: "Con", con: this.lookupCon("C", 1), args: [{ tag: "Lit", lit: { tag: "LitChar", value: character } }] },
              tail,
            ],
          }),
          { tag: "Con", con: this.lookupCon("[]", 0), args: [] },
        );
      case "unit":
        return { tag: "Lit", lit: int(0) };
      // The type has already done its work in `src/elaborate.ts`, and STG is
      // type-erased, so the node is simply the expression it wraps.
      case "annot":
        return this.expr(e.expr, scope);
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
      case "if":
        return this.boolCase(
          this.expr(e.condition, scope),
          () => this.expr(e.thenBranch, scope),
          () => this.expr(e.elseBranch, scope),
        );
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

  saturateOp(prim: Prim, args: CoreExpr[]): CoreExpr {
    const op: StgOp = typeof prim.op === "string" ? { tag: "StgPrimOp", op: prim.op } : prim.op;
    const call = (as: CoreExpr[]): CoreExpr => {
      const raw: CoreExpr = { tag: "Op", op, arity: prim.arity, args: as };
      // GHC's `tagToEnum#`: the machine comparison yields 0 or 1, and the
      // whole rest of the compiler only ever sees a real constructor.
      return prim.bool ? this.boolCase(raw, () => this.con("True"), () => this.con("False"), true) : raw;
    };
    if (args.length >= prim.arity) return mkApps(call(args.slice(0, prim.arity)), args.slice(prim.arity));
    const extra = Array.from({ length: prim.arity - args.length }, (_, i) => mkBinder(`p${i}`));
    return mkLams(extra, call([...args, ...extra.map(varOf)]));
  }

  con(name: string): CoreExpr {
    return { tag: "Con", con: this.lookupCon(name, 0), args: [] };
  }

  /** Scrutinise a condition. `primitive` says whether it is still the 0/1
   * machine result of a comparison primop, or already a real `Bool`. */
  boolCase(scrutinee: CoreExpr, whenTrue: () => CoreExpr, whenFalse: () => CoreExpr, primitive = false): CoreExpr {
    return {
      tag: "Case",
      scrutinee,
      binder: mkBinder("cond"),
      alts: primitive
        ? [
            { con: { tag: "LitAlt", lit: int(0) }, binders: [], body: whenFalse() },
            { con: { tag: "DEFAULT" }, binders: [], body: whenTrue() },
          ]
        : [
            { con: { tag: "DataAlt", con: this.lookupCon("False", 0) }, binders: [], body: whenFalse() },
            { con: { tag: "DataAlt", con: this.lookupCon("True", 0) }, binders: [], body: whenTrue() },
          ],
    };
  }

  application(head: Expr, args: Expr[], scope: Scope): CoreExpr {
    const lowered = args.map((arg) => this.expr(arg, scope));
    if (head.tag === "var") {
      const shortCut = this.overloadedLit(head.name, lowered);
      if (shortCut) return shortCut;
    }
    if (head.tag === "var") {
      // A foreign import IS in scope (it is a top-level binding), so this test
      // is that the name still means that binding and has not been shadowed.
      const foreign = this.foreignOps.get(head.name);
      if (foreign && scope.get(head.name) === this.top.get(head.name) && lowered.length >= foreign.arity)
        return this.saturateOp(foreign, lowered);
    }
    if (head.tag === "var" && !scope.has(head.name)) {
      const con = this.cons.get(head.name);
      if (con) return this.saturateCon(con, lowered);
      const prim = primOps[head.name];
      if (prim) return this.saturateOp(prim, lowered);
    }
    return mkApps(this.expr(head, scope), lowered);
  }

  /** GHC's `dsOverLit` short-cut: an overloaded literal whose type is already
   * known is built directly rather than left as a `fromInteger` call, so
   * `5 :: Int` is `I# 5#` and not a thunk that computes it. The literal is
   * then a constructor application with an atomic argument, which the backend
   * allocates statically - and for `Int`, whose one field is unboxable, that
   * static allocation IS the number.
   *
   * Elaboration has already picked the dictionary, and `$fNumInt` names the
   * `Int` instance the way GHC's `intDataCon` names its constructor, so the
   * type is recoverable here without a type checker. */
  overloadedLit(head: string, args: CoreExpr[]): CoreExpr | undefined {
    if (args.length !== 2) return undefined;
    const [dict, lit] = args;
    if (dict.tag !== "Var") return undefined;
    // Binder identity, not just the name: only the module's own `$fNumInt`
    // pins the type down to `Int`.
    if (head === "fromInteger" && dict.binder === this.top.get("$fNumInt")) {
      if (lit.tag !== "Lit" || lit.lit.tag !== "LitNumInt") return undefined;
      return { tag: "Con", con: this.lookupCon("I", 1), args: [lit] };
    }
    if (head === "fromRational" && dict.binder === this.top.get("$fFractionalDouble")) {
      if (lit.tag !== "Lit" || lit.lit.tag !== "LitDouble") return undefined;
      return { tag: "Con", con: this.lookupCon("DoubleBox", 1), args: [lit] };
    }
    return undefined;
  }

  /** `case` and `\case` alternatives; guards inside an alternative fall
   * through to the next alternative when none succeeds. */
  alternatives(scrutinee: CoreExpr, alts: CaseAlternative[], scope: Scope, span: Span): CoreExpr {
    const subject = scrutinee.tag === "Var" ? scrutinee.binder : mkBinder("scrut");
    const rows = alts.map((alt) => ({
      patterns: [alt.pattern],
      guards: alt.guard ? [{ condition: alt.guard, body: alt.body }] : [{ body: alt.body }],
      whereBindings: [] as LocalBinding[],
      hasPatternGuards: (alt.patternGuards?.length ?? 0) > 0,
    }));
    for (const row of rows) if (row.hasPatternGuards) this.fail("pattern guards", span);
    // Naming an already-named scrutinee would add a `case` that enters it a
    // second time; that is wrong for an unboxed scrutinee and pointless for
    // any other.
    if (scrutinee.tag === "Var") return this.match([subject], rows, scope, raise());
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

    const column = subjects.findIndex((_, i) => rows.some((row) => isRefutable(row.patterns[i])));
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
      if (pattern.tag === "char") {
        return {
          con: { tag: "LitAlt", lit: { tag: "LitChar", value: pattern.value } },
          binders: [],
          body: this.matchGroup(subjects, group, column, [], scope, fallback),
        };
      }
      if (pattern.tag === "int") {
        return {
          con: { tag: "LitAlt", lit: int(pattern.value) },
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

    const typeName = alts[0]?.con.tag === "DataAlt" ? alts[0].con.con.typeName : undefined;
    // Rows whose pattern here is a variable were merged into every
    // constructor group above, so once every constructor has an alternative
    // the DEFAULT one is unreachable.
    const exhaustive = typeName !== undefined && alts.length === this.conCount.get(typeName);
    return {
      tag: "Case",
      scrutinee: { tag: "Var", binder: subject },
      binder: mkBinder("c"),
      alts: exhaustive ? alts : [{ con: { tag: "DEFAULT" }, binders: [], body: defaultBody() }, ...alts],
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
          : this.boolCase(
              this.expr(guard.condition, inner),
              () => this.expr(guard.body, inner),
              () => rest,
            ),
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

/** A missing pattern means the equation has fewer arguments than its
 * siblings. That is an arity error, and the elaborator already reports it as
 * one; crashing here would replace a good diagnostic with a stack trace, so
 * an absent column is treated as irrefutable and the build carries on to
 * report everything else it finds. */
const isRefutable = (p: Pattern | undefined): boolean =>
  p !== undefined &&
  (p.tag === "int" || p.tag === "string" || p.tag === "char" || p.tag === "con" || p.tag === "record");

const patternName = (p: Pattern): string | undefined =>
  p.tag === "var" ? p.name : p.tag === "as" ? p.name : undefined;

const patternSpan = (p: Pattern): Span => p.span;
const patternConName = (p: Pattern): string => (p.tag === "con" ? p.name : p.tag === "record" ? p.name : "?");
const patternArity = (p: Pattern): number => (p.tag === "con" ? p.args.length : 0);
const patternKey = (p: Pattern): string =>
  p.tag === "int" ? `#${p.value}` : p.tag === "string" ? `s${p.value}` : p.tag === "char" ? `q${p.value}` : `c${patternConName(p)}`;

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
      d.conCount.set(decl.name, decl.constructors.length);
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
    // top-level arrows. The wrapper is still emitted for an unsaturated use;
    // a saturated call goes straight to the foreign call (see `foreignOps`).
    const params = Array.from({ length: decl.arity }, (_, i) => mkBinder(`ffi${i}`));
    const op: StgOp = {
      tag: "StgFCallOp",
      target: { javascript: decl.javascript, safety: "unsafe" },
    };
    d.foreignOps.set(decl.name, { op, arity: decl.arity });
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
