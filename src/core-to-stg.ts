/** Core (`src/core.ts`) to STG (`src/stg.ts`), after
 * `references/ghc/compiler/GHC/CoreToStg.hs` and `CoreToStg/Prep.hs`.
 *
 * Everything here exists to establish the two invariants `src/stg.ts`'s
 * header states, because codegen assumes them rather than checking them:
 *
 *   1. Every application is saturated and every argument is atomic. Core
 *     already guarantees saturation for `Con` and `Op` (the desugarer
 *     eta-expands); this pass supplies atomicity by ANF-ising - each
 *     non-atomic argument is floated out into a binding and replaced by the
 *     variable naming it. Unknown-arity calls stay as `StgApp` and are what
 *     `h$ap_gen` is for.
 *   2. Every closure lists its free variables and its update flag. Free
 *     variables are computed on the emitted STG, after ANF, so a variable
 *     introduced by a floated binding is counted; the update flag is decided
 *     as described at `mkClosure` below.
 */
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "./core.js";
import type {
  AltType,
  Binder,
  DataCon,
  StgAlt,
  StgArg,
  StgBinding,
  StgExpr,
  StgModule,
  StgRhs,
} from "./stg.js";
import { UpdateFlag, litArg, mkBinder, varArg } from "./stg.js";

/** Either a `let` (a real allocation) or a `case` (evaluate now), the two
 * ways CorePrep floats a non-atomic subexpression out of an argument
 * position. Applied outside-in in the order they were produced. */
type Float = (body: StgExpr) => StgExpr;

class Converter {
  /**
   * @param topLevel every top-level binder. These are never free variables of
   * a closure: codegen resolves them to module-level symbols, not payload
   * slots.
   * @param topLevelThunks the nullary subset - CAFs. A reference to one is a
   * pointer to an unentered thunk, so it has to be forced before it can be
   * used as a value (see `atom`).
   */
  constructor(
    private readonly topLevel: ReadonlySet<Binder>,
    private readonly topLevelThunks: ReadonlySet<Binder>,
  ) {}

  /** Peel the leading lambdas, so a right-hand side becomes a function
   * closure rather than a thunk that returns one. */
  rhs(expr: CoreExpr): StgRhs {
    const args: Binder[] = [];
    let body = expr;
    while (body.tag === "Lam") {
      args.push(body.binder);
      body = body.body;
    }
    const stgBody = this.expr(body);

    // A constructor application with atomic arguments needs no entry code at
    // all: codegen can allocate it directly. Anything that had to be floated
    // stays a thunk, since an StgRhsCon has nowhere to put the bindings.
    if (args.length === 0 && stgBody.tag === "StgConApp") {
      return { tag: "StgRhsCon", con: stgBody.con, args: stgBody.args };
    }
    return this.mkClosure(args, stgBody);
  }

  /** The update-flag decision, in one place.
   *
   *   - a closure with arguments is a function: entering it must NOT
   *     overwrite it, or the second call would find a value where it expects
   *     code. ReEntrant.
   *   - a thunk that some other code can reach more than once has to be
   *     overwritten by its value on first entry, or the work is repeated and,
   *     worse, an update frame is missing where the RTS expects one.
   *     Updatable. This covers source-level `let`s and top-level CAFs.
   *
   * SingleEntry is deliberately never emitted. It would be the right flag for
   * a thunk this pass invented to make one argument atomic - substituted for
   * exactly one occurrence, so the update is provably wasted - but `atom`
   * floats arguments with `case` instead, so no such thunk is ever built.
   * Guessing SingleEntry anywhere else risks losing an update frame the RTS
   * expects, which fails silently rather than loudly. */
  mkClosure(args: Binder[], body: StgExpr): StgRhs {
    const update = args.length > 0 ? UpdateFlag.ReEntrant : UpdateFlag.Updatable;
    const bound = new Set(args);
    const freeVars = [...freeVarsOf(body)].filter((v) => !bound.has(v) && !this.topLevel.has(v));
    return { tag: "StgRhsClosure", freeVars, update, args, body };
  }

  expr(e: CoreExpr): StgExpr {
    switch (e.tag) {
      case "Var":
        return { tag: "StgApp", fn: e.binder, args: [] };
      case "Lit":
        return { tag: "StgLit", lit: e.lit };
      case "Con": {
        const floats: Float[] = [];
        const args = e.args.map((arg) => this.atom(arg, floats, false));
        return wrap(floats, { tag: "StgConApp", con: e.con, args });
      }
      case "Op": {
        const floats: Float[] = [];
        // A primop consumes machine values, so its arguments are evaluated
        // here rather than thunked.
        const args = e.args.map((arg) => this.atom(arg, floats, true));
        return wrap(floats, { tag: "StgOpApp", op: e.op, args });
      }
      case "Lam": {
        // A lambda in a non-right-hand-side position still has to become a
        // closure before anything can refer to it.
        const binder = mkBinder("lam");
        return {
          tag: "StgLet",
          binding: { tag: "StgNonRec", binder, rhs: this.rhs(e) },
          body: { tag: "StgApp", fn: binder, args: [] },
        };
      }
      case "Let": {
        // A non-recursive `let` whose right-hand side is not a function is
        // evaluated here rather than thunked - see `atom` for why this
        // language is call-by-value.
        if (e.bind.tag === "NonRec" && e.bind.rhs.tag !== "Lam") {
          return {
            tag: "StgCase",
            scrutinee: this.expr(e.bind.rhs),
            binder: e.bind.binder,
            altType: altTypeOfExpr(e.bind.rhs),
            alts: [{ con: { tag: "DEFAULT" }, binders: [], body: this.expr(e.body) }],
          };
        }
        return { tag: "StgLet", binding: this.bind(e.bind), body: this.expr(e.body) };
      }
      case "Case": {
        const alts = e.alts.map((alt) => this.alt(alt));
        return {
          tag: "StgCase",
          scrutinee: this.expr(e.scrutinee),
          binder: e.binder,
          altType: altTypeOf(e.alts, e.scrutinee),
          alts,
        };
      }
      case "App": {
        const [head, args] = flatten(e);
        const floats: Float[] = [];
        const atoms = args.map((arg) => this.atom(arg, floats, false));
        if (head.tag === "Var") {
          return wrap(floats, { tag: "StgApp", fn: head.binder, args: atoms });
        }
        // The head is itself a computation; name it, then apply the name.
        const headFloats: Float[] = [];
        const headAtom = this.atom(head, headFloats, true);
        if (headAtom.tag !== "StgVarArg") throw new Error("coreToStg: literal in function position");
        return wrap([...headFloats, ...floats], { tag: "StgApp", fn: headAtom.id, args: atoms });
      }
    }
  }

  alt(alt: CoreAlt): StgAlt {
    return { con: alt.con, binders: alt.binders, body: this.expr(alt.body) };
  }

  bind(bind: CoreBind): StgBinding {
    return bind.tag === "NonRec"
      ? { tag: "StgNonRec", binder: bind.binder, rhs: this.rhs(bind.rhs) }
      : { tag: "StgRec", pairs: bind.pairs.map(([b, rhs]) => [b, this.rhs(rhs)] as [Binder, StgRhs]) };
  }

  /** Make one subexpression atomic, recording how to re-attach it.
   *
   * `case` or `let` is a representation question, and dictionaries changed the
   * answer. It used to be `case` unconditionally: with no `Num` dictionary an
   * `Int` WAS an `Int#`, so a thunk in a constructor field or a function
   * argument would have been added or compared as a closure object, silently.
   * Now `Int` is the boxed `I Int#`, so those positions hold pointers and a
   * thunk belongs there - that is where laziness lives, and a self-referential
   * dictionary such as `$fEqInt = MkDict_Eq ... ($dmEq$/= $fEqInt)` only
   * terminates because the field is one.
   *
   * What must still be evaluated here:
   *
   *   - `strict` positions, which is a primop's arguments and a call's head.
   *     A primop consumes a machine value; entering a thunk there is not a
   *     representation the backend has.
   *   - a primop result or a literal, which IS a machine value, and cannot be
   *     the payload of a thunk.
   *   - a CAF reference, which is a pointer to an unentered thunk.
   *
   * The thunks this pass now builds are Updatable rather than SingleEntry: the
   * argument they stand for can be duplicated by the callee, so the update is
   * not provably wasted, and a missing update frame fails silently. */
  atom(e: CoreExpr, floats: Float[], strict: boolean): StgArg {
    if (e.tag === "Lit") return litArg(e.lit);
    if (e.tag === "Var" && !this.topLevelThunks.has(e.binder)) return varArg(e.binder);
    const binder = mkBinder("t");
    const value = this.expr(e);
    const evaluate = strict || e.tag === "Op" || e.tag === "Var";
    floats.push(
      evaluate
        ? (body) => ({
            tag: "StgCase",
            scrutinee: value,
            binder,
            altType: altTypeOfExpr(e),
            alts: [{ con: { tag: "DEFAULT" }, binders: [], body }],
          })
        : (body) => ({
            tag: "StgLet",
            // `rhs` rather than `mkClosure`: a constructor application with
            // atomic arguments is allocated directly, exactly as it would be
            // in a source-level `let`, instead of behind a thunk.
            binding: { tag: "StgNonRec", binder, rhs: this.rhs(e) },
            body,
          }),
    );
    return varArg(binder);
  }
}

const wrap = (floats: Float[], body: StgExpr): StgExpr =>
  floats.reduceRight<StgExpr>((acc, float) => float(acc), body);

function flatten(e: CoreExpr): [CoreExpr, CoreExpr[]] {
  const args: CoreExpr[] = [];
  let head = e;
  while (head.tag === "App") {
    args.unshift(head.arg);
    head = head.fn;
  }
  return [head, args];
}

/** What codegen dispatches on. A DataAlt anywhere means a tag test; a LitAlt
 * means a primitive comparison; only DEFAULT means nothing to test. */
function altTypeOf(alts: readonly CoreAlt[], scrutinee: CoreExpr): AltType {
  for (const alt of alts) {
    if (alt.con.tag === "DataAlt") return { tag: "AlgAlt", typeName: alt.con.con.typeName };
    if (alt.con.tag === "LitAlt") return { tag: "PrimAlt" };
  }
  // All-DEFAULT: the scrutinee is the only evidence left of whether the bound
  // value is a machine value or a pointer.
  return altTypeOfExpr(scrutinee);
}

/** The alt type for a case this pass invented around a floated argument.
 * A primop result is a primitive value; anything else is a pointer whose
 * shape is unknown here. */
const altTypeOfExpr = (e: CoreExpr): AltType =>
  e.tag === "Op" || e.tag === "Lit" ? { tag: "PrimAlt" } : { tag: "PolyAlt" };

function freeVarsOf(expr: StgExpr): Set<Binder> {
  const free = new Set<Binder>();
  const arg = (a: StgArg, scope: Set<Binder>): void => {
    if (a.tag === "StgVarArg" && !scope.has(a.id)) free.add(a.id);
  };
  const rhsVars = (r: StgRhs, scope: Set<Binder>): void => {
    if (r.tag === "StgRhsCon") {
      for (const a of r.args) arg(a, scope);
      return;
    }
    // A nested closure's own free variables are free in the enclosing one
    // too, minus what it binds itself.
    go(r.body, new Set([...scope, ...r.args]));
  };
  const go = (e: StgExpr, scope: Set<Binder>): void => {
    switch (e.tag) {
      case "StgApp":
        if (!scope.has(e.fn)) free.add(e.fn);
        for (const a of e.args) arg(a, scope);
        return;
      case "StgLit":
        return;
      case "StgConApp":
      case "StgOpApp":
        for (const a of e.args) arg(a, scope);
        return;
      case "StgCase": {
        go(e.scrutinee, scope);
        const inner = new Set([...scope, e.binder]);
        for (const alt of e.alts) go(alt.body, new Set([...inner, ...alt.binders]));
        return;
      }
      case "StgLet":
      case "StgLetNoEscape": {
        const bound =
          e.binding.tag === "StgNonRec" ? [e.binding.binder] : e.binding.pairs.map(([b]) => b);
        const rhsScope = e.binding.tag === "StgNonRec" ? scope : new Set([...scope, ...bound]);
        if (e.binding.tag === "StgNonRec") rhsVars(e.binding.rhs, rhsScope);
        else for (const [, r] of e.binding.pairs) rhsVars(r, rhsScope);
        go(e.body, new Set([...scope, ...bound]));
        return;
      }
    }
  };
  go(expr, new Set());
  return free;
}

/** The top-level binding GHC emits for a data constructor's worker; codegen
 * turns it into the `..._con_e` entry function allocated closures point at. */
const conWorker = (con: DataCon): StgBinding => ({
  tag: "StgNonRec",
  binder: { name: con.name, unique: con.unique, exported: true },
  rhs: { tag: "StgRhsCon", con, args: [] },
});

export function coreToStg(program: CoreProgram): StgModule {
  const topLevel = new Set<Binder>();
  const topLevelThunks = new Set<Binder>();
  for (const bind of program.binds) {
    if (bind.tag === "NonRec") {
      topLevel.add(bind.binder);
      if (bind.rhs.tag !== "Lam") topLevelThunks.add(bind.binder);
    } else {
      for (const [b, rhs] of bind.pairs) {
        topLevel.add(b);
        if (rhs.tag !== "Lam") topLevelThunks.add(b);
      }
    }
  }
  const converter = new Converter(topLevel, topLevelThunks);
  return {
    name: program.name,
    bindings: [
      ...program.dataCons.map(conWorker),
      ...program.binds.map((bind) => converter.bind(bind)),
    ],
  };
}
