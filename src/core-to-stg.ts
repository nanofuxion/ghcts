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
import { occInfo } from "./core-opt/simplify.js";
import { UpdateFlag, isUnboxedTupleCon, litArg, mkBinder, varArg } from "./stg.js";
import { isAlwaysSinkableCon } from "./stg-js/sinker.js";

/** Either a `let` (a real allocation) or a `case` (evaluate now), the two
 * ways CorePrep floats a non-atomic subexpression out of an argument
 * position. Applied outside-in in the order they were produced. */
type Float = (body: StgExpr) => StgExpr;

class Converter {
  /** Bindings this pass lifted out of an argument position and up to the top
   * level - CorePrep's float. See `floatToTop`. */
  readonly floated: StgBinding[] = [];

  /** Whether a float from here would reach the top level. CorePrep's floats do
   * not escape a lambda or a `case` alternative, so only a top-level
   * right-hand side that is not a function produces any. GHC's own output is
   * what pins this down: `ten = 5 + 5` floats its two `I# 5`s away, while
   * `big n = n > 10` keeps `I# 10` as a local `let` - and GHC's `big` still
   * carries the empty `var` that leaves behind. */
  private toTop = false;

  /**
   * @param topLevel every top-level binder, which `floatToTop` adds to. These
   * are never free variables of a closure: codegen resolves them to
   * module-level symbols, not payload slots.
   */
  constructor(private readonly topLevel: Set<Binder>) {}

  private under<A>(toTop: boolean, f: () => A): A {
    const saved = this.toTop;
    this.toTop = toTop;
    try {
      return f();
    } finally {
      this.toTop = saved;
    }
  }

  /** CorePrep floats a constructor application whose arguments are all
   * literals to the top level, where `GHC.StgToJS.Sinker` unfloats most of
   * them again into the place they were used.
   *
   * ghcts has no CorePrep, so this floats only the shape the Sinker's
   * `alwaysSinkable` is certain to take back: nothing new can be left standing
   * at the top level, and the pair's whole visible effect is that the argument
   * is emitted as its literal instead of through a `var` that names it.
   * Widening it would need a pass that can decide what the rest should cost. */
  floatToTop(binder: Binder, rhs: StgRhs): boolean {
    if (!this.toTop || !isAlwaysSinkableCon(rhs)) return false;
    this.floated.push({ tag: "StgNonRec", binder, rhs });
    // A top-level binder is a module-level symbol, never a closure payload
    // slot, so every enclosing `mkClosure` has to stop counting it free and
    // `liveVars` has to stop putting it in a payload - which is what
    // `exported`, GHC's `isGlobalId`, says. `internal` is the other half of
    // GHC's name: no module owns it, which is how the Sinker recognises it.
    this.topLevel.add(binder);
    binder.exported = true;
    binder.internal = true;
    return true;
  }

  /** Peel the leading lambdas, so a right-hand side becomes a function
   * closure rather than a thunk that returns one. */
  rhs(expr: CoreExpr, owner?: Binder): StgRhs {
    const args: Binder[] = [];
    let body = expr;
    while (body.tag === "Lam") {
      args.push(body.binder);
      body = body.body;
    }
    const stgBody = this.under(this.toTop && args.length === 0, () => this.expr(body));

    // A constructor application with atomic arguments needs no entry code at
    // all: codegen can allocate it directly. Anything that had to be floated
    // stays a thunk, since an StgRhsCon has nowhere to put the bindings.
    if (args.length === 0 && stgBody.tag === "StgConApp") {
      // An unboxed tuple has no heap representation, so there is nothing to
      // bind here; reaching this means a caller put one in a lazy position
      // (an argument or a constructor field), which is exactly what GHC's
      // levity rules forbid. Failing loudly beats allocating a closure the
      // backend will never be able to enter.
      if (isUnboxedTupleCon(stgBody.con)) throw new Error("coreToStg: unboxed tuple in a lazy position");
      // A constructor binding is a value, not a thunk, so every use of it is
      // already in WHNF. This is the easy half of GHC's InferTags, and
      // without it `genApp` sends each use through `h$ap_0_0_fast` to enter a
      // closure that was never going to do any work.
      if (owner) owner.evaluated = true;
      return { tag: "StgRhsCon", con: stgBody.con, args: stgBody.args };
    }
    if (owner && args.length > 0) {
      owner.funRepArity = args.length;
      // A function closure is not a thunk: GHC's `isStrictId` is true of
      // top-level Funs because they are already evaluated as functions.
      // Without this bit, genApp never takes the saturated/oversaturated
      // jump and every call pays `h$ap_N_M_fast`.
      owner.strict = true;
      // A deliberately narrow seed set for native-region lowering: closed,
      // monomorphic primitive workers.  Later passes may reject this; no
      // caller may treat the bit as permission to skip the ABI wrapper.
      owner.nativeEligible =
        stgBody.tag === "StgOpApp" &&
        stgBody.op.tag === "StgPrimOp" &&
        args.every((a) => (a.arity ?? 1) === 1) &&
        freeVarsOf(stgBody).size === 0;
      if (owner.nativeEligible && stgBody.tag === "StgOpApp") {
        const op = stgBody.op.tag === "StgPrimOp" ? stgBody.op.op : "";
        owner.nativeResultRep =
          op.startsWith("Int") || op.startsWith("Word") || op.startsWith("Char") ? "i32" :
          op.startsWith("Double") || op.startsWith("Float") ? "f64" :
          op.includes("Eq") || op.includes("Gt") || op.includes("Ge") || op.includes("Lt") || op.includes("Le") ? "bool" :
          undefined;
        owner.nativeEligible = owner.nativeResultRep !== undefined;
        if (owner.nativeEligible) {
          owner.strict = true;
          // Primitive workers consume their arguments strictly. Preserve this
          // demand fact for the native-region pass instead of rediscovering it
          // from the lowered expression later.
          for (const arg of stgBody.args) {
            if (arg.tag === "StgVarArg") arg.id.strict = true;
          }
        }
      }
    }
    return this.mkClosure(args, stgBody, owner);
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
   * SingleEntry is emitted only where the binding's own body proves it: the
   * thunk is read exactly once, outside any lambda and outside any recursive
   * group, so no second entry can exist to find the update missing. That is
   * the occurrence analysis behind GHC's update flags, and each thunk it
   * applies to saves an update frame push and a black-hole write. Guessing it
   * anywhere else fails silently rather than loudly. */
  mkClosure(args: Binder[], body: StgExpr, owner?: Binder): StgRhs {
    const update =
      args.length > 0
        ? UpdateFlag.ReEntrant
        : owner?.singleEntry === true
          ? UpdateFlag.SingleEntry
          : UpdateFlag.Updatable;
    const bound = new Set(args);
    const freeVars = [...freeVarsOf(body)].filter((v) => !bound.has(v) && !this.topLevel.has(v));
    return { tag: "StgRhsClosure", freeVars, update, args, body };
  }

  /** `out` collects the bindings this expression had to float out. When the
   * caller passes one it takes on the job of re-attaching them, which is how
   * CorePrep gets a `case`'s scrutinee floats to enclose the whole `case`
   * rather than sit inside it. */
  expr(e: CoreExpr, out?: Float[]): StgExpr {
    const floats: Float[] = out ?? [];
    const done = (body: StgExpr): StgExpr => (out === undefined ? wrap(floats, body) : body);
    switch (e.tag) {
      case "Var":
        return { tag: "StgApp", fn: e.binder, args: [] };
      case "Lit":
        return { tag: "StgLit", lit: e.lit };
      case "Con": {
        const args = e.args.map((arg) => this.atom(arg, floats, false));
        return done({ tag: "StgConApp", con: e.con, args });
      }
      case "Op": {
        // A primop consumes machine values, so its arguments are evaluated
        // here rather than thunked.
        const args = e.args.map((arg) => this.atom(arg, floats, true));
        return done({ tag: "StgOpApp", op: e.op, args });
      }
      case "Lam": {
        // A lambda in a non-right-hand-side position still has to become a
        // closure before anything can refer to it.
        const binder = mkBinder("lam");
        return {
          tag: "StgLet",
          binding: { tag: "StgNonRec", binder, rhs: this.rhs(e, binder) },
          body: { tag: "StgApp", fn: binder, args: [] },
        };
      }
      case "Let": {
        // A source `let` is lazy, so it stays a `let`: the right-hand side
        // becomes a thunk the body enters, which is what CorePrep leaves and
        // what the backend allocates with h$c1.
        //
        // Whether that thunk needs an update frame is a fact about the body,
        // not the right-hand side, so it is decided here and left on the
        // binder for `mkClosure` to read.
        if (e.bind.tag === "NonRec") {
          const occ = occInfo(e.body, e.bind.binder.unique);
          if (occ.count === 1 && !occ.inLam) e.bind.binder.singleEntry = true;
        }
        return { tag: "StgLet", binding: this.bind(e.bind), body: this.expr(e.body) };
      }
      case "Case": {
        // The scrutinee's floats belong outside the whole `case`, not inside
        // its scrutinee: CorePrep produces `let sat = ... in case f x sat of`,
        // and a float left in the scrutinee would be generated after the
        // return frame was already pushed.
        const scrutinee = this.expr(e.scrutinee, floats);
        const alts = e.alts.map((alt) => this.alt(alt));
        // `case v of b { ... }`: inside the alternatives `b` and `v` denote the
        // same value, but `b` denotes it already evaluated - it is what the
        // return frame leaves in R1 - while `v` is still the original,
        // possibly-unentered pointer. GHC's CoreToStg leaves only `b` behind,
        // so `v` is not free in the alternatives and the return frame does not
        // save it. ghcts kept both, which cost a stack slot per frame *and* a
        // redundant re-entry of an already-forced value at every use.
        // Rewriting `v` to `b` here is what makes the emitted frame
        // `h$p2(acc, cont)` rather than `h$p3(n, acc, cont)`, matching GHC.
        //
        // Both binders must carry a runtime value for the swap to be
        // meaningful: a void binder (the state token) occupies no slot, and
        // `arity === 0` is how that is recorded.
        const scrutVar =
          scrutinee.tag === "StgApp" && scrutinee.args.length === 0 ? scrutinee.fn : undefined;
        const substituted =
          scrutVar !== undefined &&
          scrutVar.unique !== e.binder.unique &&
          scrutVar.arity !== 0 &&
          e.binder.arity !== 0
            ? alts.map((alt) => ({ ...alt, body: substBinder(alt.body, scrutVar, e.binder) }))
            : alts;
        // A `case` that tests a constructor tag or a literal proves what no
        // type annotation had to: only a data value can be matched against
        // `DataAlt`/`LitAlt`, so the scrutinee is a heap constructor and never
        // a bare function. That is precisely `not (mightBeFunTy (idType i))`,
        // and it is the fact `genApp` needs to emit `h$e(x)` rather than send
        // the value through the generic apply. It matters most in the Prelude,
        // where every instance method written `(+) (I a) (I b) = ...` forces
        // both of its arguments through exactly such a `case`, twice per
        // arithmetic operation.
        const altType = altTypeOf(e.alts, e.scrutinee);
        // The case binder names WHNF only when it is not the scrutinee
        // itself. Desugar reuses a `Var` scrutinee as the binder (`case p of
        // p { DEFAULT -> ... }`) so the Case still enters; marking that
        // binder evaluated makes `isInlineApp` skip the enter and unpack a
        // thunk.
        if (scrutVar === undefined || scrutVar.unique !== e.binder.unique)
          e.binder.evaluated = true;
        if (
          scrutVar !== undefined &&
          scrutVar.mightBeFun === undefined &&
          (altType.tag === "AlgAlt" || altType.tag === "PrimAlt")
        )
          scrutVar.mightBeFun = false;
        // The case binder stands for exactly the scrutinee's value, so what the
        // scrutinee's type proved about it holds of the binder too. Carrying
        // this over is what lets `genApp` emit `h$e(x)` instead of routing the
        // binder through the generic apply (see `Binder.mightBeFun`).
        if (substituted !== alts && scrutVar!.mightBeFun === false && e.binder.mightBeFun === undefined)
          e.binder.mightBeFun = false;
        return done({ tag: "StgCase", scrutinee, binder: e.binder, altType, alts: substituted });
      }
      case "App": {
        const [head, args] = flatten(e);
        const atoms = args.map((arg) => this.atom(arg, floats, false));
        if (head.tag === "Var") {
          return done({ tag: "StgApp", fn: head.binder, args: atoms });
        }
        // The head is itself a computation; name it, then apply the name. Its
        // float has to come before the arguments', since the arguments may
        // mention nothing of it but it is evaluated first.
        const headFloats: Float[] = [];
        const headAtom = this.atom(head, headFloats, true);
        if (headAtom.tag !== "StgVarArg") throw new Error("coreToStg: literal in function position");
        floats.unshift(...headFloats);
        return done({ tag: "StgApp", fn: headAtom.id, args: atoms });
      }
    }
  }

  alt(alt: CoreAlt): StgAlt {
    return { con: alt.con, binders: alt.binders, body: this.under(false, () => this.expr(alt.body)) };
  }

  bind(bind: CoreBind, toTop = false): StgBinding {
    return this.under(toTop, () =>
      bind.tag === "NonRec"
        ? { tag: "StgNonRec", binder: bind.binder, rhs: this.rhs(bind.rhs, bind.binder) }
        : { tag: "StgRec", pairs: bind.pairs.map(([b, rhs]) => [b, this.rhs(rhs, b)] as [Binder, StgRhs]) },
    );
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
   *
   * A variable is already an atom, whatever it is bound to. In particular a
   * reference to a top-level thunk is passed on unentered, exactly as
   * CorePrep leaves it: the pointer IS the value, and whoever needs it in
   * WHNF enters it. Forcing it here would be sound but would put a `case`
   * where GHC puts an argument.
   *
   * The thunks this pass now builds are Updatable rather than SingleEntry: the
   * argument they stand for can be duplicated by the callee, so the update is
   * not provably wasted, and a missing update frame fails silently. */
  atom(e: CoreExpr, floats: Float[], strict: boolean): StgArg {
    if (e.tag === "Lit") return litArg(e.lit);
    if (e.tag === "Var") return varArg(e.binder);
    const binder = mkBinder("t");
    // A lambda is already a value, so a strict position needs no `case` around
    // it - only the allocation. That matters for `catch#`, whose action and
    // handler are both lambdas: forcing them would push a return frame per
    // argument that the closure immediately returns into.
    const evaluate = (strict && e.tag !== "Lam") || e.tag === "Op";
    // Only one of the two translations is used, and each one walks `e` again.
    // Building both made a nested constructor cost 2^depth: a 25-character
    // string literal - `error "Prelude.head: empty list"` - took eleven
    // seconds to reach STG.
    const value = evaluate ? this.expr(e) : undefined;
    // CorePrep's top-level float, which is what leaves the Sinker something to
    // unfloat; when it takes the binding there is nothing left to re-attach.
    // The Core-level shape test comes first so that `rhs` is walked twice only
    // for a one-literal constructor - which allocates no binder of its own, so
    // the unique supply sees the same sequence it always did.
    const literalCon = e.tag === "Con" && e.args.length === 1 && e.args[0]!.tag === "Lit";
    if (!evaluate && literalCon && this.floatToTop(binder, this.rhs(e))) return varArg(binder);
    floats.push(
      evaluate
        ? (body) => ({
            tag: "StgCase",
            scrutinee: value!,
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
    // An unboxed tuple returns its fields in registers, so there is no tag to
    // dispatch on - only slots to unpack. `arity` counts the fields that
    // survive erasure, which for `(# State# RealWorld, a #)` is the one.
    if (alt.con.tag === "DataAlt" && isUnboxedTupleCon(alt.con.con)) {
      return { tag: "MultiValAlt", arity: alt.binders.reduce((n, b) => n + (b.arity ?? 1), 0) };
    }
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

/** Replace every occurrence of one binder with another throughout an STG
 * expression. Used for the `case v of b` rewrite in `expr` above.
 *
 * Binders are compared by `unique`, and a shadowing binding introduces a
 * *different* binder object with its own unique, so no scope tracking is
 * needed: a name that shadows `from` simply never matches it. */
function substBinder(expr: StgExpr, from: Binder, to: Binder): StgExpr {
  const sub = (b: Binder): Binder => (b.unique === from.unique ? to : b);
  const arg = (a: StgArg): StgArg =>
    a.tag === "StgVarArg" && a.id.unique === from.unique ? { ...a, id: to } : a;
  const rhs = (r: StgRhs): StgRhs =>
    r.tag === "StgRhsCon"
      ? { ...r, args: r.args.map(arg) }
      : { ...r, freeVars: r.freeVars.map(sub), body: go(r.body) };
  const go = (e: StgExpr): StgExpr => {
    switch (e.tag) {
      case "StgApp":
        return { ...e, fn: sub(e.fn), args: e.args.map(arg) };
      case "StgLit":
        return e;
      case "StgConApp":
      case "StgOpApp":
        return { ...e, args: e.args.map(arg) };
      case "StgCase":
        return {
          ...e,
          scrutinee: go(e.scrutinee),
          alts: e.alts.map((a) => ({ ...a, body: go(a.body) })),
        };
      case "StgLet":
      case "StgLetNoEscape":
        return {
          ...e,
          binding:
            e.binding.tag === "StgNonRec"
              ? { ...e.binding, rhs: rhs(e.binding.rhs) }
              : { ...e.binding, pairs: e.binding.pairs.map(([b, r]): [Binder, StgRhs] => [b, rhs(r)]) },
          body: go(e.body),
        };
    }
  };
  return go(expr);
}

function freeVarsOf(expr: StgExpr): Set<Binder> {
  const free = new Set<Binder>();
  const arg = (a: StgArg, scope: Set<Binder>): void => {
    // A void variable - the state token - has no runtime value, so it cannot
    // be a closure's payload slot: capturing it would reserve a field the
    // backend then never writes.
    if (a.tag === "StgVarArg" && a.id.arity !== 0 && !scope.has(a.id)) free.add(a.id);
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
  for (const bind of program.binds) {
    if (bind.tag === "NonRec") topLevel.add(bind.binder);
    else for (const [b] of bind.pairs) topLevel.add(b);
  }
  const converter = new Converter(topLevel);
  const bindings = program.binds.map((bind) => converter.bind(bind, true));
  return {
    name: program.name,
    // The floats go last, as CorePrep's do: nothing already emitted can refer
    // to a binder that did not exist when it was converted, and the Sinker's
    // `topSortDecls` is what puts any that survive ahead of their users.
    bindings: [...program.dataCons.map(conWorker), ...bindings, ...converter.floated],
  };
}
