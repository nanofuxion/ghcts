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

const isStaticFingerprintCon = (rhs: StgRhs): boolean =>
  rhs.tag === "StgRhsCon" && /fingerprint/i.test(rhs.con.name) && rhs.args.length >= 1;

const isStaticWord64Core = (e: CoreExpr): boolean => {
  if (e.tag !== "App" || e.arg.tag !== "Lit") return false;
  const head = e.fn;
  return head.tag === "App" && head.arg.tag === "Lit" && head.fn.tag === "Var" &&
    /(?:word64FromHalves|bigFromHalves)$/.test(head.fn.binder.name);
};

/** Either a `let` (a real allocation) or a `case` (evaluate now), the two
 * ways CorePrep floats a non-atomic subexpression out of an argument
 * position. Applied outside-in in the order they were produced. */
type Float = (body: StgExpr) => StgExpr;

const isStaticWord64 = (rhs: StgRhs): boolean =>
  rhs.tag === "StgRhsClosure" && rhs.args.length === 0 && rhs.body.tag === "StgApp" &&
  /(?:word64FromHalves|bigFromHalves)$/.test(rhs.body.fn.name) && rhs.body.args.length === 2 &&
  rhs.body.args.every((a) => a.tag === "StgLitArg");

/** Primops whose result is a lifted value taken from somewhere, not
 * computed: it may be an unevaluated thunk, so the case binder is not WHNF. */
const LIFTED_RESULT_PRIMOPS = new Set([
  "ReadMutVarOp", "AtomicModifyMutVar2Op", "AtomicModifyMutVar_Op", "AtomicSwapMutVarOp", "CasMutVarOp",
  "ReadArrayOp", "IndexArrayOp", "ReadSmallArrayOp", "IndexSmallArrayOp",
  "TakeMVarOp", "ReadMVarOp", "TryTakeMVarOp", "TryReadMVarOp", "ReadTVarOp", "ReadTVarIOOp",
  "DeRefWeakOp", "DeRefStablePtrOp", "CatchOp", "CatchRetryOp", "CatchSTMOp", "AtomicallyOp", "KeepAliveOp",
]);

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
  private readonly topByUnique: Map<number, Binder>;

  /**
   * @param topLevel every top-level binder, which `floatToTop` adds to. These
   * are never free variables of a closure: codegen resolves them to
   * module-level symbols, not payload slots.
   */
  constructor(
    private readonly topLevel: Set<Binder>,
    private readonly topRhs: Map<Binder, CoreExpr>,
  ) {
    this.topByUnique = new Map([...topLevel].map((b) => [b.unique, b]));
  }

  /** GHC's `dataConWorkId`: one Binder per DataCon, shared by every argument
   * that names the constructor and by its top-level worker binding, so free
   * variables, `luIdDeps` and the identifier cache all see one object.
   *
   * `exported` is what `liveVars` reads as `isGlobalId`, keeping the worker
   * out of closure payloads and return frames; `internal` stays unset because
   * it would suffix the symbol and let the Sinker sink the binding. */
  private readonly workers = new Map<DataCon, Binder>();
  workerFor(con: DataCon): Binder {
    let binder = this.workers.get(con);
    if (binder === undefined) {
      binder = {
        name: con.name,
        unique: con.unique,
        exported: true,
        topLevel: true,
        mightBeFun: false,
        definingUnitId: con.definingUnitId,
        definingModuleName: con.definingModuleName,
      };
      this.workers.set(con, binder);
      this.topLevel.add(binder);
    }
    return binder;
  }

  /** Core rewrites may clone references while retaining their unique. Keep
   * STG's top-level function facts (arity, strictness, representation) on the
   * canonical defining binder. */
  private canon(b: Binder): Binder {
    return this.aliases.get(b) ?? this.topByUnique.get(b.unique) ?? b;
  }

  /** `let x = False in e` never reaches GHC's STG: a nullary constructor is a
   * name, so the Simplifier substitutes it. Reaching codegen as a `let` it
   * would be an `h$c0(...)` allocation - for `Bool` a heap object where every
   * consumer tests a raw boolean. Keyed by the binder itself, so a shadowing
   * binder with a reused unique is a different key. */
  private readonly aliases = new Map<Binder, Binder>();
  /** The constructor each worker stands for, so an aliased variable in
   * expression position becomes `StgConApp dc []`, as `Con dc []` would. */
  private readonly aliasCon = new Map<Binder, DataCon>();

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
    if (!this.toTop || (!isAlwaysSinkableCon(rhs) && !isStaticWord64(rhs) && !isStaticFingerprintCon(rhs))) return false;
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
  rhs(expr: CoreExpr, owner?: Binder, recursive?: Set<Binder>): StgRhs {
    if (owner && expr.tag === "Var" && !expr.binder.sptFingerprint) {
      const target = this.topRhs.get(expr.binder);
      if (target?.tag === "Lam") {
        const params: Binder[] = [];
        let targetBody: CoreExpr = target;
        while (targetBody.tag === "Lam") {
          params.push(targetBody.binder);
          targetBody = targetBody.body;
        }
        if (params.length > 0) {
          expr = params.reduce<CoreExpr>(
            (fn, param) => ({ tag: "App", fn, arg: { tag: "Var", binder: param } }),
            { tag: "Var", binder: expr.binder },
          );
          for (const param of [...params].reverse()) expr = { tag: "Lam", binder: param, body: expr };
        }
      }
    }
    // A top-level alias to a static pointer is an evaluated value, not a thunk
    // that should enter the pointer CAF. GHC's CorePrep preserves this alias
    // as the StaticPtr constructor; retaining the constructor here also keeps
    // `staticKey ptr` on the direct projection path.
    if (owner && expr.tag === "Var" && expr.binder.sptFingerprint !== undefined) {
      const target = this.topRhs.get(expr.binder);
      if (target?.tag === "Con" && target.con.name === "StaticPtr") expr = target;
    }
    const args: Binder[] = [];
    let body = expr;
    while (body.tag === "Lam") {
      args.push(body.binder);
      body = body.body;
    }
    if (owner?.parameterReps) {
      for (let i = 0; i < args.length; i++) {
        const rep = owner.parameterReps[i];
        if (rep) args[i] = { ...args[i]!, primitiveRep: rep, ...(rep === "Bool" ? { unboxedInt: true as const } : {}) };
      }
    }
    const stgBody = this.under(this.toTop && args.length === 0, () => this.expr(body));

    // A constructor application with atomic arguments needs no entry code at
    // all: codegen can allocate it directly. Anything that had to be floated
    // stays a thunk, since an StgRhsCon has nowhere to put the bindings.
    if (stgBody.tag === "StgConApp" && (args.length === 0 || stgBody.con.name === "StaticPtr")) {
      const directBody = stgBody;
      // An unboxed tuple has no heap representation, so there is nothing to
      // bind here; reaching this means a caller put one in a lazy position
      // (an argument or a constructor field), which is exactly what GHC's
      // levity rules forbid. Failing loudly beats allocating a closure the
      // backend will never be able to enter.
      if (isUnboxedTupleCon(directBody.con)) throw new Error("coreToStg: unboxed tuple in a lazy position");
      // A constructor binding is a value, not a thunk, so every use of it is
      // already in WHNF. This is the easy half of GHC's InferTags, and
      // without it `genApp` sends each use through `h$ap_0_0_fast` to enter a
      // closure that was never going to do any work.
      if (owner) owner.evaluated = true;
      return { tag: "StgRhsCon", con: directBody.con, args: directBody.args };
    }
    if (owner && args.length > 0) {
      owner.funRepArity = args.length;
      // Function-ness supplies the entry arity, but not demand strictness.
      // GHCJS's `isStrictId` is a demand fact; ordinary user functions still
      // go through generic apply until strictness analysis proves otherwise.
      // A deliberately narrow seed set for native-region lowering: closed,
      // monomorphic primitive workers.  Later passes may reject this; no
      // caller may treat the bit as permission to skip the ABI wrapper.
      owner.nativeEligible =
        stgBody.tag === "StgOpApp" &&
        stgBody.op.tag === "StgPrimOp" &&
        args.every((a) => (a.arity ?? 1) === 1) &&
        // The lambda parameters are free in the lowered body by design. Only
        // external captures disqualify this primitive worker from the native
        // entry path.
        [...freeVarsOf(stgBody)].every((v) => args.some((a) => a.unique === v.unique));
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
    return this.mkClosure(args, stgBody, owner, recursive);
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
  mkClosure(args: Binder[], body: StgExpr, owner?: Binder, recursive?: Set<Binder>): StgRhs {
    const update =
      args.length > 0
        ? UpdateFlag.ReEntrant
        : owner?.singleEntry === true
          ? UpdateFlag.SingleEntry
          : UpdateFlag.Updatable;
    const bound = new Set(args.map((a) => a.unique));
    const freeVars = [...freeVarsOf(body)].filter(
      (v) => !bound.has(v.unique) && ![...(recursive ?? [])].some((r) => r.unique === v.unique) && ![...this.topLevel].some((t) => t.unique === v.unique),
    );
    if (process.env.GHCTS_TRACE_STG && owner) {
      const wanted = process.env.GHCTS_TRACE_STG;
      const text = [owner.name, ...args.map((a) => a.name), ...freeVars.map((v) => v.name)].join(" ");
      if (wanted === "*" || text.includes(wanted)) {
        console.error(`[ghcts stg] ${owner.name}#${owner.unique} args=[${args.map((a) => `${a.name}#${a.unique}/${a.arity ?? 1}`).join(",")}] free=[${freeVars.map((v) => `${v.name}#${v.unique}/${v.arity ?? 1}`).join(",")}] update=${update} native=${owner.nativeEligible ?? false}`);
      }
    }
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
      case "Var": {
        const alias = this.aliases.get(e.binder);
        if (alias) return { tag: "StgConApp", con: this.aliasCon.get(alias)!, args: [] };
        return { tag: "StgApp", fn: this.canon(e.binder), args: [] };
      }
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
          // GHC marks a thunk single-entry from its cardinality analysis, never
          // from one syntactic occurrence: a thunk passed once to a function is
          // entered as often as the callee likes. Here that occurrence has to
          // be the body's own `case` on it. Handed to `pack`, a once-used
          // thunk was entered by `forceString` and left un-updated, so GHC's
          // `h$jsstringPack` met a thunk instead of a cons and packed "" -
          // every JSON field name in misogram's swiper came out empty.
          if (e.bind.rhs.tag === "Con" && e.bind.rhs.args.length === 0 && !isUnboxedTupleCon(e.bind.rhs.con)) {
            // Scoped to the body: the Simplifier's case-of-case hands sibling
            // alternatives the same `let` binder object with different
            // right-hand sides (`sat = []` in one, `sat = 0 : ds` in the
            // other), and an alias left behind rewrote the second to `[]` -
            // `magMul [2] [0,1]` came out as `[0]`.
            const worker = this.workerFor(e.bind.rhs.con);
            const previous = this.aliases.get(e.bind.binder);
            this.aliases.set(e.bind.binder, worker);
            this.aliasCon.set(worker, e.bind.rhs.con);
            try {
              return this.expr(e.body, out);
            } finally {
              if (previous) this.aliases.set(e.bind.binder, previous);
              else this.aliases.delete(e.bind.binder);
            }
          }
          const occ = occInfo(e.body, e.bind.binder.unique);
          if (occ.count === 1 && !occ.inLam && scrutinisedOnce(e.body, e.bind.binder.unique)) e.bind.binder.singleEntry = true;
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
        const altType = altTypeOf(e.alts, e.scrutinee);
        // CorePrep's case-of-case keeps both matches as a strict case tree.
        // `expr` can expose the inner case here when a projection (such as
        // staticKey) was inlined into the outer scrutinee. STG cannot use a
        // case as an argument, so distribute the outer alternatives into the
        // inner alternatives instead of letting `atom` turn the projection
        // into a lazy let.
        if (scrutinee.tag === "StgCase") {
          return done({
            ...scrutinee,
            alts: scrutinee.alts.map((alt) => ({
              ...alt,
              body: {
                tag: "StgCase" as const,
                scrutinee: alt.body,
                binder: e.binder,
                altType,
                alts,
              },
            })),
          });
        }
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
        // The case binder names WHNF only when it is not the scrutinee
        // itself. Desugar reuses a `Var` scrutinee as the binder (`case p of
        // p { DEFAULT -> ... }`) so the Case still enters; marking that
        // binder evaluated makes `isInlineApp` skip the enter and unpack a
        // thunk.
        // ... unless the scrutinee is a primop that hands back a lifted value
        // it never entered: `readMutVar#` returns whatever was stored, thunk
        // included, and treating that binder as WHNF made `atomicModifyIORef'`
        // multiply an unevaluated closure (`Math.imul(closure, 2)` is 0).
        const liftedResult =
          scrutinee.tag === "StgOpApp" && scrutinee.op.tag === "StgPrimOp" && LIFTED_RESULT_PRIMOPS.has(scrutinee.op.op);
        if (!liftedResult && (scrutVar === undefined || scrutVar.unique !== e.binder.unique))
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
          return done({ tag: "StgApp", fn: this.canon(head.binder), args: atoms });
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
    const dataCon = alt.con.tag === "DataAlt" ? alt.con.con : undefined;
    const binders = dataCon
      ? alt.binders.map((b, i) => dataCon.fieldUnboxed?.[i] === true ? { ...b, unboxedInt: true as const } : b)
      : alt.binders;
    return { con: alt.con, binders, body: this.under(false, () => this.expr(alt.body)) };
  }

  bind(bind: CoreBind, toTop = false): StgBinding {
    return this.under(toTop, () =>
      bind.tag === "NonRec"
        ? { tag: "StgNonRec", binder: bind.binder, rhs: this.rhs(bind.rhs, bind.binder) }
        : {
            tag: "StgRec",
            pairs: bind.pairs.map(([b, rhs]) => [b, this.rhs(rhs, b, new Set(bind.pairs.map(([binder]) => binder)))] as [Binder, StgRhs]),
          },
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
    if (e.tag === "Var") return varArg(this.aliases.get(e.binder) ?? e.binder);
    // A nullary constructor is `Var (dataConWorkId dc)` in GHC's Core: trivial,
    // so CorePrep's `cpeArg` leaves it as an argument even in a strict
    // position, and `genArg` renders it `true_`/`false_` or the worker's
    // static closure. Let-binding it instead would allocate `h$c0(...)`, which
    // for `Bool` is a truthy object where GHC has `false`.
    if (e.tag === "Con" && e.args.length === 0 && !isUnboxedTupleCon(e.con)) return varArg(this.workerFor(e.con));
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
    const staticFingerprint = e.tag === "Con" && /fingerprint/i.test(e.con.name) && e.args.length >= 1;
    const staticWord64 = isStaticWord64Core(e);
    if (!evaluate && (literalCon || staticFingerprint || staticWord64) && this.floatToTop(binder, this.rhs(e))) return varArg(binder);
    floats.push(
      evaluate
        ? (body) => {
            const altType = altTypeOfExpr(e);
            if (value!.tag === "StgCase") {
              return {
                ...value!,
                alts: value!.alts.map((alt) => ({
                  ...alt,
                  body: {
                    tag: "StgCase" as const,
                    scrutinee: alt.body,
                    binder,
                    altType,
                    alts: [{ con: { tag: "DEFAULT" }, binders: [], body }],
                  },
                })),
              };
            }
            return {
              tag: "StgCase" as const,
              scrutinee: value!,
              binder,
              altType,
              alts: [{ con: { tag: "DEFAULT" }, binders: [], body }],
            };
          }
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
const conWorker = (binder: Binder, con: DataCon): StgBinding => ({
  tag: "StgNonRec",
  binder,
  rhs: { tag: "StgRhsCon", con, args: [] },
});

/** Whether the binder's only occurrence is as the scrutinee of a `case` -
 * the one shape where the body itself proves it is entered exactly once. */
function scrutinisedOnce(e: CoreExpr, u: number): boolean {
  let scrutinee = 0;
  let other = 0;
  const go = (x: CoreExpr): void => {
    switch (x.tag) {
      case "Var": if (x.binder.unique === u) other++; return;
      case "Lit": return;
      case "App": go(x.fn); go(x.arg); return;
      case "Lam": go(x.body); return;
      case "Let":
        if (x.bind.tag === "NonRec") go(x.bind.rhs); else for (const [, r] of x.bind.pairs) go(r);
        go(x.body); return;
      case "Case":
        if (x.scrutinee.tag === "Var" && x.scrutinee.binder.unique === u) scrutinee++; else go(x.scrutinee);
        for (const a of x.alts) go(a.body); return;
      case "Con": case "Op": for (const a of x.args) go(a); return;
    }
  };
  go(e);
  return scrutinee === 1 && other === 0;
}

export function coreToStg(program: CoreProgram): StgModule {
  const topLevel = new Set<Binder>();
  for (const bind of program.binds) {
    if (bind.tag === "NonRec") topLevel.add(bind.binder);
    else for (const [b] of bind.pairs) topLevel.add(b);
  }
  const topRhs = new Map<Binder, CoreExpr>();
  for (const bind of program.binds) {
    if (bind.tag === "NonRec") topRhs.set(bind.binder, bind.rhs);
    else for (const [b, rhs] of bind.pairs) topRhs.set(b, rhs);
  }
  // GHC's Id arity is available to every call site before any binding is
  // lowered. Pre-seed it here; discovering it only while converting a later
  // definition makes earlier calls fall through to generic apply.
  for (const [binder, rhs] of topRhs) {
    binder.topLevel = true;
    let body = rhs;
    let arity = 0;
    while (body.tag === "Lam") { arity++; body = body.body; }
    if (arity > 0) binder.funRepArity = arity;
  }
  const converter = new Converter(topLevel, topRhs);
  // Every worker exists before any body is converted, so `mkClosure` already
  // counts it top-level when it meets a reference.
  const workers = program.dataCons.map((con) => conWorker(converter.workerFor(con), con));
  const bindings = program.binds.map((bind) => converter.bind(bind, true));
  return {
    name: program.name,
    // The floats go last, as CorePrep's do: nothing already emitted can refer
    // to a binder that did not exist when it was converted, and the Sinker's
    // `topSortDecls` is what puts any that survive ahead of their users.
    bindings: [...workers, ...bindings, ...converter.floated],
  };
}
