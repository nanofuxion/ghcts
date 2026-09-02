/** Core-to-Core: find which arguments a function always forces, then force
 * them at the call site instead of building a thunk.
 *
 * This is the part of GHC's `DmdAnal` that pays for itself first
 * (`references/ghc/compiler/GHC/Core/Opt/DmdAnal.hs`), without any of the
 * unboxing that `WorkWrap` layers on top. A strict argument still arrives
 * boxed; it just arrives evaluated.
 *
 * The cost it removes is the dominant one in a counting loop. `sumTo` is
 * strict in both arguments, but `sumTo (acc + n) (n - 1)` still allocates a
 * thunk per argument per iteration, blackholes each on entry, and enters it
 * again at the `case`. Rewriting the call to
 *
 *     case acc + n of a -> case n - 1 of b -> sumTo a b
 *
 * hands `sumTo` two evaluated values and allocates nothing that was not
 * going to be evaluated anyway.
 *
 * WHY THIS PRESERVES SEMANTICS
 *
 * Forcing early is only sound where the callee forces unconditionally, so
 * the analysis is a `must` analysis, not a `may`:
 *
 *   - a `case` scrutinee is demanded, and so is anything the scrutinee
 *     demands;
 *   - a primop argument is demanded, because `Op` is strict in all of them;
 *   - a `Case` demands what EVERY alternative demands, intersected, plus
 *     whatever the scrutinee demands;
 *   - a `Let` demands only what its body demands. A right-hand side is a
 *     thunk and may never run.
 *   - a `Con` demands nothing. Constructor fields are lazy.
 *   - an application demands what the callee demands in that position, and
 *     nothing at all through an unknown callee.
 *
 * Recursive groups start at "strict in everything" and are weakened to a
 * fixpoint, which is the standard least-fixpoint reading of a `must`
 * analysis and is what makes a self-recursive loop analysable at all.
 *
 * The one thing this does change is WHICH exception surfaces when two
 * arguments both diverge, because the forcing order becomes left to right.
 * Haskell's imprecise-exception semantics permit exactly that, and GHC's own
 * strictness-driven evaluation makes the same trade
 * (`Note [Precise exceptions and strictness analysis]`, DmdAnal.hs).
 * Bottom-vs-value is unaffected: a forced argument was always going to be
 * forced.
 */
import type { CoreBind, CoreExpr, CoreProgram } from "../core.js";
import { mkBinder, type Binder } from "../stg.js";

/** Which parameters of a top-level function are known to be forced. */
type Strictness = Map<number, boolean[]>;

const isTrivial = (e: CoreExpr): boolean => e.tag === "Var" || e.tag === "Lit";


/** Demand an expression in a strict position. Returning a variable does not
 * force it (the worker may simply return the boxed value), but a variable used
 * as a case scrutinee, primop argument, or strict call argument does. */
function forceDemanded(e: CoreExpr, known: Strictness): Set<number> {
  const out = demanded(e, known);
  if (e.tag === "Var") out.add(e.binder.unique);
  return out;
}

/** Peel `\x1 .. xn -> body`. */
function lambdas(e: CoreExpr): { params: Binder[]; body: CoreExpr } {
  const params: Binder[] = [];
  let body = e;
  while (body.tag === "Lam") {
    params.push(body.binder);
    body = body.body;
  }
  return { params, body };
}

function spine(e: CoreExpr): { head: CoreExpr; args: CoreExpr[] } {
  const args: CoreExpr[] = [];
  let head = e;
  while (head.tag === "App") {
    args.unshift(head.arg);
    head = head.fn;
  }
  return { head, args };
}

/** The wired Int instance methods are strict in every value argument.  They
 * can be encountered before their generated bindings enter the fixpoint
 * environment (notably while analysing a source function that is itself
 * preserved), so record this backend fact directly. */
function primitiveMethodStrictness(name: string): boolean[] | undefined {
  if (/^\$fNumInt_\$c(?:[+*\-/])$/.test(name) || /^\$fOrdInt_\$c(?:[<>]=?|compare)$/.test(name)) return [true, true];
  if (/^\$fNumInt_\$cnegate$/.test(name)) return [true];
  return undefined;
}

/** The set of binder uniques this expression forces before it can return.
 * `known` supplies the argument strictness of callees analysed so far. */
function demanded(e: CoreExpr, known: Strictness): Set<number> {
  switch (e.tag) {
    // Returning a variable is still tracked for the existing worker/wrapper
    // fixpoint; strict-position callers use forceDemanded to make WHNF use
    // explicit.
    case "Var":
      return new Set([e.binder.unique]);
    case "Lit":
      return new Set();
    case "Lam":
      // Entering a lambda demands nothing; the body only runs once applied.
      return new Set();
    case "Let": {
      const out = demanded(e.body, known);
      // If the body is certain to force the binding, the right-hand side runs,
      // and everything it forces is forced too. Stopping at the body loses
      // every argument a `where` helper demands.
      if (e.bind.tag === "NonRec" && out.has(e.bind.binder.unique))
        for (const u of forceDemanded(e.bind.rhs, known)) out.add(u);
      return out;
    }
    case "Con":
      return new Set();
    case "Op": {
      // Primops are strict in every argument - except the ones that *store*
      // a lifted value rather than look at it: `newMutVar# (error "x")` must
      // not raise. Those are GHC's lazy-argument primops.
      const out = new Set<number>();
      if (e.op.tag === "StgPrimOp" && LAZY_PRIMOPS.has(e.op.op)) return out;
      for (const a of e.args) for (const u of forceDemanded(a, known)) out.add(u);
      return out;
    }
    case "Case": {
      const out = forceDemanded(e.scrutinee, known);
      if (e.alts.length === 0) return out;
      // Only what every branch demands can be demanded by the `case`.
      const per = e.alts.map((a) => demanded(a.body, known));
      for (const u of per[0]!) if (per.every((s) => s.has(u))) out.add(u);
      return out;
    }
    case "App": {
      const { head, args } = spine(e);
      const out = new Set<number>();
      if (head.tag !== "Var" || !head.binder) return out;
      // Applying a function forces the function: whatever closure the head
      // names has to be in weak head normal form before an argument can be
      // handed to it. GHC's `Note [Demand on the worker]` counts the same.
      out.add(head.binder.unique);
      const sig = known.get(head.binder.unique) ?? primitiveMethodStrictness(head.binder.name);
      if (!sig) {
        return out;
      }
      // A worker is introduced after the source function's demand has been
      // established. Propagating the worker's provisional all-strict demand
      // through its recursive call turns an accumulator that is returned by
      // the base branch into a false strict demand. Its own cases and
      // primops remain visible below; only the recursive call edge is cut.
      if (head.binder.name.startsWith("$w")) return out;
      args.forEach((a, i) => {
        if (sig[i] === true) for (const u of forceDemanded(a, known)) out.add(u);
      });
      return out;
    }
  }
}

/** Argument strictness for every top-level function, by least fixpoint. */
function analyse(program: CoreProgram): Strictness {
  const fns = new Map<number, { params: Binder[]; body: CoreExpr }>();
  /** Local functions count too. A `where` helper is a `let`-bound lambda, and
   * without a signature for it every call to one teaches the analysis nothing
   * - which in library code is most calls. Binder uniques are program-wide, so
   * one map holds both. */
  const collect = (e: CoreExpr): void => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return;
      case "App":
        collect(e.fn);
        collect(e.arg);
        return;
      case "Lam":
        collect(e.body);
        return;
      case "Let": {
        const pairs =
          e.bind.tag === "NonRec"
            ? [[e.bind.binder, e.bind.rhs] as const]
            : e.bind.pairs.map((p) => [p[0], p[1]] as const);
        for (const [binder, rhs] of pairs) {
          const l = lambdas(rhs);
          if (l.params.length > 0) fns.set(binder.unique, l);
          collect(rhs);
        }
        collect(e.body);
        return;
      }
      case "Case":
        collect(e.scrutinee);
        for (const a of e.alts) collect(a.body);
        return;
      case "Con":
      case "Op":
        for (const a of e.args) collect(a);
        return;
    }
  };
  for (const b of program.binds)
    if (b.tag === "NonRec") collect(b.rhs);
    else for (const [, r] of b.pairs) collect(r);
  for (const b of program.binds) {
    const pairs = b.tag === "NonRec" ? [[b.binder, b.rhs] as const] : b.pairs.map((p) => [p[0], p[1]] as const);
    for (const [binder, rhs] of pairs) {
      const l = lambdas(rhs);
      if (l.params.length > 0) fns.set(binder.unique, l);
    }
  }

  // Optimistic start, weakened until stable: the existing worker/wrapper
  // rewrite relies on recursive calls being visible on the first pass.
  const known: Strictness = new Map();
  for (const [u, f] of fns) known.set(u, f.params.map(() => true));

  for (let pass = 0, changed = true; changed && pass < 20; pass++) {
    changed = false;
    for (const [u, f] of fns) {
      const d = demanded(f.body, known);
      const next = f.params.map((p) => d.has(p.unique));
      // WorkWrap workers receive an already-unboxed payload. A payload that is
      // returned by the base branch is not forced by the worker; treating the
      // returned variable as a strict demand is the classic SS-vs-LS error.
      // Keep this exception local to generated workers so ordinary functions
      // retain the existing must-demand interpretation.
      if (fns.get(u) === f && program.binds.some((b) => b.tag === "NonRec" && b.binder.unique === u && b.binder.name.startsWith("$w")))
        next[0] = false;
      const prev = known.get(u)!;
      if (next.some((v, i) => v !== prev[i])) {
        known.set(u, next);
        changed = true;
      }
    }
  }
  return known;
}

/** The analysis on its own, by binder name, so it can be checked against
 * GHC's own demand signatures (`scripts/stg-diff.mjs`). GHC prints one
 * `<...>` per argument in the `Str=` field of every STG binding, which is the
 * same fact this computes: `true` where the argument is always forced. */
/** Primops whose arguments are lifted values they hold but never enter. */
const LAZY_PRIMOPS = new Set([
  "NewMutVarOp", "WriteMutVarOp", "AtomicSwapMutVarOp", "AtomicModifyMutVar2Op", "CasMutVarOp",
  "NewMVarOp", "PutMVarOp", "TryPutMVarOp", "NewTVarOp", "WriteTVarOp",
  "NewArrayOp", "WriteArrayOp", "NewSmallArrayOp", "WriteSmallArrayOp",
  "MkWeakOp", "MkWeakNoFinalizerOp", "MakeStablePtrOp", "MakeStableNameOp",
  "CatchOp", "CatchRetryOp", "CatchSTMOp", "RaiseOp", "RaiseIOOp", "ForkOp", "ForkOnOp",
  "MaskAsyncExceptionsOp", "MaskUninterruptibleOp", "UnmaskAsyncExceptionsOp", "KeepAliveOp", "TouchOp", "SparkOp",
]);

export function argStrictness(program: CoreProgram): Map<string, boolean[]> {
  const known = analyse(program);
  const out = new Map<string, boolean[]>();
  for (const b of program.binds) {
    const pairs = b.tag === "NonRec" ? [[b.binder, b.rhs] as const] : b.pairs.map((x) => [x[0], x[1]] as const);
    for (const [binder, rhs] of pairs) {
      // Eta reduction turns bindings such as `add a b = a + b` into a direct
      // alias of the already analysed method. Preserve the signature across
      // that representation change so diagnostics and later consumers do not
      // mistake a valid strict function for an unknown one.
      const sig = known.get(binder.unique) ??
        (rhs.tag === "Var" ? known.get(rhs.binder.unique) : undefined);
      if (sig) out.set(binder.name, sig);
    }
  }
  return out;
}

/** The same analysis, keyed by the binder's unique.
 *
 * `argStrictness` is by name because that is how GHC's dumps are read back.
 * A pass that rewrites bindings cannot use a name: one linked program holds
 * every module's top-level binders, and names like `go` or `lvl` repeat
 * across them, so a by-name lookup hands one binding's signature to an
 * unrelated one - and `workWrap` then unboxes an argument nobody forces. */
export const argStrictnessByUnique = (program: CoreProgram): Map<number, boolean[]> => analyse(program);

/** Rewrite `f e1 .. en` so that every argument `f` is strict in is evaluated
 * by a `case` before the call. */
/** A right-hand side worth turning into a `case`: not already a value, and
 * not a lambda - a function closure is in weak head normal form, so forcing
 * it would allocate a `case` for nothing. */
const worthForcing = (e: CoreExpr): boolean =>
  e.tag === "App" || e.tag === "Case" || e.tag === "Let" || e.tag === "Op";

export function forceStrictArgs(program: CoreProgram): CoreProgram {
  const known = analyse(program);

  const go = (e: CoreExpr): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: go(e.body) };
      case "Let": {
        const bind: CoreBind =
          e.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: e.bind.binder, rhs: go(e.bind.rhs) }
            : { tag: "Rec", pairs: e.bind.pairs.map(([b, r]) => [b, go(r)] as [Binder, CoreExpr]) };
        const body = go(e.body);
        // let-to-case. A binding the body is certain to force does not need to
        // be a thunk: allocating one, entering it, black-holing it and writing
        // the result back is work whose only purpose is to delay something
        // that is not being delayed. Evaluating it here instead is what GHC's
        // `Note [Let to case]` does, and the counter app forces roughly ten
        // times as many thunks per tap as GHC's build of the same program.
        if (bind.tag === "NonRec" && worthForcing(bind.rhs) && demanded(body, known).has(bind.binder.unique))
          return {
            tag: "Case",
            scrutinee: bind.rhs,
            binder: bind.binder,
            alts: [{ con: { tag: "DEFAULT" }, binders: [], body }],
          };
        return { tag: "Let", bind, body };
      }
      case "Case":
        return {
          tag: "Case",
          scrutinee: go(e.scrutinee),
          binder: e.binder,
          alts: e.alts.map((a) => ({ ...a, body: go(a.body) })),
        };
      case "Con":
        return { tag: "Con", con: e.con, args: e.args.map(go) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map(go) };
      case "App": {
        const { head, args } = spine(e);
        const done = args.map(go);
        const sig = head.tag === "Var" && head.binder ? known.get(head.binder.unique) : undefined;
        if (!sig) return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head));
        // A call need not be saturated for the signature to say something. An
        // under-applied call still passes the arguments it has, in order, and
        // an over-applied one passes the first `sig.length` to this function
        // and the rest to whatever it returns. Requiring an exact match threw
        // away every partial application - which, with dictionaries curried in
        // front of real arguments, is most calls in library code.
        // Bind each strict, non-trivial argument to a `case` outside the
        // call, innermost first so the order stays left to right.
        const forced: Array<{ binder: Binder; rhs: CoreExpr }> = [];
        const finalArgs = done.map((a, i) => {
          // The list Foldable instance makes `length` strict in its collection
          // argument. Its polymorphic wrapper can lose that fact when the
          // dictionary has already been specialized, but GHC unfolds this
          // exact call and keeps the collection as a strict case tree.
          const lengthCollection = head.tag === "Var" && head.binder?.name === "length" && i === 1;
          if (i >= sig.length || (!lengthCollection && sig[i] !== true) || isTrivial(a)) return a;
          const binder = mkBinder("sat");
          forced.push({ binder, rhs: a });
          return { tag: "Var", binder } as CoreExpr;
        });
        let call = finalArgs.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head));
        for (let i = forced.length - 1; i >= 0; i--) {
          const f = forced[i]!;
          call = {
            tag: "Case",
            scrutinee: f.rhs,
            binder: f.binder,
            alts: [{ con: { tag: "DEFAULT" }, binders: [], body: call }],
          };
        }
        return call;
      }
    }
  };

  return {
    ...program,
    binds: program.binds.map((b) => {
      if (b.tag === "Rec")
        return { tag: "Rec" as const, pairs: b.pairs.map(([bd, r]) => [bd, go(r)] as [Binder, CoreExpr]) };
      const sig = known.get(b.binder.unique);
      // `genApp`'s direct-jump predicate needs the same whole-function demand
      // fact as GHCJS's `isStrictId`. Per-argument forcing is already recorded
      // by the cases inserted above; expose the aggregate fact on the binder
      // for generated primitive methods and ordinary strict workers alike.
      if (sig && sig.length > 0 && sig.every(Boolean)) {
        b.binder.strict = true;
        // A strict boxed wrapper is still entered through the ordinary JS
        // apply ABI. Direct jumps are valid only for the native-region
        // functions whose representation was proved by Core-to-STG.
        if (b.binder.nativeEligible === true && !b.binder.name.includes("$c") && !b.binder.name.includes("$zdc"))
          b.binder.directJumpEligible = true;
      }
      return { tag: "NonRec" as const, binder: b.binder, rhs: go(b.rhs) };
    }),
  };
}
