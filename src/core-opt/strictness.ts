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

/** The set of binder uniques this expression forces before it can return.
 * `known` supplies the argument strictness of callees analysed so far. */
function demanded(e: CoreExpr, known: Strictness): Set<number> {
  switch (e.tag) {
    // Returning a variable demands it: the caller is in a `case` or is
    // itself demanded, which is the only way this expression is reached.
    case "Var":
      return new Set([e.binder.unique]);
    case "Lit":
      return new Set();
    case "Lam":
      // Entering a lambda demands nothing; the body only runs once applied.
      return new Set();
    case "Let":
      return demanded(e.body, known);
    case "Con":
      return new Set();
    case "Op": {
      // Primops are strict in every argument.
      const out = new Set<number>();
      for (const a of e.args) for (const u of demanded(a, known)) out.add(u);
      return out;
    }
    case "Case": {
      const out = demanded(e.scrutinee, known);
      if (e.alts.length === 0) return out;
      // Only what every branch demands can be demanded by the `case`.
      const per = e.alts.map((a) => demanded(a.body, known));
      for (const u of per[0]!) if (per.every((s) => s.has(u))) out.add(u);
      return out;
    }
    case "App": {
      const { head, args } = spine(e);
      const out = new Set<number>();
      if (head.tag !== "Var") return out;
      const sig = known.get(head.binder.unique);
      if (!sig) return out;
      args.forEach((a, i) => {
        if (sig[i] === true) for (const u of demanded(a, known)) out.add(u);
      });
      return out;
    }
  }
}

/** Argument strictness for every top-level function, by least fixpoint. */
function analyse(program: CoreProgram): Strictness {
  const fns = new Map<number, { params: Binder[]; body: CoreExpr }>();
  for (const b of program.binds) {
    const pairs = b.tag === "NonRec" ? [[b.binder, b.rhs] as const] : b.pairs.map((p) => [p[0], p[1]] as const);
    for (const [binder, rhs] of pairs) {
      const l = lambdas(rhs);
      if (l.params.length > 0) fns.set(binder.unique, l);
    }
  }

  // Optimistic start, weakened until stable: the least fixpoint for a `must`
  // analysis, so a self-recursive call does not defeat itself on the first
  // pass.
  const known: Strictness = new Map();
  for (const [u, f] of fns) known.set(u, f.params.map(() => true));

  for (let pass = 0, changed = true; changed && pass < 20; pass++) {
    changed = false;
    for (const [u, f] of fns) {
      const d = demanded(f.body, known);
      const next = f.params.map((p) => d.has(p.unique));
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
export function argStrictness(program: CoreProgram): Map<string, boolean[]> {
  const known = analyse(program);
  const out = new Map<string, boolean[]>();
  for (const b of program.binds) {
    const pairs = b.tag === "NonRec" ? [[b.binder, b.rhs] as const] : b.pairs.map((x) => [x[0], x[1]] as const);
    for (const [binder] of pairs) {
      const sig = known.get(binder.unique);
      if (sig) out.set(binder.name, sig);
    }
  }
  return out;
}

/** Rewrite `f e1 .. en` so that every argument `f` is strict in is evaluated
 * by a `case` before the call. */
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
        return { tag: "Let", bind, body: go(e.body) };
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
        const sig = head.tag === "Var" ? known.get(head.binder.unique) : undefined;
        if (!sig || sig.length !== done.length) {
          return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head));
        }
        // Bind each strict, non-trivial argument to a `case` outside the
        // call, innermost first so the order stays left to right.
        const forced: Array<{ binder: Binder; rhs: CoreExpr }> = [];
        const finalArgs = done.map((a, i) => {
          if (sig[i] !== true || isTrivial(a)) return a;
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
    binds: program.binds.map((b) =>
      b.tag === "NonRec"
        ? { tag: "NonRec", binder: b.binder, rhs: go(b.rhs) }
        : { tag: "Rec", pairs: b.pairs.map(([bd, r]) => [bd, go(r)] as [Binder, CoreExpr]) },
    ),
  };
}
