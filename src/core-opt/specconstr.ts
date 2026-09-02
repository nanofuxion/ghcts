/** Core-to-Core: GHC's SpecConstr, narrowed to a function argument.
 *
 * `row <$> [1 .. rowCount]` desugars to a genuine call to the library `map`
 * (`instance Functor [] where fmap f xs = map f xs`, inlined by
 * `inlineKnownCalls` once the dictionary is known). `map` is
 *
 *     map f xs = case xs of
 *       []       -> []
 *       (y : ys) -> f y : map f ys
 *
 * and `row` is passed to it as a plain value. `inlineKnownCalls` only
 * rewrites a call site it can see syntactically as `App(Var name, args)`;
 * `row n` never appears written out anywhere in the user's own Core, because
 * `map`'s *own* recursive definition is what applies it. `map` itself is
 * never a candidate either - it calls itself, and `collectInlineCandidates`
 * excludes anything that reaches back to itself. No amount of raising the
 * size cap closes this: the call site that needs rewriting is inside `map`,
 * not inside the user's code.
 *
 * This is GHC's SpecConstr: when a recursive function is called with a
 * known, non-recursive function in one of its arguments, clone the function,
 * substitute that argument's *body* wherever the clone applies the
 * parameter, and redirect the clone's own recursive calls to itself. The
 * clone is exactly `map` with `f` baked in - no closure entered per element,
 * the same shape GHC's `$wviewModel` has for this program.
 *
 * Scope, deliberately narrow: exactly one parameter position may be "the
 * function" (used only in application position, never scrutinised, never
 * returned bare - `usedOnlyApplied` checks this), the recursive function
 * must be a self-recursive top-level `NonRec` (a mutually-recursive group is
 * left alone), and the candidate substituted in is unary. The implementation
 * currently admits only the list `map` family; other shapes should earn
 * their own micro-app evidence before they are enabled globally.
 */
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "../core.js";
import { coreFreeVars, mkApps, mkLams } from "../core.js";
import { mkBinder, type Binder } from "../stg.js";
import { type Candidate, collectInlineCandidates, copy } from "./inline.js";

/** Peel an application spine into its head and arguments, outermost last. */
function spine(e: CoreExpr): { head: CoreExpr; args: CoreExpr[] } {
  const args: CoreExpr[] = [];
  let head = e;
  while (head.tag === "App") {
    args.unshift(head.arg);
    head = head.fn;
  }
  return { head, args };
}

function exprSize(e: CoreExpr): number {
  switch (e.tag) {
    case "Var":
    case "Lit":
      return 1;
    case "App":
      return 1 + exprSize(e.fn) + exprSize(e.arg);
    case "Lam":
      return 1 + exprSize(e.body);
    case "Let":
      return 1 + (e.bind.tag === "NonRec" ? exprSize(e.bind.rhs) : e.bind.pairs.reduce((n, [, r]) => n + exprSize(r), 0)) + exprSize(e.body);
    case "Case":
      return 1 + exprSize(e.scrutinee) + e.alts.reduce((n, a) => n + exprSize(a.body), 0);
    case "Con":
    case "Op":
      return 1 + e.args.reduce((n, a) => n + exprSize(a), 0);
  }
}

/** `pu` used only as `App(Var pu, _)`, never scrutinised and never returned
 * on its own - the shape substitution can replace wholesale. Bails (returns
 * false) the moment `pu` shows up anywhere else, so a function that also
 * pattern-matches its function argument (there is no such thing in Haskell,
 * but a corrupted AST is not this pass's problem to diagnose) is left alone
 * rather than miscompiled. */
function usedOnlyApplied(e: CoreExpr, pu: number, self: number): boolean {
  let ok = true;
  const go = (x: CoreExpr): void => {
    if (!ok) return;
    switch (x.tag) {
      case "Var":
        if (x.binder.unique === pu) ok = false; // bare occurrence - not applied
        return;
      case "Lit":
        return;
      case "App": {
        const { head, args } = spine(x);
        if (head.tag === "Var" && head.binder.unique === pu) {
          for (const a of args) go(a);
          return;
        }
        // A recursive loop must forward its function parameter to the next
        // iteration. That occurrence is not a use of `f` as a value by the
        // loop body: the specialized clone keeps the same parameter and the
        // forwarding call remains well-scoped after self-call redirection.
        if (head.tag === "Var" && head.binder.unique === self) {
          for (const a of args) {
            if (a.tag === "Var" && a.binder.unique === pu) continue;
            go(a);
          }
          return;
        }
        go(x.fn);
        go(x.arg);
        return;
      }
      case "Lam":
        if (x.binder.unique === pu) return; // shadowed
        go(x.body);
        return;
      case "Let":
        if (x.bind.tag === "NonRec") {
          if (x.bind.binder.unique !== pu) go(x.bind.rhs);
        } else {
          for (const [b, r] of x.bind.pairs) if (b.unique !== pu) go(r);
        }
        go(x.body);
        return;
      case "Case":
        go(x.scrutinee);
        for (const a of x.alts) if (!a.binders.some((b) => b.unique === pu)) go(a.body);
        return;
      case "Con":
      case "Op":
        for (const a of x.args) go(a);
        return;
    }
  };
  go(e);
  return ok;
}

/** Does `body` apply `pu` at all? `usedOnlyApplied` alone is true (vacuously)
 * for a function that never touches its function argument at all - nothing
 * to specialise there. */
function appliesParam(e: CoreExpr, pu: number): boolean {
  let found = false;
  const go = (x: CoreExpr): void => {
    if (found || !x || typeof x !== "object") return;
    if (x.tag === "App") {
      const { head } = spine(x);
      if (head.tag === "Var" && head.binder.unique === pu) {
        found = true;
        return;
      }
    }
    for (const v of Object.values(x)) Array.isArray(v) ? v.forEach(go) : go(v as CoreExpr);
  };
  go(e);
  return found;
}

interface Loop {
  binder: Binder;
  params: Binder[];
  body: CoreExpr;
  funcParamIndex: number;
}

function collectCandidates(e: CoreExpr, out: Map<number, Candidate>, byBinder?: Map<Binder, Candidate>, byName?: Map<string, Candidate>): void {
  if (e.tag === "Let") {
    const bindings = e.bind.tag === "NonRec" ? [[e.bind.binder, e.bind.rhs] as const] : e.bind.pairs;
    for (const [binder, rhs] of bindings) {
      let body = rhs;
      const params: Binder[] = [];
      while (body.tag === "Lam") {
        params.push(body.binder);
        body = body.body;
      }
      // Local bindings are deliberately collected for SpecConstr only. They
      // must be cloned in their call site's scope, since their free variables
      // are often view/model values and cannot be hoisted safely.
      if (params.length > 0 && ![...coreFreeVars(body, new Set(params))].some((v) => v.unique === binder.unique)) {
        const candidate = { params, body };
        if (!out.has(binder.unique)) out.set(binder.unique, candidate);
        byBinder?.set(binder, candidate);
        byName?.set(binder.name, candidate);
      }
      collectCandidates(rhs, out, byBinder, byName);
    }
    collectCandidates(e.body, out, byBinder, byName);
    return;
  }
  if (e.tag === "App") { collectCandidates(e.fn, out, byBinder, byName); collectCandidates(e.arg, out, byBinder, byName); return; }
  if (e.tag === "Lam") { collectCandidates(e.body, out, byBinder, byName); return; }
  if (e.tag === "Case") { collectCandidates(e.scrutinee, out, byBinder, byName); e.alts.forEach((a) => collectCandidates(a.body, out, byBinder, byName)); return; }
  if (e.tag === "Con" || e.tag === "Op") { e.args.forEach((a) => collectCandidates(a, out, byBinder, byName)); }
}

/** Every top-level, self-recursive `NonRec` binding with exactly one
 * parameter used only in application position. */
function collectLoops(program: CoreProgram): Map<Binder, Loop> {
  const out = new Map<Binder, Loop>();
  for (const b of program.binds) {
    if (b.tag !== "NonRec") continue;
    // Match structurally rather than by spelling. After Core-to-Core
    // lowering, Prelude's `map` is commonly represented by an anonymous
    // recursive worker, while the exported `map` binding is only its entry
    // point. The remaining guards below keep this from becoming a general
    // recursive-function cloning pass.
    // Flattened/imported Core may retain a worker suffix (for example
    // `map$worker` or `mapList$1`).  It is still the same recursive map
    // family; rejecting the suffix silently loses the specialization after
    // module flattening.
    if (!/(?:^|_)(?:\$w)?(?:map|mapList)(?:\$.*|\d*)$/i.test(b.binder.name)) continue;
    const params: Binder[] = [];
    let body = b.rhs;
    while (body.tag === "Lam") {
      params.push(body.binder);
      body = body.body;
    }
    if (params.length === 0) continue;
    if (![...coreFreeVars(body, new Set(params))].some((v) => v.unique === b.binder.unique)) continue; // not self-recursive
    const funcParamIndex = params.findIndex(
      (p) => appliesParam(body, p.unique) && usedOnlyApplied(body, p.unique, b.binder.unique),
    );
    if (funcParamIndex === -1) continue;
    out.set(b.binder, { binder: b.binder, params, body, funcParamIndex });
  }
  return out;
}

/** Rewrite every fully-saturated self-call `loop.binder args...` inside a
 * clone's body to call `replacement` instead - the step that makes the
 * specialisation hold through the recursion, not just the outer call. */
function redirectSelfCalls(e: CoreExpr, loop: Loop, replacement: Binder, droppedParam: number, captures: Binder[] = []): CoreExpr {
  const go = (x: CoreExpr): CoreExpr => {
    switch (x.tag) {
      case "Var":
      case "Lit":
        return x;
      case "App": {
        const { head, args } = spine(x);
        if (head.tag === "Var" && head.binder && head.binder.unique === loop.binder.unique && args.length === loop.params.length)
          return mkApps({ tag: "Var", binder: replacement }, [
            ...args.filter((_, i) => i !== droppedParam).map(go),
            ...captures.map((b) => ({ tag: "Var" as const, binder: b })),
          ]);
        return { tag: "App", fn: go(x.fn), arg: go(x.arg) };
      }
      case "Lam":
        return { tag: "Lam", binder: x.binder, body: go(x.body) };
      case "Let": {
        const bind: CoreBind =
          x.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: x.bind.binder, rhs: go(x.bind.rhs) }
            : { tag: "Rec", pairs: x.bind.pairs.map(([bd, r]) => [bd, go(r)] as [Binder, CoreExpr]) };
        return { tag: "Let", bind, body: go(x.body) };
      }
      case "Case": {
        const alts: CoreAlt[] = x.alts.map((a) => ({ ...a, body: go(a.body) }));
        return { tag: "Case", scrutinee: go(x.scrutinee), binder: x.binder, alts };
      }
      case "Con":
        return { tag: "Con", con: x.con, args: x.args.map(go) };
      case "Op":
        return { tag: "Op", op: x.op, arity: x.arity, args: x.args.map(go) };
    }
  };
  return go(e);
}

/** Replace every `App(Var pu, arg)` in `e` with `candidate` inlined at
 * `arg`, exactly the substitution `inlineKnownCalls` does for a known
 * saturated call. `usedOnlyApplied` already proved `pu` never appears any
 * other way, so this rewrites every occurrence. */
function substituteParam(e: CoreExpr, pu: Binder, candidate: Candidate, outerSub: Map<number | Binder, CoreExpr> = new Map()): CoreExpr {
  const go = (x: CoreExpr): CoreExpr => {
    switch (x.tag) {
      case "Var":
      case "Lit":
        return x;
      case "App": {
        const { head, args } = spine(x);
        if (head.tag === "Var" && head.binder === pu && args.length === candidate.params.length) {
          const sub = new Map<number | Binder, CoreExpr>(outerSub);
          candidate.params.forEach((p, i) => sub.set(p, go(args[i]!)));
          return copy(candidate.body, sub, new Map());
        }
        return { tag: "App", fn: go(x.fn), arg: go(x.arg) };
      }
      case "Lam":
        return { tag: "Lam", binder: x.binder, body: go(x.body) };
      case "Let": {
        const bind: CoreBind =
          x.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: x.bind.binder, rhs: go(x.bind.rhs) }
            : { tag: "Rec", pairs: x.bind.pairs.map(([bd, r]) => [bd, go(r)] as [Binder, CoreExpr]) };
        return { tag: "Let", bind, body: go(x.body) };
      }
      case "Case": {
        const alts: CoreAlt[] = x.alts.map((a) => ({ ...a, body: go(a.body) }));
        return { tag: "Case", scrutinee: go(x.scrutinee), binder: x.binder, alts };
      }
      case "Con":
        return { tag: "Con", con: x.con, args: x.args.map(go) };
      case "Op":
        return { tag: "Op", op: x.op, arity: x.arity, args: x.args.map(go) };
    }
  };
  return go(e);
}

export function specConstr(program: CoreProgram, options: {
  allowLambdaCallbacks?: boolean;
  /** Match GHC's call-pattern trigger: don't specialize a recursive map when
   * its collection is an unknown variable. */
  requireKnownCollection?: boolean;
} = {}): CoreProgram {
  const loops = collectLoops(program);
  if (loops.size === 0) return program;
  // SpecConstr's local collector still keys its auxiliary map by unique;
  // ordinary inlining uses Binder identity (uniques collide after flattening).
  const candidates = new Map<number, Candidate>();
  const candidatesByBinder = new Map<Binder, Candidate>();
  const candidatesByName = new Map<string, Candidate>();
  for (const b of program.binds) {
    if (b.tag === "NonRec") {
      // Include top-level wrappers that ordinary inlining rejected because a
      // later argument is nontrivial; the bridge below may expose a recursive
      // loop inside them without making them general inlining candidates.
      collectCandidates({ tag: "Let", bind: { tag: "NonRec", binder: b.binder, rhs: b.rhs }, body: { tag: "Var", binder: b.binder } }, candidates, candidatesByBinder, candidatesByName);
      collectCandidates(b.rhs, candidates, candidatesByBinder, candidatesByName);
    } else b.pairs.forEach(([, rhs]) => collectCandidates(rhs, candidates, candidatesByBinder, candidatesByName));
  }

  const topLevel = new Set<Binder>();
  for (const b of program.binds) {
    if (b.tag === "NonRec") topLevel.add(b.binder);
    else b.pairs.forEach(([binder]) => topLevel.add(binder));
  }

  const extra: CoreBind[] = [];
  // SpecConstr is deliberately opportunistic here. A large application can
  // contain thousands of higher-order recursive helpers (especially after
  // imported modules regain their defining namespaces); cloning all of them
  // is worse than leaving the cold generic call in place and can exhaust the
  // host stack before STG generation. Keep enough room for the vtree/map path
  // while making the pass have a deterministic size bound.
  const MAX_SPECIALISATIONS = 8;
  let specialisationCount = 0;
  // Uniques are only module-local; imported modules can reuse them. Keep the
  // memo keyed by the actual function binders, just like loop discovery.
  const made = new Map<Binder, Map<Binder, Binder>>();
  const candidateFor = (binder: Binder, local?: Map<number, Candidate>): Candidate | undefined =>
    local?.get(binder.unique) ?? candidatesByBinder.get(binder) ?? candidates.get(binder.unique) ?? candidatesByName.get(binder.name);
  const specialise = (loop: Loop, fBinder: Binder, local?: Map<number, Candidate>): { binder: Binder; rhs: CoreExpr; hoisted: boolean } | undefined => {
    if (specialisationCount >= MAX_SPECIALISATIONS) return undefined;
    // Binder uniques are only module-local and can collide after imported
    // modules are flattened. The exact Binder object is the identity of the
    // function value at this call site; using the unique alone specialized
    // `map` with an unrelated `a1` binding and produced an invalid closure.
    // Flattening and Core rewrites may clone a local reference while keeping
    // its module-local unique. Prefer object identity, but recover the
    // defining candidate by unique when the reference is such a clone. This
    // is safe here because `candidates` is collected from this one flattened
    // program and the object-identity map still wins when imported uniques
    // collide.
    const candidate = candidateFor(fBinder, local);
    if (!candidate) return undefined;
    if (candidate.params.length !== 1) return undefined; // `f y`: unary only, see module doc
    // vtree's row builder is larger than the tiny corpus callback, but GHC
    // still specializes it because it is the callback of the demanded map.
    // Keep a finite limit to avoid cloning large parser callbacks wholesale.
    if (exprSize(candidate.body) > 320) return undefined;

    const free = [...coreFreeVars(candidate.body, new Set(candidate.params))];
    // Imported/primitive references can be represented without a Binder while
    // the frontend is still being normalized. Do not clone such a callback:
    // specialization must never manufacture an invalid Core `Var`.
    if (free.some((b) => !b)) return undefined;
    // Binder uniques can collide after imported modules are flattened. Do not
    // infer safe top-level hoisting from that numeric identity; only a clone
    // with no captured variables can be safely promoted here.
    const hoisted = free.every((b) => topLevel.has(b));
    if (hoisted) {
      const existing = made.get(loop.binder)?.get(fBinder);
      if (existing) return { binder: existing, rhs: candidate.body, hoisted: true };
    }

    const clone = mkBinder(`$s${loop.binder.name}_${fBinder.name}`);
    specialisationCount++;
    clone.exported = false;
    clone.internal = true;
    const freshParams = loop.params.filter((_, i) => i !== loop.funcParamIndex).map((p) => mkBinder(p.name));
    // A local specialization must not retain the callback's environment as a
    // closure payload. Lambda-lift those captures into the recursive worker,
    // as GHC does for vtree's model-dependent row builder.
    // Top-level references remain ordinary globals in the specialized worker;
    // only bindings owned by the enclosing local scope need lambda lifting.
    // Capturing globals here needlessly turns a compact worker into a large
    // closure and prevents the STG backend from matching GHC's worker shape.
    const captures = hoisted ? [] : free.filter((p) => !topLevel.has(p));
    const captureParams = captures.map((p) => mkBinder(p.name));
    const sub = new Map<number | Binder, CoreExpr>();
    let j = 0;
    loop.params.forEach((p, i) => {
      if (i !== loop.funcParamIndex) sub.set(p, { tag: "Var", binder: freshParams[j++]! });
    });
    if (!hoisted) captures.forEach((p, i) => sub.set(p, { tag: "Var", binder: captureParams[i]! }));
    const renamed = copy(loop.body, sub, new Map());
    const substituted = substituteParam(renamed, loop.params[loop.funcParamIndex]!, candidate, sub);
    const redirected = redirectSelfCalls(substituted, loop, clone, loop.funcParamIndex, captureParams);

    const rhs = mkLams([...freshParams, ...captureParams], redirected);
    if (hoisted) {
      let byCandidate = made.get(loop.binder);
      if (!byCandidate) {
        byCandidate = new Map<Binder, Binder>();
        made.set(loop.binder, byCandidate);
      }
      byCandidate.set(fBinder, clone);
      // The clone's recursive calls were redirected to `clone`, so even a
      // top-level specialization is recursive. Emitting NonRec leaves its
      // closure uninitialized when the generated JS entry is built.
      extra.push({ tag: "Rec", pairs: [[clone, rhs]] });
    }
    return { binder: clone, rhs, hoisted };
  };

  const go = (e: CoreExpr, local = new Map<number, Candidate>()): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App": {
        const { head, args } = spine(e);
        const done = args.map((a) => go(a, local));
        // The list Functor method can survive dictionary lowering as a direct
        // (<$>) application.  Expose its defining map before looking for a
        // recursive call; otherwise the callback remains hidden behind the
        // class method and SpecConstr never sees the call pattern.
        if (
          head.tag === "Var" && head.binder?.name === "<$>" &&
          ((done.length === 3 && done[0]?.tag === "Var" && done[0].binder?.name === "$fFunctorList") || done.length === 2)
        ) {
          const mapLoop = [...loops.values()].find((l) => l.binder.name === "map");
          if (mapLoop) {
            const mapArgs = done.length === 3 ? [done[1]!, done[2]!] : done;
            return go(mkApps({ tag: "Var", binder: mapLoop.binder }, mapArgs), local);
          }
        }
        if (head.tag === "Var") {
          const loop = loops.get(head.binder);
          if (loop && done.length === loop.params.length) {
            const collectionArgs = done.filter((_, i) => i !== loop.funcParamIndex);
            if (options.requireKnownCollection && collectionArgs.every((a) => a.tag === "Var"))
              return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head));
            const fArg = done[loop.funcParamIndex]!;
            if (fArg.tag === "Var") {
              const clone = specialise(loop, fArg.binder, local);
              if (clone) {
                const call = mkApps({ tag: "Var", binder: clone.binder }, [
                  ...done.filter((_, i) => i !== loop.funcParamIndex),
                  ...(clone.hoisted ? [] : [...coreFreeVars(candidateFor(fArg.binder, local)!.body, new Set(candidateFor(fArg.binder, local)!.params))].filter((b): b is Binder => !!b && !topLevel.has(b)).map((b) => ({ tag: "Var" as const, binder: b }))),
                ]);
                return clone.hoisted ? call : {
                  tag: "Let",
                  bind: { tag: "Rec", pairs: [[clone.binder, clone.rhs]] },
                  body: call,
                };
              }
            } else if (options.allowLambdaCallbacks !== false && fArg.tag === "Lam") {
              // Sections and explicit lambdas are already values in Core,
              // but have no top-level binder for the candidate table. Give a
              // unary lambda a temporary identity and run the same
              // capture-avoiding specialization path used for named helpers.
              const lambdaBinder = mkBinder("$lambda");
              const lambdaBody = fArg.body;
              const lambdaCandidate = { params: [fArg.binder], body: lambdaBody };
              candidatesByBinder.set(lambdaBinder, lambdaCandidate);
              const clone = specialise(loop, lambdaBinder);
              candidatesByBinder.delete(lambdaBinder);
              if (clone) {
                const call = mkApps({ tag: "Var", binder: clone.binder }, done.filter((_, i) => i !== loop.funcParamIndex));
                return clone.hoisted ? call : {
                  tag: "Let",
                  bind: { tag: "Rec", pairs: [[clone.binder, clone.rhs]] },
                  body: call,
                };
              }
            }
          }
        }
        // Dictionary specialization can leave a small higher-order wrapper
        // such as `$s<$>$FunctorList` around the real recursive `map` call.
        // Its function argument is known, but its list argument is not a
        // trivial value, so ordinary call inlining intentionally leaves it
        // alone. Inline this wrapper only when its body visibly contains one
        // of the recursive loops we specialize; each parameter must occur at
        // most once, so the rewrite does not duplicate work.
        if (head.tag === "Var") {
          const wrapper = candidatesByBinder.get(head.binder);
          if (wrapper && wrapper.params.length === done.length && done[0]?.tag === "Var") {
            const loopCall = (x: CoreExpr): boolean => {
              if (x.tag === "App") {
                const { head: h } = spine(x);
                if (h.tag === "Var" && loops.has(h.binder)) return true;
                return loopCall(x.fn) || loopCall(x.arg);
              }
              if (x.tag === "Lam") return loopCall(x.body);
              if (x.tag === "Let") return loopCall(x.body) || (x.bind.tag === "NonRec" ? loopCall(x.bind.rhs) : x.bind.pairs.some(([, r]) => loopCall(r)));
              if (x.tag === "Case") return loopCall(x.scrutinee) || x.alts.some((a) => loopCall(a.body));
              if (x.tag === "Con" || x.tag === "Op") return x.args.some(loopCall);
              return false;
            };
            const expose = loopCall(wrapper.body) || head.binder.name.includes("FunctorList");
            if (expose) {
              // Imported/flattened Core can reuse uniques. `copy` accepts
              // Binder keys precisely so this bridge preserves lexical
              // identity instead of substituting an unrelated parameter with
              // the same numeric unique.
              const sub = new Map<number | Binder, CoreExpr>();
              wrapper.params.forEach((p, i) => sub.set(p, done[i]!));
              return go(copy(wrapper.body, sub, new Map()));
            }
          }
        }
        return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head, local));
      }
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: go(e.body, local) };
      case "Let": {
        const next = new Map(local);
        const add = (binder: Binder, rhs: CoreExpr): void => {
          const params: Binder[] = [];
          let body = rhs;
          while (body.tag === "Lam") { params.push(body.binder); body = body.body; }
          if (params.length > 0 && ![...coreFreeVars(body, new Set(params))].some((v) => v.unique === binder.unique))
            next.set(binder.unique, { params, body });
        };
        if (e.bind.tag === "NonRec") add(e.bind.binder, e.bind.rhs);
        const bind: CoreBind =
          e.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: e.bind.binder, rhs: go(e.bind.rhs, local) }
            : { tag: "Rec", pairs: e.bind.pairs.map(([bd, r]) => [bd, go(r, local)] as [Binder, CoreExpr]) };
        return { tag: "Let", bind, body: go(e.body, next) };
      }
      case "Case": {
        const alts: CoreAlt[] = e.alts.map((a) => ({ ...a, body: go(a.body, local) }));
        return { tag: "Case", scrutinee: go(e.scrutinee, local), binder: e.binder, alts };
      }
      case "Con":
        return { tag: "Con", con: e.con, args: e.args.map((a) => go(a, local)) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((a) => go(a, local)) };
    }
  };

  const binds = program.binds.map((b) =>
    b.tag === "NonRec"
      ? { tag: "NonRec" as const, binder: b.binder, rhs: go(b.rhs) }
      : { tag: "Rec" as const, pairs: b.pairs.map(([bd, r]) => [bd, go(r)] as [Binder, CoreExpr]) },
  );
  return extra.length ? { ...program, binds: [...extra, ...binds] } : { ...program, binds };
}
