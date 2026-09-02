/** Core-to-Core: inline saturated calls to small non-recursive top-level
 * functions whose arguments are all trivial.
 *
 * This is the narrow, always-safe corner of GHC's Simplifier - the case its
 * `Note [Pre/postInlineUnconditionally]` calls a trivial argument, where
 * substitution cannot duplicate work because there is no work to duplicate.
 *
 * It exists because a class method at a known type is already resolved to the
 * instance's own binding by `elaborate`, but that binding is still a separate
 * function that has to be entered. `acc + n` at `Int` desugars to
 *
 *     $cNumInt$+ acc n
 *
 * where `$cNumInt$+ = \a b -> case a of I x -> case b of I y -> I (x +# y)`,
 * so every `Int` addition costs a call, an argument-passing sequence and a
 * four-frame continuation chain before it reaches the primop it is made of.
 * GHC never pays that: `Specialise` plus the Simplifier turn the same Core
 * into the `case`/primop body in place. Inlining the callee here is that
 * transformation, arrived at from the other side.
 *
 * WHAT KEEPS THIS SEMANTICS-PRESERVING
 *
 *   - Only saturated calls. An under-applied call would change arity, and
 *     with it the closure a partial application allocates.
 *   - Only trivial arguments (`Var`/`Lit`) or cheap constructors (`I 1`,
 *     nullary cons). Substituting those can duplicate an allocation but not
 *     work, so laziness, exception timing and bottom timing are untouched.
 *   - Only non-recursive callees, checked through the whole call graph, so
 *     the rewrite always terminates.
 *   - Only small bodies, so the emitted code cannot blow up.
 *   - Every binder in the inlined copy is renamed to a fresh unique, so a
 *     body that shadows one of the argument names cannot capture it.
 *
 * What it deliberately does NOT do is unbox anything. The `I` box survives
 * the rewrite; removing it needs demand analysis and worker/wrapper.
 */
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "../core.js";
import { coreFreeVars, mkLams } from "../core.js";
import { mkBinder, type Binder } from "../stg.js";

/** Bodies above this many nodes are left alone. A class method at a known
 * type - two `case`s around one primop - is about eight. Instance methods on
 * the view/JSON path are larger than that and still worth inlining once
 * Specialise has closed their types. */
const MAX_BODY = 48;
const MAX_METHOD = 120;

/** A callee we are willing to inline: `params.length` leading lambdas with
 * `body` underneath. */
export interface Candidate {
  params: Binder[];
  body: CoreExpr;
  /** Explicit source INLINE pragma; permits GHC's larger method budget. */
  inline?: boolean;
}

const size = (e: CoreExpr): number => {
  switch (e.tag) {
    case "Var":
    case "Lit":
      return 1;
    case "App":
      return 1 + size(e.fn) + size(e.arg);
    case "Lam":
      return 1 + size(e.body);
    case "Let":
      return 1 + bindSize(e.bind) + size(e.body);
    case "Case":
      return 1 + size(e.scrutinee) + e.alts.reduce((n, a) => n + size(a.body), 0);
    case "Con":
    case "Op":
      return 1 + e.args.reduce((n, a) => n + size(a), 0);
  }
};
const bindSize = (b: CoreBind): number =>
  b.tag === "NonRec" ? size(b.rhs) : b.pairs.reduce((n, [, r]) => n + size(r), 0);

/** Every top-level binder the expression mentions, for the recursion check. */
function refs(e: CoreExpr, out: Set<number>): void {
  switch (e.tag) {
    case "Var":
      out.add(e.binder.unique);
      return;
    case "Lit":
      return;
    case "App":
      refs(e.fn, out);
      refs(e.arg, out);
      return;
    case "Lam":
      refs(e.body, out);
      return;
    case "Let":
      if (e.bind.tag === "NonRec") refs(e.bind.rhs, out);
      else for (const [, r] of e.bind.pairs) refs(r, out);
      refs(e.body, out);
      return;
    case "Case":
      refs(e.scrutinee, out);
      for (const a of e.alts) refs(a.body, out);
      return;
    case "Con":
    case "Op":
      for (const a of e.args) refs(a, out);
      return;
  }
}

function refBinders(e: CoreExpr, out: Set<Binder>): void {
  switch (e.tag) {
    case "Var": out.add(e.binder); return;
    case "Lit": return;
    case "App": refBinders(e.fn, out); refBinders(e.arg, out); return;
    case "Lam": refBinders(e.body, out); return;
    case "Let":
      if (e.bind.tag === "NonRec") refBinders(e.bind.rhs, out);
      else for (const [, r] of e.bind.pairs) refBinders(r, out);
      refBinders(e.body, out); return;
    case "Case":
      refBinders(e.scrutinee, out); for (const a of e.alts) refBinders(a.body, out); return;
    case "Con":
    case "Op": for (const a of e.args) refBinders(a, out); return;
  }
}

export const isTrivial = (e: CoreExpr): boolean => e.tag === "Var" || e.tag === "Lit";

/** Already in weak head normal form, so substituting it can duplicate an
 * allocation but never any work: a saturated constructor whose fields are
 * themselves trivial. `I 1`, the second argument of every `n - 1`, is the
 * case that matters. Nullary and unboxable constructors are free to
 * duplicate on this backend - an `I` is the number itself. */
export const isCheapValue = (e: CoreExpr): boolean => {
  if (e.tag !== "Con" || !e.args.every(isTrivial)) return false;
  return e.args.length === 0 || e.args.length === 1;
};

const isMethodName = (name: string): boolean =>
  name.startsWith("$c") || name.startsWith("$f") && name.includes("_$c") || name.startsWith("$s") || name.startsWith("$dm") || /(?:from|to)JS(?:Val|Value)/.test(name);

/** Primitive Int operators are strict in all their arguments.  GHC's
 * simplifier can therefore float a non-trivial nested operator into a let
 * before unfolding the outer operator. */
const isStrictIntMethod = (name: string): boolean =>
  /^\$fNumInt_\$c(?:[+*\-/])$/.test(name) || /^\$cNumInt\$(?:[+*\-/])$/.test(name) ||
  /^\$fOrdInt_\$c(?:[<>]=?|compare)$/.test(name) || /^\$cOrdInt\$(?:[<>]=?|compare)$/.test(name);




/** Workers are what worker/wrapper just created: the big, boxed-argument-free
 * half. GHC gives the *wrapper* the INLINE unfolding and leaves the worker
 * alone; inlining the worker back into its wrapper would undo the pass. */
const isWorkerName = (name: string): boolean => name.startsWith("$w");

/** Substitute, renaming every binder the copy introduces. `sub` maps a
 * unique to the expression replacing it; `fresh` maps a unique to the binder
 * replacing it. */
export function copy(e: CoreExpr, sub: Map<number | Binder, CoreExpr>, fresh: Map<number, Binder>): CoreExpr {
  /** A renaming that reaches only where the new binders are in scope.
   *
   * `fresh` used to be one map mutated for the whole walk, which is only sound
   * while every binder in the copied body has a unique nobody else shares.
   * They do not: a desugared module already binds the same unique at more than
   * one site, and specialising copies bodies that share more. One flat map then
   * hands a reference in one branch the binder minted for another, and the name
   * it points at exists nowhere - `h$$mainZCMainzizuzupatternzu90_u_a812 is not
   * defined`, thrown out of `dispatchMainThreadEvent` on the first swipe.
   * Extending a copy per scope is what makes the renaming capture-avoiding. */
  const extend = (bs: Binder[], from: Map<number, Binder>) => {
    const out = new Map(from);
    const binders = bs.map((b) => {
      const nb: Binder = { ...b, unique: mkBinder(b.name).unique };
      out.set(b.unique, nb);
      return nb;
    });
    return { fresh: out, binders };
  };
  switch (e.tag) {
    case "Var": {
      // An inner binding shadows a parameter, so the renaming is asked first.
      const f = fresh.get(e.binder.unique);
      if (f) return { tag: "Var", binder: f };
      return sub.get(e.binder) ?? sub.get(e.binder.unique) ?? e;
    }
    case "Lit":
      return e;
    case "App":
      return { tag: "App", fn: copy(e.fn, sub, fresh), arg: copy(e.arg, sub, fresh) };
    case "Lam": {
      const { fresh: inner, binders } = extend([e.binder], fresh);
      return { tag: "Lam", binder: binders[0]!, body: copy(e.body, sub, inner) };
    }
    case "Let": {
      if (e.bind.tag === "NonRec") {
        const rhs = copy(e.bind.rhs, sub, fresh);
        const { fresh: inner, binders } = extend([e.bind.binder], fresh);
        return { tag: "Let", bind: { tag: "NonRec", binder: binders[0]!, rhs }, body: copy(e.body, sub, inner) };
      }
      // Recursive group: the binders scope over their own right-hand sides,
      // so they have to be renamed before any of them is copied.
      const { fresh: inner, binders } = extend(e.bind.pairs.map(([b]) => b), fresh);
      const pairs = e.bind.pairs.map(([, r], i) => [binders[i]!, copy(r, sub, inner)] as [Binder, CoreExpr]);
      return { tag: "Let", bind: { tag: "Rec", pairs }, body: copy(e.body, sub, inner) };
    }
    case "Case": {
      const scrutinee = copy(e.scrutinee, sub, fresh);
      const { fresh: scoped, binders: bound } = extend([e.binder], fresh);
      const alts: CoreAlt[] = e.alts.map((a) => {
        const { fresh: inner, binders } = extend(a.binders, scoped);
        return { con: a.con, binders, body: copy(a.body, sub, inner) };
      });
      return { tag: "Case", scrutinee, binder: bound[0]!, alts };
    }
    case "Con":
      return { tag: "Con", con: e.con, args: e.args.map((a) => copy(a, sub, fresh)) };
    case "Op":
      return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((a) => copy(a, sub, fresh)) };
  }
}

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

/** Every top-level, non-recursive, small-enough binding, by its own unique -
 * the set `inlineKnownCalls` substitutes at a saturated call site, and the
 * set `src/core-opt/specconstr.ts` substitutes into a higher-order loop's
 * function parameter. Shared so both passes agree on what "known and small"
 * means, and so a program that changes the size cap only has to change it
 * once. */
export function collectInlineCandidates(program: CoreProgram): Map<Binder, Candidate> {
  // Only top-level non-recursive bindings are candidates, and only those
  // whose own right-hand side does not reach back to any of them.
  const tops = new Map<Binder, { rhs: CoreExpr; name: string }>();
  for (const b of program.binds)
    if (b.tag === "NonRec") tops.set(b.binder, { rhs: b.rhs, name: b.binder.name });

  const reaches = new Map<Binder, Set<Binder>>();
  for (const [binder, { rhs }] of tops) {
    const s = new Set<Binder>();
    refBinders(rhs, s);
    reaches.set(binder, s);
  }
  // Transitive closure over the candidate set, so a mutually recursive pair
  // is excluded even though neither names itself.
  for (let changed = true; changed; ) {
    changed = false;
    for (const [binder, s] of reaches)
      for (const v of [...s]) {
        const t = reaches.get(v);
        if (!t) continue;
        for (const w of t)
          if (!s.has(w)) {
            s.add(w);
            changed = true;
          }
      }
  }

  const candidates = new Map<Binder, Candidate>();
  for (const [binder, { rhs, name }] of tops) {
    if (reaches.get(binder)?.has(binder)) continue;
    if (isWorkerName(name)) continue;
    const params: Binder[] = [];
    let body = rhs;
    while (body.tag === "Lam") {
      params.push(body.binder);
      body = body.body;
    }
    if (params.length === 0) continue;
    const inline = binder.inline === true;
    if (size(body) > (inline || isMethodName(name) ? MAX_METHOD : MAX_BODY)) continue;
    candidates.set(binder, { params, body, ...(inline ? { inline: true } : {}) });
  }
  return candidates;
}

export function inlineKnownCalls(
  program: CoreProgram,
  options: { preserveUnreferencedTopLevelBodies?: boolean; roots?: readonly string[] } = {},
): CoreProgram {
  const candidates = collectInlineCandidates(program);
  // Core rewrites may clone a reference binder while preserving its unique.
  // Candidate membership is therefore keyed by unique as well as object
  // identity; otherwise a specialized method is visible in the top-level
  // environment but its call sites silently miss the inline rule.
  const candidatesByUnique = new Map<number, Candidate>();
  for (const [binder, candidate] of candidates) candidatesByUnique.set(binder.unique, candidate);

  // GHC does not spend simplifier budget rewriting the RHS of an exported
  // binding that has no local use.  In particular, the corpus' `add` binding
  // is deliberately uncalled (`main = pure ()`): expanding its Num method
  // changes the binding's observable STG head from a dictionary call to a
  // case, without helping any call site.  Keep this policy opt-in so the
  // standalone pass remains useful for focused Core tests.
  const referenced = new Set<number>();
  if (options.roots) {
    const byBinder = new Map<Binder, CoreExpr>();
    for (const b of program.binds) {
      if (b.tag === "NonRec") byBinder.set(b.binder, b.rhs);
      else for (const [binder, rhs] of b.pairs) byBinder.set(binder, rhs);
    }
    const queue = [...byBinder.keys()].filter((b) => options.roots!.includes(b.name));
    const live = new Set<Binder>();
    while (queue.length) {
      const binder = queue.pop()!;
      if (live.has(binder)) continue;
      live.add(binder);
      referenced.add(binder.unique);
      for (const ref of refBindersIn(byBinder.get(binder)!)) if (byBinder.has(ref)) queue.push(ref);
    }
  } else if (options.preserveUnreferencedTopLevelBodies) {
    for (const b of program.binds) {
      const pairs = b.tag === "NonRec" ? [[b.binder, b.rhs] as const] : b.pairs;
      for (const [, rhs] of pairs) {
        const seen = new Set<number>();
        refs(rhs, seen);
        for (const u of seen) referenced.add(u);
      }
    }
  }

  const go = (e: CoreExpr, demanded = true, lazyBoundary = false): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App": {
        const { head, args } = spine(e);
        const done = args.map((arg) => go(arg, false, lazyBoundary));
        if (head.tag === "Var" && head.binder) {
          const c = candidates.get(head.binder) ?? candidatesByUnique.get(head.binder.unique);
          // Only trivial arguments, or ones that are already values. Binding a
          // non-trivial argument with a `let` and inlining anyway is what GHC
          // does, and it is worth roughly a millisecond a tap here - but it
          // also stopped every tap on the device from reaching its handler,
          // and a faster app that ignores the user is not faster.
          const substitutable =
            c !== undefined &&
            c.params.length === done.length &&
            done.every((a) => isTrivial(a) || isCheapValue(a));
          // A known function applied to only a trivial prefix can be
          // specialized without changing the original function's ABI.  This
          // is GHC's small partial-application unfolding (`plus1 = add 1`):
          // retain the remaining lambdas, but substitute the supplied prefix.
          if (
            c && done.length > 0 && done.length < c.params.length &&
            done.every((a) => isTrivial(a) || isCheapValue(a)) &&
            (!lazyBoundary || isMethodName(head.binder.name))
          ) {
            const sub = new Map<number, CoreExpr>();
            done.forEach((arg, i) => sub.set(c.params[i]!.unique, arg));
            return mkLams(c.params.slice(done.length), copy(c.body, sub, new Map()));
          }
          // A lazy binding must remain a thunk, but inlining a known strict
          // method inside that thunk is still semantics-preserving: it changes
          // only the thunk's payload, not when the payload is entered. GHC's
          // simplifier performs this rewrite for boxed numeric methods, which
          // is what exposes the cases/primop to CPR and worker/wrapper.
          if ((!lazyBoundary || isMethodName(head.binder.name)) && c && substitutable && (demanded || isMethodName(head.binder.name))) {
            const sub = new Map<number, CoreExpr>();
            c.params.forEach((p, i) => {
              sub.set(p.unique, done[i]!);
            });
            return go(copy(c.body, sub, new Map()), demanded);
          }
          if (c && isStrictIntMethod(head.binder.name) && c.params.length === done.length && (demanded || done.some((a) => a.tag === "Case")) && !lazyBoundary) {
            const sub = new Map<number, CoreExpr>();
            const lets: Array<{ binder: Binder; rhs: CoreExpr }> = [];
            c.params.forEach((p, i) => {
              const arg = done[i]!;
              if (isTrivial(arg) || isCheapValue(arg)) sub.set(p.unique, arg);
              else {
                const binder = mkBinder("$inline");
                lets.push({ binder, rhs: arg });
                sub.set(p.unique, { tag: "Var", binder });
              }
            });
            let body = go(copy(c.body, sub, new Map()), demanded);
            for (let i = lets.length - 1; i >= 0; i--) {
              const let_ = lets[i]!;
              body = { tag: "Let", bind: { tag: "NonRec", binder: let_.binder, rhs: let_.rhs }, body };
            }
            return body;
          }
        }
        return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head, true, false));
      }
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: go(e.body, true, false) };
      case "Let": {
        const bind: CoreBind =
          e.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: e.bind.binder, rhs: go(e.bind.rhs, false, true) }
            : { tag: "Rec", pairs: e.bind.pairs.map(([b, r]) => [b, go(r, false, true)] as [Binder, CoreExpr]) };
        return { tag: "Let", bind, body: go(e.body, demanded, lazyBoundary) };
      }
      case "Case":
        return {
          tag: "Case",
          scrutinee: go(e.scrutinee, true, false),
          binder: e.binder,
          alts: e.alts.map((a) => ({ ...a, body: go(a.body, demanded, lazyBoundary) })),
        };
      case "Con":
        return { tag: "Con", con: e.con, args: e.args.map((arg) => go(arg, false, true)) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((arg) => go(arg, true, false)) };
    }
  };

  return {
    ...program,
    binds: program.binds.map((b) =>
      b.tag === "NonRec"
        ? { tag: "NonRec", binder: b.binder, rhs: options.preserveUnreferencedTopLevelBodies && !referenced.has(b.binder.unique) ? b.rhs : go(b.rhs) }
        : { tag: "Rec", pairs: b.pairs.map(([bd, r]) => [bd, go(r)] as [Binder, CoreExpr]) },
    ),
  };
}

function refBindersIn(e: CoreExpr): Set<Binder> {
  const out = new Set<Binder>();
  refBinders(e, out);
  return out;
}
