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
import { mkBinder, type Binder } from "../stg.js";

/** Bodies above this many nodes are left alone. A class method at a known
 * type - two `case`s around one primop - is about eight. Instance methods on
 * the view/JSON path are larger than that and still worth inlining once
 * Specialise has closed their types. */
const MAX_BODY = 48;
const MAX_METHOD = 120;

/** A callee we are willing to inline: `params.length` leading lambdas with
 * `body` underneath. */
interface Candidate {
  params: Binder[];
  body: CoreExpr;
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

const isTrivial = (e: CoreExpr): boolean => e.tag === "Var" || e.tag === "Lit";

/** Already in weak head normal form, so substituting it can duplicate an
 * allocation but never any work: a saturated constructor whose fields are
 * themselves trivial. `I 1`, the second argument of every `n - 1`, is the
 * case that matters. Nullary and unboxable constructors are free to
 * duplicate on this backend - an `I` is the number itself. */
const isCheapValue = (e: CoreExpr): boolean => {
  if (e.tag !== "Con" || !e.args.every(isTrivial)) return false;
  return e.args.length === 0 || e.args.length === 1;
};

const isMethodName = (name: string): boolean =>
  name.startsWith("$c") || name.startsWith("$s") || name.startsWith("$dm");

/** Workers are what worker/wrapper just created: the big, boxed-argument-free
 * half. GHC gives the *wrapper* the INLINE unfolding and leaves the worker
 * alone; inlining the worker back into its wrapper would undo the pass. */
const isWorkerName = (name: string): boolean => name.startsWith("$w");

/** Substitute, renaming every binder the copy introduces. `sub` maps a
 * unique to the expression replacing it; `fresh` maps a unique to the binder
 * replacing it. */
export function copy(e: CoreExpr, sub: Map<number, CoreExpr>, fresh: Map<number, Binder>): CoreExpr {
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
      return sub.get(e.binder.unique) ?? e;
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

export function inlineKnownCalls(program: CoreProgram): CoreProgram {
  // Only top-level non-recursive bindings are candidates, and only those
  // whose own right-hand side does not reach back to any of them.
  const tops = new Map<number, { rhs: CoreExpr; name: string }>();
  for (const b of program.binds)
    if (b.tag === "NonRec") tops.set(b.binder.unique, { rhs: b.rhs, name: b.binder.name });

  const reaches = new Map<number, Set<number>>();
  for (const [u, { rhs }] of tops) {
    const s = new Set<number>();
    refs(rhs, s);
    reaches.set(u, s);
  }
  // Transitive closure over the candidate set, so a mutually recursive pair
  // is excluded even though neither names itself.
  for (let changed = true; changed; ) {
    changed = false;
    for (const [u, s] of reaches)
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

  const candidates = new Map<number, Candidate>();
  for (const [u, { rhs, name }] of tops) {
    if (reaches.get(u)?.has(u)) continue;
    if (isWorkerName(name)) continue;
    const params: Binder[] = [];
    let body = rhs;
    while (body.tag === "Lam") {
      params.push(body.binder);
      body = body.body;
    }
    if (params.length === 0) continue;
    if (size(body) > (isMethodName(name) ? MAX_METHOD : MAX_BODY)) continue;
    candidates.set(u, { params, body });
  }

  const go = (e: CoreExpr): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App": {
        const { head, args } = spine(e);
        const done = args.map(go);
        if (head.tag === "Var") {
          const c = candidates.get(head.binder.unique);
          // Only trivial arguments, or ones that are already values. Binding a
          // non-trivial argument with a `let` and inlining anyway is what GHC
          // does, and it is worth roughly a millisecond a tap here - but it
          // also stopped every tap on the device from reaching its handler,
          // and a faster app that ignores the user is not faster.
          const substitutable =
            c !== undefined &&
            c.params.length === done.length &&
            done.every((a) => isTrivial(a) || isCheapValue(a));
          if (c && substitutable) {
            const sub = new Map<number, CoreExpr>();
            c.params.forEach((p, i) => sub.set(p.unique, done[i]!));
            return go(copy(c.body, sub, new Map()));
          }
        }
        return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head));
      }
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
