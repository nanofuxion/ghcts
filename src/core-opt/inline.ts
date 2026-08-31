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
 *   - Only trivial arguments (`Var`/`Lit`). Substituting a variable for a
 *     variable can neither duplicate work nor move evaluation across a
 *     `case`, so laziness, exception timing and bottom timing are untouched
 *     however many times the parameter occurs in the body.
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
 * type - two `case`s around one primop - is about eight. */
const MAX_BODY = 24;

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
 * case that matters. */
const isCheapValue = (e: CoreExpr): boolean => e.tag === "Con" && e.args.every(isTrivial);

/** How many times the binder occurs. GHC's `preInlineUnconditionally` allows
 * a non-trivial argument through only at one occurrence, because a second
 * one would duplicate the allocation; the count stops at two since that is
 * all the decision needs. */
function occurrences(e: CoreExpr, unique: number, seen = { n: 0 }): number {
  if (seen.n > 1) return seen.n;
  switch (e.tag) {
    case "Var":
      if (e.binder.unique === unique) seen.n++;
      return seen.n;
    case "Lit":
      return seen.n;
    case "App":
      occurrences(e.fn, unique, seen);
      return occurrences(e.arg, unique, seen);
    case "Lam":
      return occurrences(e.body, unique, seen);
    case "Let":
      if (e.bind.tag === "NonRec") occurrences(e.bind.rhs, unique, seen);
      else for (const [, r] of e.bind.pairs) occurrences(r, unique, seen);
      return occurrences(e.body, unique, seen);
    case "Case":
      occurrences(e.scrutinee, unique, seen);
      for (const a of e.alts) occurrences(a.body, unique, seen);
      return seen.n;
    case "Con":
    case "Op":
      for (const a of e.args) occurrences(a, unique, seen);
      return seen.n;
  }
}

/** Substitute, renaming every binder the copy introduces. `sub` maps a
 * unique to the expression replacing it; `fresh` maps a unique to the binder
 * replacing it. */
function copy(e: CoreExpr, sub: Map<number, CoreExpr>, fresh: Map<number, Binder>): CoreExpr {
  // `mkBinder` spreads its `extra` last, so the fresh unique has to be read
  // back off the result rather than passed in with the other fields.
  const rename = (b: Binder): Binder => {
    const out: Binder = { ...b, unique: mkBinder(b.name).unique };
    fresh.set(b.unique, out);
    return out;
  };
  switch (e.tag) {
    case "Var": {
      const s = sub.get(e.binder.unique);
      if (s) return s;
      const f = fresh.get(e.binder.unique);
      return f ? { tag: "Var", binder: f } : e;
    }
    case "Lit":
      return e;
    case "App":
      return { tag: "App", fn: copy(e.fn, sub, fresh), arg: copy(e.arg, sub, fresh) };
    case "Lam": {
      const b = rename(e.binder);
      return { tag: "Lam", binder: b, body: copy(e.body, sub, fresh) };
    }
    case "Let": {
      if (e.bind.tag === "NonRec") {
        const rhs = copy(e.bind.rhs, sub, fresh);
        const b = rename(e.bind.binder);
        return { tag: "Let", bind: { tag: "NonRec", binder: b, rhs }, body: copy(e.body, sub, fresh) };
      }
      // Recursive group: the binders scope over their own right-hand sides,
      // so they have to be renamed before any of them is copied.
      const bs = e.bind.pairs.map(([b]) => rename(b));
      const pairs = e.bind.pairs.map(([, r], i) => [bs[i]!, copy(r, sub, fresh)] as [Binder, CoreExpr]);
      return { tag: "Let", bind: { tag: "Rec", pairs }, body: copy(e.body, sub, fresh) };
    }
    case "Case": {
      const scrutinee = copy(e.scrutinee, sub, fresh);
      const binder = rename(e.binder);
      const alts: CoreAlt[] = e.alts.map((a) => {
        const binders = a.binders.map(rename);
        return { con: a.con, binders, body: copy(a.body, sub, fresh) };
      });
      return { tag: "Case", scrutinee, binder, alts };
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
  const tops = new Map<number, CoreExpr>();
  for (const b of program.binds)
    if (b.tag === "NonRec") tops.set(b.binder.unique, b.rhs);

  const reaches = new Map<number, Set<number>>();
  for (const [u, rhs] of tops) {
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
  for (const [u, rhs] of tops) {
    if (reaches.get(u)?.has(u)) continue;
    const params: Binder[] = [];
    let body = rhs;
    while (body.tag === "Lam") {
      params.push(body.binder);
      body = body.body;
    }
    if (params.length === 0) continue;
    if (size(body) > MAX_BODY) continue;
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
          const substitutable =
            c !== undefined &&
            c.params.length === done.length &&
            done.every(
              (a, i) => isTrivial(a) || (isCheapValue(a) && occurrences(c.body, c.params[i]!.unique) <= 1),
            );
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
