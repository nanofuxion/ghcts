/** Core-to-Core: case-of-known-constructor, the Simplifier rule the rest of
 * the pipeline leans on.
 *
 * Once `inlineKnownCalls` has pulled a class method's body into its caller,
 * the result is full of cases that scrutinise something already known to be a
 * constructor. `acc + 1` at `Int` inlines to
 *
 *     case acc of a { I# x -> case I# 1 of b { I# y -> I# (x +# y) } }
 *
 * where the inner `case` allocates a box and takes it apart again in the next
 * breath, and a recursive call further down scrutinises `acc` a second time
 * even though the outer `case` already forced it. GHC never sees either: its
 * `Note [Case of known constructor]` fires as the Simplifier rebuilds the
 * expression, so what reaches STG is the primops alone.
 *
 * Two forms are recognised, and they are the same rule seen from two sides:
 *
 *   - the scrutinee IS a constructor application, so the matching alternative
 *     is the only one that can run;
 *   - the scrutinee is a variable an enclosing `case` already matched, so the
 *     constructor and its fields are in scope and the answer is known.
 *
 * Dropping the `case` in either form removes an evaluation that has already
 * happened, so laziness, exception order and bottoms are unchanged. Fields
 * replace the alternative's binders by substitution when they are trivial and
 * by a `let` when they are not, which keeps work from being duplicated.
 *
 * The pass matters most in front of `workWrap`: a worker can only take a
 * payload if nothing downstream still wants the box, and it is this rule that
 * removes the second look at `acc`.
 */
import { copy } from "./inline.js";
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "../core.js";
import type { Binder, DataCon, Literal } from "../stg.js";
import { isUnboxedTupleCon } from "../stg.js";

/** What an enclosing `case` proved about a variable. `fields` are the
 * expressions its constructor was applied to, already simplified. */
interface Known {
  con: DataCon;
  fields: CoreExpr[];
}

/** What an enclosing scope knew about these uniques no longer applies once a
 * binder reuses one of them: uniques are only unique per desugaring site, so
 * a substitution or a known-constructor fact must stop at the binder that
 * shadows it, exactly as GHC's substitution carries an in-scope set. */
const shadow = <A,>(m: Map<number, A>, binders: readonly Binder[]): Map<number, A> => {
  if (!binders.some((b) => m.has(b.unique))) return m;
  const out = new Map(m);
  for (const b of binders) out.delete(b.unique);
  return out;
};

/** GHC's `exprIsTrivial`, minus the nullary constructor GHC counts.
 *
 * In GHC's Core a nullary constructor IS its worker `Var`, so GHC substitutes
 * one rather than binding it, and `core-to-stg`'s `atom` now spells ghcts's
 * the same way. Doing it here as well - substituting a `let`-bound nullary
 * constructor into the body - is what still leaves nine `h$c0(...True/False)`
 * allocations in the counter that GHC does not make. It is NOT a safe change
 * as the pass stands: it compiles a bundle whose first tap dies in miso's
 * `fromMisoString StaticKey`, while `npm test`, `scripts/hs-run.mjs` and
 * `scripts/stg-diff.mjs` all stay green. Whatever the `let` is carrying that
 * the substituted copies are not, find it before widening this. */
const isTrivial = (e: CoreExpr): boolean => e.tag === "Var" || e.tag === "Lit";

/** GHC's `exprIsDupable`: a term small enough to copy into each branch of a
 * case. Applications, variables, literals and constructors count against
 * `dupAppSize`; a lambda, `let` or `case` is never copied. */
const dupAppSize = 8;
const exprIsDupable = (e: CoreExpr): boolean => {
  const go = (x: CoreExpr, n: number): number => {
    if (n < 0) return n;
    switch (x.tag) {
      case "Var":
      case "Lit":
        return n - 1;
      case "App":
        return go(x.arg, go(x.fn, n) - 1);
      case "Con":
      case "Op":
        return x.args.reduce((m, a) => go(a, m), n - 1);
      default:
        return -1;
    }
  };
  return go(e, dupAppSize) >= 0;
};

const sameLit = (a: Literal, b: Literal): boolean =>
  a.tag === b.tag && (a as { value?: unknown }).value === (b as { value?: unknown }).value;

/** How often the binder is read, and whether any of those reads sit under a
 * lambda - GHC's `OccInfo`, cut down to what `preInlineUnconditionally` asks.
 * A single read outside a lambda can be substituted without duplicating work;
 * anything else has to stay behind a binding. */
export function occInfo(e: CoreExpr, u: number, underLam = false): { count: number; inLam: boolean } {
  const zero = { count: 0, inLam: false };
  const join = (...xs: Array<{ count: number; inLam: boolean }>) => ({
    count: xs.reduce((n, x) => n + x.count, 0),
    inLam: xs.some((x) => x.inLam),
  });
  switch (e.tag) {
    case "Var":
      return e.binder.unique === u ? { count: 1, inLam: underLam } : zero;
    case "Lit":
      return zero;
    case "App":
      return join(occInfo(e.fn, u, underLam), occInfo(e.arg, u, underLam));
    case "Lam":
      return occInfo(e.body, u, true);
    case "Let": {
      const rhs =
        e.bind.tag === "NonRec"
          ? occInfo(e.bind.rhs, u, underLam)
          : join(...e.bind.pairs.map(([, r]) => occInfo(r, u, true)));
      return join(rhs, occInfo(e.body, u, underLam));
    }
    case "Case":
      // Alternatives are exclusive, so the worst branch is the cost, but a
      // binder read in two branches is still read once on any given run.
      return join(
        occInfo(e.scrutinee, u, underLam),
        ...e.alts.map((a) => occInfo(a.body, u, underLam)),
      );
    case "Con":
    case "Op":
      return join(...e.args.map((a) => occInfo(a, u, underLam)));
  }
}

function mentions(e: CoreExpr, u: number): boolean {
  switch (e.tag) {
    case "Var":
      return e.binder.unique === u;
    case "Lit":
      return false;
    case "App":
      return mentions(e.fn, u) || mentions(e.arg, u);
    case "Lam":
      return mentions(e.body, u);
    case "Let":
      return e.bind.tag === "NonRec"
        ? mentions(e.bind.rhs, u) || mentions(e.body, u)
        : e.bind.pairs.some(([, r]) => mentions(r, u)) || mentions(e.body, u);
    case "Case":
      return mentions(e.scrutinee, u) || e.alts.some((a) => mentions(a.body, u));
    case "Con":
    case "Op":
      return e.args.some((a) => mentions(a, u));
  }
}

export function simplifyCore(program: CoreProgram): CoreProgram {
  const topKnown = new Map<number, CoreExpr>();
  for (const b of program.binds) {
    if (b.tag === "NonRec" && b.rhs.tag === "Con" && b.rhs.con.name !== "StaticPtr" &&
        (b.rhs.args.every(isTrivial) || b.rhs.args.length === 0))
      topKnown.set(b.binder.unique, b.rhs);
  }
  /** GHC's Simplifier performs eta reduction on top-level bindings. This is
   * especially important for a monomorphic class-method alias such as
   * `add a b = a + b`: after dictionary resolution its RHS is exactly
   * `($fNumInt_$c+) a b`, so retaining the lambda wrapper changes the entry
   * ABI and prevents the linker from treating `add` as the method value. */
  const etaReduce = (e: CoreExpr): CoreExpr => {
    const params: Binder[] = [];
    let body: CoreExpr = e;
    while (body.tag === "Lam") {
      params.push(body.binder);
      body = body.body;
    }
    let head: CoreExpr = body;
    const args: CoreExpr[] = [];
    while (head.tag === "App") {
      args.unshift(head.arg);
      head = head.fn;
    }
    if (head.tag !== "Var" || args.length !== params.length) return e;
    for (const [arg, param] of args.map((x, i) => [x, params[i]!] as const))
      if (arg.tag !== "Var" || arg.binder !== param) return e;
    return { tag: "Var", binder: head.binder };
  };
  /** Bindings a collapsed `case` still has to make: trivial fields go in
   * `sub` and cost nothing, the rest come back as `let`s around the body. */
  const bindAlt = (
    binders: Binder[],
    fields: CoreExpr[],
    body: CoreExpr,
    sub: Map<number, CoreExpr>,
  ): boolean => {
    const plan: Array<[number, CoreExpr]> = [];
    for (const [i, b] of binders.entries()) {
      const f = fields[i];
      if (f === undefined) return false;
      if (isTrivial(f)) {
        plan.push([b.unique, f]);
        continue;
      }
      // A field can be an unboxed primop result, which no `let` may bind, so
      // the only way to keep it is to substitute - and that is sound just
      // when the alternative reads it once, outside any lambda.
      const occ = occInfo(body, b.unique);
      if (occ.count > 1 || occ.inLam) return false;
      plan.push([b.unique, f]);
    }
    for (const [u, f] of plan) sub.set(u, f);
    return true;
  };

  const wrap = (lets: Array<[Binder, CoreExpr]>, body: CoreExpr): CoreExpr =>
    lets.reduceRight<CoreExpr>(
      (inner, [binder, rhs]) =>
        // A constructor the simplified body no longer reads is an allocation
        // nobody asked for; it does no work and cannot diverge, so it goes.
        rhs.tag === "Con" && !mentions(inner, binder.unique)
          ? inner
          : { tag: "Let", bind: { tag: "NonRec", binder, rhs }, body: inner },
      body,
    );

  const go = (e: CoreExpr, env: Map<number, Known>, sub: Map<number, CoreExpr>): CoreExpr => {
    switch (e.tag) {
      case "Var":
        return e.binder ? (sub.get(e.binder.unique) ?? topKnown.get(e.binder.unique) ?? e) : e;
      case "Lit":
        return e;
      case "App": {
        const fn = go(e.fn, env, sub);
        // Beta reduction. A lambda in head position is what inlining a
        // single-use `\s -> ...` (below) leaves behind; `(\x -> b) a` is
        // `let x = a in b`, and the `let` rule then substitutes a trivial `a`.
        //
        // The lambda's body was simplified where the lambda was written, so
        // it is not walked again here: this site's substitution is keyed by
        // unique, and a desugared module binds the same unique at more than
        // one place, so a second walk under a different scope could capture.
        // A trivial argument is substituted by `copy`, which renames every
        // binder it passes; anything else is let-bound, and the next round
        // of the pipeline picks up what that exposes.
        if (fn.tag === "Lam") {
          const arg = go(e.arg, env, sub);
          return isTrivial(arg)
            ? copy(fn.body, new Map([[fn.binder.unique, arg]]), new Map())
            : { tag: "Let", bind: { tag: "NonRec", binder: fn.binder, rhs: arg }, body: fn.body };
        }
        return { tag: "App", fn, arg: go(e.arg, env, sub) };
      }
      case "Lam": {
        const scope = [e.binder];
        return { tag: "Lam", binder: e.binder, body: go(e.body, shadow(env, scope), shadow(sub, scope)) };
      }
      case "Let": {
        if (e.bind.tag === "Rec") {
          const scope = e.bind.pairs.map(([b]) => b);
          const [recEnv, recSub] = [shadow(env, scope), shadow(sub, scope)];
          const pairs = e.bind.pairs.map(([b, r]) => [b, go(r, recEnv, recSub)] as [Binder, CoreExpr]);
          return { tag: "Let", bind: { tag: "Rec", pairs }, body: go(e.body, recEnv, recSub) };
        }
        const letBinder = e.bind.binder;
        const rhs = go(e.bind.rhs, env, sub);
        const [bodyEnv, bodySub] = [shadow(env, [letBinder]), shadow(sub, [letBinder])];
        // GHC's preInlineUnconditionally: a trivial right-hand side is
        // substituted, never let-bound. It costs nothing to repeat, and a
        // nullary constructor kept in a `let` would be allocated by codegen.
        if (isTrivial(rhs)) return go(e.body, bodyEnv, new Map(bodySub).set(letBinder.unique, rhs));
        const occ = occInfo(e.body, letBinder.unique);
        // GHC's preInlineUnconditionally, the other half: a lambda read
        // exactly once goes to its one use, lambda or no lambda around it -
        // a lambda is a value, so nothing is recomputed, only allocated where
        // it is used instead of where it was written. With IO a newtype this
        // is what turns `let m = \s -> ... in m s` into the body itself.
        if (rhs.tag === "Lam" && occ.count === 1) return go(e.body, bodyEnv, new Map(bodySub).set(letBinder.unique, rhs));
        const single = occ.count <= 1;
        const innerEnv =
          rhs.tag === "Con" && rhs.con.name !== "StaticPtr" && (rhs.args.every(isTrivial) || single)
            ? new Map(bodyEnv).set(letBinder.unique, { con: rhs.con, fields: rhs.args })
            : bodyEnv;
        const body = go(e.body, innerEnv, bodySub);
        // Nothing reads it any more. A `let` is lazy, so a binding nobody
        // forces contributes nothing - not a value, not an exception, not
        // non-termination - and the thunk it would have allocated goes with
        // it. This is GHC's dead-binding elimination.
        if (!mentions(body, letBinder.unique)) return body;
        // A box the worker rebuilt for one cold branch should not be built on
        // every call. A constructor application does no work and cannot
        // diverge, so pushing it into the alternatives that read it is sound,
        // and the branches that do not read it stop paying for it. GHC calls
        // the same move floating a reboxing `let` inwards.
        if (
          rhs.tag === "Con" &&
          rhs.args.every(isTrivial) &&
          body.tag === "Case" &&
          !mentions(body.scrutinee, letBinder.unique) &&
          body.alts.some((a) => !mentions(a.body, letBinder.unique))
        ) {
          const bind: CoreBind = { tag: "NonRec", binder: letBinder, rhs };
          const alts = body.alts.map((a) =>
            mentions(a.body, letBinder.unique)
              ? { ...a, body: { tag: "Let" as const, bind, body: a.body } }
              : a,
          );
          return { tag: "Case", scrutinee: body.scrutinee, binder: body.binder, alts };
        }
        return { tag: "Let", bind: { tag: "NonRec", binder: letBinder, rhs }, body };
      }
      case "Con":
        return { tag: "Con", con: e.con, args: e.args.map((a) => go(a, env, sub)) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((a) => go(a, env, sub)) };
      case "Case": {
        // `case m of f { DEFAULT -> f s }` is `m s`: applying `m` evaluates it
        // first anyway, and `f` names nothing else. The erased `unIO m s`
        // has this shape, and only as an application can `m` be inlined and
        // beta-reduced into a straight-line state step.
        if (e.alts.length === 1 && e.alts[0]!.con.tag === "DEFAULT") {
          const args: CoreExpr[] = [];
          let head = e.alts[0]!.body;
          while (head.tag === "App") { args.unshift(head.arg); head = head.fn; }
          if (args.length > 0 && head.tag === "Var" && head.binder.unique === e.binder.unique && occInfo(e.alts[0]!.body, e.binder.unique).count === 1)
            return go(args.reduce<CoreExpr>((f, arg) => ({ tag: "App", fn: f, arg }), e.scrutinee), env, sub);
        }
        const scrut = go(e.scrutinee, env, sub);
        // A lambda is already a value: `case \x -> b of f { DEFAULT -> e }`
        // evaluates nothing, so it is `let f = \x -> b in e`, where the
        // single-use rule can carry it to its call.
        if (scrut.tag === "Lam" && e.alts.length === 1 && e.alts[0]!.con.tag === "DEFAULT")
          return go({ tag: "Let", bind: { tag: "NonRec", binder: e.binder, rhs: scrut }, body: e.alts[0]!.body }, env, sub);

        // GHC's case-of-case rule: move an outer match into each branch of an
        // inner match. Strict-call forcing produces this shape; reassociating
        // it lets the constructor rule below see the resulting value without
        // evaluating the inner computation twice.
        //
        // Only when the outer alternatives are cheap to copy. GHC duplicates a
        // continuation only if `exprIsDupable` says so (`dupAppSize = 8`) and
        // otherwise makes a join point; copying every time is exponential in
        // the nesting, and misogram's derived `parseJSON` - 61 such sites, 48
        // deep - never finished and ran the heap out.
        if (scrut.tag === "Case") {
          // An unboxed tuple cannot be a function's argument, so a match on
          // one (every IO step) is always distributed; its alternatives are
          // the state-token shapes, small by construction.
          const unboxedTuple = e.alts.some((a) => a.con.tag === "DataAlt" && isUnboxedTupleCon(a.con.con));
          if (unboxedTuple || e.alts.every((a) => exprIsDupable(a.body))) {
            const distributed: CoreExpr = {
              tag: "Case",
              scrutinee: scrut.scrutinee,
              binder: scrut.binder,
              alts: scrut.alts.map((inner) => ({
                ...inner,
                body: {
                  tag: "Case" as const,
                  scrutinee: inner.body,
                  binder: e.binder,
                  alts: e.alts,
                },
              })),
            };
            return go(distributed, env, sub);
          }
          // Otherwise the nested match stays as it is. GHC would bind the outer
          // alternatives as a join point; ghcts's Core has no let-no-escape,
          // and spelling one as an ordinary local function miscompiles the
          // counter (`fromJSValUnchecked: failure` on its first tap) - the
          // wrapper's unboxing case then sits behind a call the
          // case-of-known-constructor rule cannot see through. Core-to-STG
          // distributes a nested case itself when it has to.
        }

        // What the scrutinee is already known to be, from its own shape or
        // from an enclosing `case` on the same variable.
        const known: Known | undefined =
          scrut.tag === "Con"
            ? { con: scrut.con, fields: scrut.args }
            : scrut.tag === "Var" && scrut.binder
              ? env.get(scrut.binder.unique)
              : undefined;

        const chosen =
          known !== undefined
            ? (e.alts.find(
                (a) =>
                  a.con.tag === "DataAlt" &&
                  a.con.con.name === known.con.name &&
                  a.con.con.typeName === known.con.typeName,
              ) ??
              e.alts.find((a) => a.con.tag === "DEFAULT"))
            : scrut.tag === "Lit"
              ? (e.alts.find((a) => a.con.tag === "LitAlt" && sameLit(a.con.lit, scrut.lit)) ??
                e.alts.find((a) => a.con.tag === "DEFAULT"))
              : undefined;

        if (chosen) {
          const scope = [e.binder, ...chosen.binders];
          const inner = new Map(shadow(sub, scope));
          const fields = chosen.con.tag === "DataAlt" && known ? known.fields : [];
          const lets: Array<[Binder, CoreExpr]> = [];
          if (!bindAlt(chosen.binders, fields, chosen.body, inner)) return rebuild(e, scrut, env, sub);
          // The case binder names the evaluated scrutinee. A variable can
          // stand in for it directly; anything else has to keep its `let` so
          // the value is not rebuilt at every use.
          const usesBinder = mentions(chosen.body, e.binder.unique);
          if (usesBinder && isTrivial(scrut)) inner.set(e.binder.unique, scrut);
          else if (usesBinder) lets.push([e.binder, scrut]);
          const innerEnv = new Map(shadow(env, scope));
          if (known) {
            // Record what the alternative's own binders now stand for, not the
            // field expressions themselves: a field that needed a `let` must
            // be reached through that `let`, or a later collapse would copy
            // the work back in. A DEFAULT alternative binds nothing, so the
            // constructor carries straight through - the case binder still
            // names it, and a `case` on that binder further down is answered.
            const proved: Known =
              chosen.con.tag === "DataAlt"
                ? {
                    con: known.con,
                    fields: chosen.binders.map(
                      (b) => inner.get(b.unique) ?? { tag: "Var" as const, binder: b },
                    ),
                  }
                : known;
            // Carrying a non-trivial field through would let a later collapse
            // recompute it, unless the alternative reads the binder once.
            const once = occInfo(chosen.body, e.binder.unique).count <= 1;
            if (chosen.con.tag === "DataAlt" || known.fields.every(isTrivial) || once) {
              if (scrut.tag === "Var" && scrut.binder) innerEnv.set(scrut.binder.unique, proved);
              innerEnv.set(e.binder.unique, proved);
            }
          }
          return wrap(lets, go(chosen.body, innerEnv, inner));
        }

        return rebuild(e, scrut, env, sub);
      }
    }
  };

  /** Keep the `case`, but let each alternative know what its own scrutinee
   * turned out to be. */
  function rebuild(
    e: Extract<CoreExpr, { tag: "Case" }>,
    scrut: CoreExpr,
    env: Map<number, Known>,
    sub: Map<number, CoreExpr>,
  ): CoreExpr {
    const alts: CoreAlt[] = e.alts.map((a) => {
      const scope = [e.binder, ...a.binders];
      const innerEnv = new Map(shadow(env, scope));
      if (a.con.tag === "DataAlt") {
        const proved: Known = {
          con: a.con.con,
          fields: a.binders.map((b) => ({ tag: "Var" as const, binder: b })),
        };
        if (scrut.tag === "Var" && scrut.binder) innerEnv.set(scrut.binder.unique, proved);
        innerEnv.set(e.binder.unique, proved);
      }
      return { ...a, body: go(a.body, innerEnv, shadow(sub, scope)) };
    });
    return { tag: "Case", scrutinee: scrut, binder: e.binder, alts };
  }

  const empty = () => new Map<number, Known>();
  return {
    ...program,
    binds: program.binds.map((b) =>
      b.tag === "NonRec"
        ? { tag: "NonRec", binder: b.binder, rhs: etaReduce(go(b.rhs, empty(), new Map())) }
        : {
            tag: "Rec",
            pairs: b.pairs.map(([bd, r]) => [bd, go(r, empty(), new Map())] as [Binder, CoreExpr]),
          },
    ),
  };
}
