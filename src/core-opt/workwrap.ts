/** Core-to-Core: the unboxing half of GHC's worker/wrapper.
 *
 * `forceStrictArgs` already evaluates strict arguments at the call site, still
 * boxed. This splits a function that takes a boxed `Int`/`Double`/… and only
 * ever takes it apart into a worker that takes the payload and a wrapper that
 * unpacks, so once the wrapper is inlined the payload never re-enters a thunk.
 *
 * WHICH ARGUMENTS
 *
 * The demand signature decides, not the shape of the body. `sumTo acc n`
 * cases `n` first and `acc` several branches down, and GHC unboxes both -
 * `Str=<1!P(L)><1!P(1L)>`. Peeling only the cases at the top of the body
 * would unbox `n` alone and leave the accumulator boxed on every iteration,
 * which is the difference `scripts/stg-diff.mjs` reports as "ghcts allocates
 * more". So an argument is unboxed when `strictness.ts` proves it is always
 * forced AND every use of it in the body is a `case` scrutinee - the second
 * condition is what makes the rebox below free.
 *
 * THE REBOX
 *
 * The worker rebuilds the box it was handed the payload of:
 *
 *     $wsumTo = \acc1 n1 -> let acc = I# acc1 in let n = I# n1 in <body>
 *
 * which looks like it undoes the whole point, and `simplifyCore` MUST run
 * next - not to make this pay off but to make it correct. Left in place, the
 * rebuilt box makes misogram die at startup with `fromJSValUnchecked:
 * failure`; `src/build.ts` therefore refuses to run this pass without the
 * Simplifier behind it. A `let` of a constructor is a known constructor,
 * so every `case acc of I# x -> …` in the body collapses to the payload, and
 * the `let` is then dead and goes. Requiring scrutinee-only uses above is
 * what guarantees that outcome instead of hoping for it. GHC does the same
 * thing for the same reason - see its `Note [Worker/wrapper for
 * strictness]` and the Simplifier pass that follows WW.
 *
 * Recursive groups are skipped: a worker that closed over its own wrapper is
 * easy to get wrong and is not the tap-path shape.
 */
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "../core.js";
import { mkApps, mkLams } from "../core.js";
import { mkBinder, type Binder, type DataCon } from "../stg.js";
import { copy } from "./inline.js";
import { argStrictnessByUnique } from "./strictness.js";

const UNBOXABLE = new Set([
  "Int",
  "Int8",
  "Int16",
  "Int32",
  "Word",
  "Word8",
  "Word16",
  "Word32",
  "Char",
  "Float",
  "Double",
]);

function lambdas(e: CoreExpr): { params: Binder[]; body: CoreExpr } {
  const params: Binder[] = [];
  let body = e;
  while (body.tag === "Lam") {
    params.push(body.binder);
    body = body.body;
  }
  return { params, body };
}

/** The constructor this binder is taken apart with, or `undefined` if it is
 * never scrutinised or is scrutinised in a way that does not unbox.
 *
 * Uses that are not `case` scrutinees are allowed: the branch that returns
 * `acc` unchanged still wants the box, and `simplifyCore` floats the worker's
 * rebuilt box into exactly that branch, so the hot path does not pay for it.
 * GHC makes the same trade under `Note [Reboxing]`. */
function unboxedWith(body: CoreExpr, u: number): DataCon | undefined {
  let con: DataCon | undefined;
  let ok = true;
  const go = (e: CoreExpr): void => {
    if (!ok) return;
    switch (e.tag) {
      case "Var":
      case "Lit":
        return;
      case "App":
        go(e.fn);
        go(e.arg);
        return;
      case "Lam":
        go(e.body);
        return;
      case "Let":
        if (e.bind.tag === "NonRec") go(e.bind.rhs);
        else for (const [, r] of e.bind.pairs) go(r);
        go(e.body);
        return;
      case "Case": {
        if (e.scrutinee.tag === "Var" && e.scrutinee.binder.unique === u) {
          const alt = e.alts.length === 1 ? e.alts[0] : undefined;
          if (!alt || alt.con.tag !== "DataAlt" || alt.binders.length !== 1) {
            ok = false;
            return;
          }
          if (!UNBOXABLE.has(alt.con.con.typeName)) {
            ok = false;
            return;
          }
          if (con && con.name !== alt.con.con.name) {
            ok = false;
            return;
          }
          con = alt.con.con;
        } else go(e.scrutinee);
        for (const a of e.alts) go(a.body);
        return;
      }
      case "Con":
      case "Op":
        for (const a of e.args) go(a);
        return;
    }
  };
  go(body);
  return ok ? con : undefined;
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

const isTrivial = (e: CoreExpr): boolean => e.tag === "Var" || e.tag === "Lit";

export function workWrap(program: CoreProgram): CoreProgram {
  const strict = argStrictnessByUnique(program);
  const extra: CoreBind[] = [];
  /** Wrappers this pass created, by the binder they replaced. GHC gives each
   * one an INLINE unfolding so the Simplifier puts it at every call site and
   * only the worker survives; the substitution below is that step. Without
   * it a self-recursive function pays MORE than before - the worker calls the
   * wrapper, which reboxes only to unbox again on the next iteration. */
  const wrappers = new Map<number, { params: Binder[]; body: CoreExpr }>();

  const binds = program.binds.map((b) => {
    if (b.tag === "Rec") return b;
    if (b.binder.name.startsWith("$w")) return b;
    const { params, body } = lambdas(b.rhs);
    if (params.length === 0) return b;
    const sig = strict.get(b.binder.unique);
    if (!sig) return b;

    const unboxed: Array<{ param: Binder; con: DataCon; payload: Binder }> = [];
    params.forEach((p, i) => {
      if (sig[i] !== true) return;
      const con = unboxedWith(body, p.unique);
      if (con) unboxed.push({ param: p, con, payload: mkBinder(`${p.name}1`) });
    });
    if (unboxed.length === 0) return b;

    const taken = new Set(unboxed.map((u) => u.param.unique));
    const rest = params.filter((p) => !taken.has(p.unique));
    const worker = mkBinder(`$w${b.binder.name}`);
    worker.exported = false;
    worker.internal = true;
    // The worker rebuilds each box; `simplifyCore` deletes it again.
    const workerBody = unboxed.reduceRight<CoreExpr>(
      (inner, u) => ({
        tag: "Let",
        bind: {
          tag: "NonRec",
          binder: u.param,
          rhs: { tag: "Con", con: u.con, args: [{ tag: "Var", binder: u.payload }] },
        },
        body: inner,
      }),
      body,
    );
    extra.push({
      tag: "NonRec",
      binder: worker,
      rhs: mkLams([...unboxed.map((u) => u.payload), ...rest], workerBody),
    });

    const fields = unboxed.map((u) => ({ ...u, field: mkBinder(u.payload.name) }));
    const call = mkApps({ tag: "Var", binder: worker }, [
      ...fields.map((u) => ({ tag: "Var" as const, binder: u.field })),
      ...rest.map((p) => ({ tag: "Var" as const, binder: p })),
    ]);
    const wrapped = fields.reduceRight<CoreExpr>(
      (inner, u) => ({
        tag: "Case",
        scrutinee: { tag: "Var", binder: u.param },
        binder: mkBinder("ww"),
        alts: [{ con: { tag: "DataAlt", con: u.con }, binders: [u.field], body: inner }],
      }),
      call,
    );
    wrappers.set(b.binder.unique, { params, body: wrapped });
    return { tag: "NonRec" as const, binder: b.binder, rhs: mkLams(params, wrapped) };
  });
  if (wrappers.size === 0) return program;

  // One substitution pass. A wrapper body names only its worker, never another
  // wrapper, so nothing it introduces is a candidate and the walk terminates
  // without a recursion check - which matters, because the functions worth
  // splitting are exactly the recursive ones a size-based check would refuse.
  const expand = (e: CoreExpr): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App": {
        const { head, args } = spine(e);
        const done = args.map(expand);
        if (head.tag === "Var") {
          const w = wrappers.get(head.binder.unique);
          if (w && w.params.length === done.length && done.every(isTrivial)) {
            const sub = new Map<number, CoreExpr>();
            w.params.forEach((p, i) => sub.set(p.unique, done[i]!));
            return copy(w.body, sub, new Map());
          }
        }
        return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), expand(head));
      }
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: expand(e.body) };
      case "Let": {
        const bind: CoreBind =
          e.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: e.bind.binder, rhs: expand(e.bind.rhs) }
            : { tag: "Rec", pairs: e.bind.pairs.map(([x, r]) => [x, expand(r)] as [Binder, CoreExpr]) };
        return { tag: "Let", bind, body: expand(e.body) };
      }
      case "Case": {
        const alts: CoreAlt[] = e.alts.map((a) => ({ ...a, body: expand(a.body) }));
        return { tag: "Case", scrutinee: expand(e.scrutinee), binder: e.binder, alts };
      }
      case "Con":
        return { tag: "Con", con: e.con, args: e.args.map(expand) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map(expand) };
    }
  };

  const rewrite = (b: CoreBind): CoreBind =>
    b.tag === "NonRec"
      ? { tag: "NonRec", binder: b.binder, rhs: expand(b.rhs) }
      : { tag: "Rec", pairs: b.pairs.map(([x, r]) => [x, expand(r)] as [Binder, CoreExpr]) };

  // The wrappers themselves keep their own bodies: they are what call sites
  // that could not be rewritten - unknown callers, non-trivial arguments -
  // still enter.
  return { ...program, binds: [...extra.map(rewrite), ...binds] };
}
