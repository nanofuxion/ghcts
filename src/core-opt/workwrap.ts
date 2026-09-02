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
import { coreFreeVars, mkApps, mkLams } from "../core.js";
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

/** GHC leaves a short nested primitive-method region in its original
 * function shape; splitting it creates an extra local worker/continuation
 * pair instead of the compact case chain emitted by CorePrep. */
function primitiveMethodCount(e: CoreExpr): number {
  if (e.tag === "App") {
    let head: CoreExpr = e;
    while (head.tag === "App") head = head.fn;
    const here = head.tag === "Var" && /^(?:\$fNumInt_\$c|\$cNumInt\$)(?:[+*\-/]|negate)$|^(?:\$fOrdInt_\$c|\$cOrdInt\$)(?:[<>]=?|compare)$|^(?:\$fIntegralInt_\$c|\$cIntegralInt\$)(?:quotRem|divMod)$/.test(head.binder.name) ? 1 : 0;
    return here + primitiveMethodCount(e.fn) + primitiveMethodCount(e.arg);
  }
  if (e.tag === "Lam") return primitiveMethodCount(e.body);
  if (e.tag === "Let") return primitiveMethodCount(e.body) + (e.bind.tag === "NonRec" ? primitiveMethodCount(e.bind.rhs) : e.bind.pairs.reduce((n, [, r]) => n + primitiveMethodCount(r), 0));
  if (e.tag === "Case") return primitiveMethodCount(e.scrutinee) + e.alts.reduce((n, a) => n + primitiveMethodCount(a.body), 0);
  if (e.tag === "Con" || e.tag === "Op") return e.args.reduce((n, a) => n + primitiveMethodCount(a), 0);
  return 0;
}

/** The constructor this binder is taken apart with, or `undefined` if it is
 * never scrutinised or is scrutinised in a way that does not unbox.
 *
 * Uses that are not `case` scrutinees are allowed: the branch that returns
 * `acc` unchanged still wants the box, and `simplifyCore` floats the worker's
 * rebuilt box into exactly that branch, so the hot path does not pay for it.
 * GHC makes the same trade under `Note [Reboxing]`. */
function unboxedWith(body: CoreExpr, u: number, primitiveRep?: Binder["primitiveRep"]): DataCon | undefined {
  let con: DataCon | undefined;
  let sawCase = false;
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
          sawCase = true;
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
  if (!ok) return undefined;
  if (sawCase) return con;
  // A strict primitive consumer is the other worker/wrapper shape GHC's
  // demand analysis recognizes: no explicit `case x of I# ...` remains in
  // Core, but an operation such as `x > 10` still consumes x's payload.
  // Restrict this first form to Int, whose boxed constructor is unambiguous
  // in the frontend's constructor table and whose JS representation is one
  // machine slot.
  // Merely returning the variable is not a strict primitive consumer: the
  // boxed value may be returned without entering it (`konst a _ = a`).
  // Require an actual primitive operation/test before using this fallback.
  if (primitiveRep === "Int" && hasPrimitiveUse(body, u))
    return { name: "I", unique: -1, tag: 1, arity: 1, typeName: "Int", fieldReps: ["other"] };
  return undefined;
}

function hasPrimitiveUse(body: CoreExpr, u: number): boolean {
  switch (body.tag) {
    case "Var":
    case "Lit": return false;
    case "Op": return body.args.some((a) => mentions(a, u)) || body.args.some((a) => hasPrimitiveUse(a, u));
    case "App": {
      const { head, args } = spine(body);
      if (head.tag === "Var" && /^(?:\$fNumInt_\$c|\$cNumInt\$)(?:[+*\-/]|negate)$|^(?:\$fOrdInt_\$c|\$cOrdInt\$)(?:[<>]=?|compare)$|^(?:\$fIntegralInt_\$c|\$cIntegralInt\$)(?:quotRem|divMod)$/.test(head.binder.name) && args.some((a) => mentions(a, u))) return true;
      return hasPrimitiveUse(body.fn, u) || hasPrimitiveUse(body.arg, u);
    }
    case "Lam": return hasPrimitiveUse(body.body, u);
    case "Let": return (body.bind.tag === "NonRec" ? hasPrimitiveUse(body.bind.rhs, u) : body.bind.pairs.some(([, r]) => hasPrimitiveUse(r, u))) || hasPrimitiveUse(body.body, u);
    case "Case": return hasPrimitiveUse(body.scrutinee, u) || body.alts.some((a) => hasPrimitiveUse(a.body, u));
    case "Con": return body.args.some((a) => hasPrimitiveUse(a, u));
  }
}

function mentions(e: CoreExpr, u: number): boolean {
  switch (e.tag) {
    case "Var": return e.binder.unique === u;
    case "Lit": return false;
    case "App": return mentions(e.fn, u) || mentions(e.arg, u);
    case "Lam": return mentions(e.body, u);
    case "Let": return (e.bind.tag === "NonRec" ? mentions(e.bind.rhs, u) : e.bind.pairs.some(([, r]) => mentions(r, u))) || mentions(e.body, u);
    case "Case": return mentions(e.scrutinee, u) || e.alts.some((a) => mentions(a.body, u));
    case "Con": return e.args.some((a) => mentions(a, u));
    case "Op": return e.args.some((a) => mentions(a, u));
  }
}

/** Whether every occurrence of `u` is either the scrutinee of a case or the
 * result of the surrounding expression. In that shape the worker can use the
 * unboxed payload directly: a case becomes a primitive test and a returned
 * payload is boxed by the wrapper. Passing `u` to an ordinary call or storing
 * it in a constructor would still require the conservative reboxed form. */
function payloadOnly(body: CoreExpr, u: number, result = true): boolean {
  switch (body.tag) {
    case "Var":
      return body.binder.unique !== u || result;
    case "Lit":
      return true;
    case "App":
      return payloadOnly(body.fn, u, false) && payloadOnly(body.arg, u, false);
    case "Lam":
      return body.binder.unique === u || payloadOnly(body.body, u, false);
    case "Let":
      return (body.bind.tag === "NonRec"
        ? payloadOnly(body.bind.rhs, u, false)
        : body.bind.pairs.every(([, rhs]) => payloadOnly(rhs, u, false))) &&
        payloadOnly(body.body, u, result);
    case "Case":
      return (body.scrutinee.tag === "Var" && body.scrutinee.binder.unique === u
        ? true
        : payloadOnly(body.scrutinee, u, false)) &&
        body.alts.every((a) => payloadOnly(a.body, u, result));
    case "Con":
    case "Op":
      return body.args.every((arg) => payloadOnly(arg, u, false));
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

const isTrivial = (e: CoreExpr): boolean => e.tag === "Var" || e.tag === "Lit";

// Class-method entry points are polymorphic ABI values.  Splitting their
// boxed arguments into private workers changes the dictionary method contract
// and makes callers fall back to generic apply.  Worker/wrapper is still
// appropriate for ordinary user bindings; generated `$c...` methods belong to
// the method-specialisation path instead.
function isClassMethod(binder: Binder): boolean {
  return binder.name === "unInt" || binder.name.includes("$c") || binder.name.includes("$zdc");
}

/** Drop the boxed shell around a machine result inside an unboxed worker.
 * Core still spells `I (a + b)` after the source-level arithmetic has been
 * copied into the worker; GHC's worker/wrapper rewrite changes that result to
 * the primitive directly. Only one-field unboxable constructors whose field
 * is an `Op` are eligible, so ordinary lazy constructor fields are untouched. */
function unboxWorkerResults(e: CoreExpr): CoreExpr {
  switch (e.tag) {
    case "Var":
    case "Lit":
      return e;
    case "Con": {
      const args = e.args.map(unboxWorkerResults);
      return args.length === 1 && UNBOXABLE.has(e.con.typeName) && args[0]!.tag === "Op" ? args[0]! : { ...e, args };
    }
    case "Op":
      return { ...e, args: e.args.map(unboxWorkerResults) };
    case "App":
      return { tag: "App", fn: unboxWorkerResults(e.fn), arg: unboxWorkerResults(e.arg) };
    case "Lam":
      return { tag: "Lam", binder: e.binder, body: unboxWorkerResults(e.body) };
    case "Let":
      return {
        tag: "Let",
        bind: e.bind.tag === "NonRec"
          ? { tag: "NonRec", binder: e.bind.binder, rhs: unboxWorkerResults(e.bind.rhs) }
          : { tag: "Rec", pairs: e.bind.pairs.map(([b, rhs]) => [b, unboxWorkerResults(rhs)] as [Binder, CoreExpr]) },
        body: unboxWorkerResults(e.body),
      };
    case "Case":
      return { ...e, scrutinee: unboxWorkerResults(e.scrutinee), alts: e.alts.map((a) => ({ ...a, body: unboxWorkerResults(a.body) })) };
  }
}

/** The worker parameter is already the constructor payload, so the source
 * case that unpacked the boxed argument has become impossible bookkeeping.
 * GHC's worker/wrapper simplifier removes it; leaving it here makes DmdAnal
 * report the worker strict in an argument whose unboxed representation it
 * never evaluates. */
function dropUnboxedCases(e: CoreExpr, payloads: Set<Binder>): CoreExpr {
  switch (e.tag) {
    case "Var":
    case "Lit":
      return e;
    case "App":
      return { tag: "App", fn: dropUnboxedCases(e.fn, payloads), arg: dropUnboxedCases(e.arg, payloads) };
    case "Lam":
      return { tag: "Lam", binder: e.binder, body: dropUnboxedCases(e.body, payloads) };
    case "Let":
      return {
        tag: "Let",
        bind: e.bind.tag === "NonRec"
          ? { tag: "NonRec", binder: e.bind.binder, rhs: dropUnboxedCases(e.bind.rhs, payloads) }
          : { tag: "Rec", pairs: e.bind.pairs.map(([b, rhs]) => [b, dropUnboxedCases(rhs, payloads)] as [Binder, CoreExpr]) },
        body: dropUnboxedCases(e.body, payloads),
      };
    case "Case": {
      const scrutinee = dropUnboxedCases(e.scrutinee, payloads);
      const alts = e.alts.map((a) => ({ ...a, body: dropUnboxedCases(a.body, payloads) }));
      if (scrutinee.tag === "Var" && payloads.has(scrutinee.binder) && alts.length === 1) {
        const alt = alts[0]!;
        if (alt.con.tag === "DataAlt" && UNBOXABLE.has(alt.con.con.typeName) && alt.binders.length === 1) {
          return copy(alt.body, new Map<Binder, CoreExpr>([[alt.binders[0]!, scrutinee]]), new Map());
        }
      }
      return { tag: "Case", scrutinee, binder: e.binder, alts };
    }
    case "Con":
      return { tag: "Con", con: e.con, args: e.args.map((a) => dropUnboxedCases(a, payloads)) };
    case "Op":
      return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((a) => dropUnboxedCases(a, payloads)) };
  }
}


export function workWrap(program: CoreProgram): CoreProgram {
  const strict = argStrictnessByUnique(program);
  const extra: CoreBind[] = [];
  /** Wrappers this pass created, by the binder they replaced. GHC gives each
   * one an INLINE unfolding so the Simplifier puts it at every call site and
   * only the worker survives; the substitution below is that step. Without
   * it a self-recursive function pays MORE than before - the worker calls the
   * wrapper, which reboxes only to unbox again on the next iteration. */
  const wrappers = new Map<Binder, { params: Binder[]; body: CoreExpr }>();

  const binds = program.binds.map((b) => {
    if (b.tag === "Rec") return b;
    if (b.binder.name.startsWith("$w")) return b;
    if (isClassMethod(b.binder)) return b;
    const { params, body } = lambdas(b.rhs);
    if (params.length === 0) return b;
    // A short arithmetic chain such as `a * b + a` is still one compact
    // primitive worker shape.  Rejecting it at two methods prevents the same
    // worker/wrapper split GHC emits for ordinary composed arithmetic.
    const methodBudget = b.binder.resultRep === "boxed-int" && params.length === 2 ? 4 : 2;
    if (primitiveMethodCount(body) > methodBudget) return b;
    // Primitive-representation metadata is already a sufficient demand fact
    // for a strict monomorphic entry.  The demand map can omit such a binder
    // after earlier Core rewrites, even though GHC still worker/wraps it.
    const sig = strict.get(b.binder.unique) ??
      (b.binder.strict === true && primitiveMethodCount(body) > 0 && primitiveMethodCount(body) <= 2
        ? params.map(() => true)
        : undefined);
    if (!sig) return b;

    const unboxed: Array<{ param: Binder; con: DataCon; payload: Binder }> = [];
    params.forEach((p, i) => {
      if (sig[i] !== true) return;
      const con = unboxedWith(body, p.unique, p.primitiveRep ?? (b.binder.resultRep === "boxed-int" ? "Int" : undefined));
      if (con) {
        // This binder is the worker's machine-value parameter, not the
        // source-level boxed parameter. Preserve the proof that selected the
        // worker so Core-to-STG gives it the primitive ABI representation.
        unboxed.push({
          param: p,
          con,
          payload: mkBinder(`${p.name}1`, {
            primitiveRep: p.primitiveRep ?? "Int",
            unboxedInt: true,
          }),
        });
      }
    });
    if (unboxed.length === 0) return b;

    const taken = new Set(unboxed.map((u) => u.param.unique));
    const rest = params.filter((p) => !taken.has(p.unique));
    const worker = mkBinder(`$w${b.binder.name}`);
    worker.topLevel = true;
    worker.exported = false;
    worker.internal = true;
    // Worker payloads are already unboxed and consumed by the worker body;
    // preserve that demand fact so the JS backend can use the worker entry
    // directly instead of allocating/pushing its closure at every call.
    worker.strict = true;
    worker.directJumpEligible = true;
    // GHC's worker takes the unboxed payload directly. The wrapper below
    // performs the one boxing step required by callers that still use the
    // source-level function type.
    // The bare payload stands in for the box everywhere, including where the
    // box is passed on as a value (`hexDigits` hands its `n` to
    // `hexDigitsStep`). That is only sound because every constructor this
    // pass unboxes is unboxable in the JS backend - the box IS the raw value
    // at runtime. Rebuilding `I# payload` here instead, as GHC's `Note
    // [Reboxing]` does, breaks the shapes `dropUnboxedCases` and
    // `unboxWorkerResults` expect (Integer arithmetic came out wrong).
    const payloadSub = new Map<number, CoreExpr>();
    for (const u of unboxed) payloadSub.set(u.param.unique, { tag: "Var", binder: u.payload });
    const copiedBody = payloadSub.size === 0 ? body : copy(body, payloadSub, new Map());
    const payloadBody = dropUnboxedCases(
      unboxWorkerResults(copiedBody),
      new Set(unboxed.map((u) => u.payload)),
    );
    // GHC's worker/wrapper also drops arguments that the worker never reads.
    // Keep them in the source wrapper for ABI compatibility, but do not pass
    // them through the private worker (the `konst a _ = a` case is the
    // simplest observable example).
    const used = coreFreeVars(payloadBody);
    const workerRest = rest.filter((p) => used.has(p));
    extra.push({
      tag: "NonRec",
      binder: worker,
      rhs: mkLams([...unboxed.map((u) => u.payload), ...workerRest], payloadBody),
    });

    const fields = unboxed.map((u) => ({ ...u, field: mkBinder(u.payload.name) }));
    const workerCall = mkApps({ tag: "Var", binder: worker }, [
      ...fields.map((u) => ({ tag: "Var" as const, binder: u.field })),
      ...workerRest.map((p) => ({ tag: "Var" as const, binder: p })),
    ]);
    const call: CoreExpr = workerCall;
    const wrapped = fields.reduceRight<CoreExpr>(
      (inner, u) => ({
        tag: "Case",
        scrutinee: { tag: "Var", binder: u.param },
        binder: mkBinder("ww"),
        alts: [{ con: { tag: "DataAlt", con: u.con }, binders: [u.field], body: inner }],
      }),
      call,
    );
    wrappers.set(b.binder, { params, body: wrapped });
    return { tag: "NonRec" as const, binder: b.binder, rhs: mkLams(params, wrapped) };
  });
  if (wrappers.size === 0) return program;

  // One substitution pass. A wrapper body names only its worker, never another
  // wrapper, so nothing it introduces is a candidate and the walk terminates
  // without a recursion check - which matters, because the functions worth
  // splitting are exactly the recursive ones a size-based check would refuse.
  const expand = (e: CoreExpr, demanded = true): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App": {
        const { head, args } = spine(e);
        const done = args.map((arg) => expand(arg, false));
        if (head.tag === "Var") {
          const w = wrappers.get(head.binder);
          if (demanded && w && w.params.length === done.length && done.every(isTrivial)) {
            const sub = new Map<number | Binder, CoreExpr>();
            w.params.forEach((p, i) => sub.set(p, done[i]!));
            return copy(w.body, sub, new Map());
          }
        }
        return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), expand(head, true));
      }
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: expand(e.body, true) };
      case "Let": {
        const bind: CoreBind =
          e.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: e.bind.binder, rhs: expand(e.bind.rhs, false) }
            : { tag: "Rec", pairs: e.bind.pairs.map(([x, r]) => [x, expand(r, false)] as [Binder, CoreExpr]) };
        return { tag: "Let", bind, body: expand(e.body, demanded) };
      }
      case "Case": {
        const alts: CoreAlt[] = e.alts.map((a) => ({ ...a, body: expand(a.body, demanded) }));
        return { tag: "Case", scrutinee: expand(e.scrutinee, true), binder: e.binder, alts };
      }
      case "Con":
        return { tag: "Con", con: e.con, args: e.args.map((arg) => expand(arg, false)) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((arg) => expand(arg, true)) };
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
