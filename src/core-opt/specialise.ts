/** Core-to-Core: GHC's Specialise for dictionaries that are already known.
 *
 * After elaboration, `xs == ys` at `[Int]` is `$cEqList$== $fEqInt xs ys`.
 * The list method still takes a dictionary and calls `==` through it on every
 * element. Substituting `$fEqInt` for that parameter and rewriting the inner
 * `== $fEqInt` to `$cEqInt$==` is the same unfolding GHC's specialiser does
 * for a constrained instance at a closed type.
 *
 * Only `$f…` arguments are treated as dictionaries, so an ordinary function
 * that happens to take a CAF is left alone.
 */
import type { CoreBind, CoreExpr, CoreProgram } from "../core.js";
import { coreFreeVars, mkLams } from "../core.js";
import { mkBinder, type Binder } from "../stg.js";
import { copy } from "./inline.js";

const dictName = (e: CoreExpr): string | undefined =>
  e.tag === "Var" && e.binder.name.startsWith("$f") ? e.binder.name : undefined;

function spine(e: CoreExpr): { head: CoreExpr; args: CoreExpr[] } {
  const args: CoreExpr[] = [];
  let head = e;
  while (head.tag === "App") {
    args.unshift(head.arg);
    head = head.fn;
  }
  return { head, args };
}

function lambdas(e: CoreExpr): { params: Binder[]; body: CoreExpr } {
  const params: Binder[] = [];
  let body = e;
  while (body.tag === "Lam") {
    params.push(body.binder);
    body = body.body;
  }
  return { params, body };
}

/** Does this expression bind a `static e` form? `sptFingerprint` is set on
 * exactly those binders. */
function hasStaticPtr(e: CoreExpr): boolean {
  let found = false;
  const seen = (b: Binder) => {
    if (b.sptFingerprint !== undefined) found = true;
  };
  const go = (x: CoreExpr): void => {
    if (found) return;
    switch (x.tag) {
      case "Var":
        seen(x.binder);
        return;
      case "Lit":
        return;
      case "App":
        go(x.fn);
        go(x.arg);
        return;
      case "Lam":
        seen(x.binder);
        go(x.body);
        return;
      case "Let":
        if (x.bind.tag === "NonRec") {
          seen(x.bind.binder);
          go(x.bind.rhs);
        } else
          for (const [b, r] of x.bind.pairs) {
            seen(b);
            go(r);
          }
        go(x.body);
        return;
      case "Case":
        go(x.scrutinee);
        seen(x.binder);
        for (const a of x.alts) {
          a.binders.forEach(seen);
          go(a.body);
        }
        return;
      case "Con":
      case "Op":
        for (const a of x.args) go(a);
        return;
    }
  };
  go(e);
  return found;
}

const specKey = (fn: string, dicts: string[]): string => `$s${fn}$${dicts.map((d) => d.slice(2)).join("$")}`;

const dictMethod = (sel: string, dict: string, names: ReadonlySet<string>): string | undefined => {
    const suffix = dict.slice(2);
    const impl = `$f${suffix}_$c${sel}`;
    if (names.has(impl)) return impl;
    // Keep consuming older elaborated programs while the canonical name is
    // being adopted throughout the pipeline.
    const legacy = `$c${suffix}$${sel}`;
    return names.has(legacy) ? legacy : undefined;
};

// These selectors are the defaults whose result is immediately projected or
// further specialized.  A default body commonly contains `fst (divMod ...)`;
// the generic application walk marks the argument to `fst` lazy, but that
// would incorrectly hide the known dictionary from the nested selector.
const integralDefaults = new Set(["div", "divMod", "quot", "quotRem", "rem", "mod"]);
// Miso's concrete JS marshalling instance methods carry INLINE pragmas in
// the GHC source. Keep their dictionary projections unfoldable even when the
// call sits in a lazy dictionary field; the pragma is the source-level proof
// that this is the intended representation-preserving rewrite.
const inlineMarshalMethod = (name: string): boolean =>
  /(?:from|to)JS(?:Val|Value)/.test(name);

export function specialiseKnownDicts(program: CoreProgram, options: { inlineGenerated?: boolean; lowerStaticPtrProjection?: boolean } = {}): CoreProgram {
  const rhsOf = new Map<string, { binder: Binder; rhs: CoreExpr }>();
  for (const b of program.binds) {
    const pairs = b.tag === "NonRec" ? [[b.binder, b.rhs] as const] : b.pairs.map((p) => [p[0], p[1]] as const);
    for (const [binder, rhs] of pairs) rhsOf.set(binder.name, { binder, rhs });
  }
  const names = new Set(rhsOf.keys());
  // GHC's simplifier collapses a top-level `f = g` binding when it is used as
  // a value.  This matters for the native marshal path: dictionary fields are
  // frequently wired through several zero-argument aliases before reaching
  // the actual foreign import.  Only direct top-level aliases qualify; local
  // bindings and lambdas retain their ordinary sharing semantics.
  const aliases = new Map<number, Binder>();
  for (const { binder, rhs } of rhsOf.values()) {
    const direct = lambdas(rhs);
    // A source-level `ptr = static handler` is represented as an alias to the
    // floated `$staticN` binding. Unlike ordinary aliases, that binding has
    // static-pointer identity and must not be canonicalised through a generic
    // value substitution.
    if (
      direct.params.length === 0 &&
      direct.body.tag === "Var" &&
      direct.body.binder.unique !== binder.unique &&
      direct.body.binder.sptFingerprint === undefined
    )
      aliases.set(binder.unique, direct.body.binder);
  }
  const aliasTarget = (binder: Binder): Binder => {
    const seen = new Set<number>();
    let out = binder;
    while (!seen.has(out.unique)) {
      seen.add(out.unique);
      const next = aliases.get(out.unique);
      if (!next) break;
      out = next;
    }
    return out;
  };
  const topUniques = new Set<number>();
  for (const { binder } of rhsOf.values()) topUniques.add(binder.unique);
  const specs = new Map<string, Binder>();
  const extra: Array<{ binder: Binder; rhs: CoreExpr }> = [];

  const ensure = (fn: string, dicts: string[]): Binder | undefined => {
    const key = specKey(fn, dicts);
    const hit = specs.get(key);
    if (hit) return hit;
    if (names.has(key)) return rhsOf.get(key)?.binder;
    // Class selectors such as `div` have only the dictionary projection as
    // their RHS. When an instance supplies no concrete `$c...$div` binding,
    // specialize the class default method instead; its remaining lambdas are
    // the actual numeric arguments. Specializing the selector itself creates
    // a zero-argument case and loses those lambdas.
    const defaultMethod = fn === "div" ? "$dmIntegral$div" :
      fn === "divMod" ? "$dmIntegral$divMod" :
      fn === "quot" ? "$dmIntegral$quot" :
      fn === "rem" ? "$dmIntegral$rem" :
      fn === "mod" ? "$dmIntegral$mod" : undefined;
    const src = defaultMethod ? (rhsOf.get(defaultMethod) ?? rhsOf.get(fn)) : rhsOf.get(fn);
    if (!src) return undefined;
    const { params, body } = lambdas(src.rhs);
    if (params.length < dicts.length) return undefined;
    const dictVars: CoreExpr[] = [];
    for (const d of dicts) {
      const found = rhsOf.get(d);
      if (!found) return undefined;
      dictVars.push({ tag: "Var", binder: found.binder });
    }
    const sub = new Map<number | Binder, CoreExpr>();
    params.slice(0, dicts.length).forEach((p, i) => sub.set(p.unique, dictVars[i]!));
    const specialised = mkLams(params.slice(dicts.length), copy(body, sub, new Map()));
    // A copy is only usable if everything it still names is in scope where it
    // is about to be placed: at the top level. Anything else means the source
    // body read a binder from an enclosing scope, and lifting it out here
    // would emit a reference to a name that is defined nowhere.
    for (const v of coreFreeVars(specialised)) if (!topUniques.has(v.unique)) return undefined;
    // A `static e` form is identified across threads by its fingerprint, and a
    // copy carries the same one. Two bindings claiming one key means the
    // static pointer table answers with whichever registered last, so the
    // main thread looks up an event handler and gets someone else's. Miso's
    // Lynx delegation is built on those keys, so a specialised copy of a body
    // holding one silently stops every tap from finding its handler.
    if (hasStaticPtr(specialised)) return undefined;
    const binder = mkBinder(key);
    binder.exported = false;
    binder.internal = true;
    specs.set(key, binder);
    names.add(key);
    topUniques.add(binder.unique);
    rhsOf.set(key, { binder, rhs: specialised });
    extra.push({ binder, rhs: specialised });
    return binder;
  };

  // A dictionary method appearing as a constructor field is still lazy. Do
  // not turn that field into a direct call: GHC keeps the call in a thunk (and
  // evaluates it only when the field is demanded). The old unconditional
  // rewrite changed the evaluation order and showed up as a `call` instead of
  // `let` in the STG differential corpus.
  const unrolling = new Set<string>();
  const go = (e: CoreExpr, lazy = false): CoreExpr => {
    switch (e.tag) {
      case "Var": {
        const target = aliasTarget(e.binder);
        return target === e.binder ? e : { tag: "Var", binder: target };
      }
      case "Lit":
        return e;
      case "App": {
        const { head, args } = spine(e);
        const done = args.map((arg) => go(arg, true));
        if (options.lowerStaticPtrProjection && head.tag === "Var" && head.binder.name === "deRefStaticPtr" && done.length === 1) {
          const p = done[0];
          if (p?.tag === "Var") {
            let ptr = rhsOf.get(p.binder.name)?.rhs;
            const seen = new Set<string>();
            while (ptr?.tag === "Var" && !seen.has(ptr.binder.name)) {
              seen.add(ptr.binder.name);
              ptr = rhsOf.get(ptr.binder.name)?.rhs;
            }
            if (ptr?.tag === "Con" && ptr.con.name === "StaticPtr") {
              const value = mkBinder("staticPtrValue");
              return {
                tag: "Case",
                scrutinee: p,
                binder: mkBinder("staticPtr"),
                alts: [{ con: { tag: "DataAlt", con: ptr.con }, binders: [mkBinder("staticPtrKey"), value], body: { tag: "Var", binder: value } }],
              };
            }
          }
        }
        // Selecting a concrete equality method does not evaluate the method's
        // arguments. Generated Eq dictionaries reach their concrete methods
        // through lazy fields, so permit this one selector there. Keep other
        // dictionary methods behind the lazy barrier: recursively expanding
        // every lazy dictionary call can copy cyclic generated dictionaries.
        const lazyEq = head.tag === "Var" && (head.binder.name === "==" || head.binder.name.endsWith("$=="));
        if ((!lazy || lazyEq || (head.tag === "Var" && integralDefaults.has(head.binder.name)) || (head.tag === "Var" && inlineMarshalMethod(head.binder.name))) && head.tag === "Var" && done.length > 0) {
          const d0 = dictName(done[0]!);
          if (d0) {
            const implName = dictMethod(head.binder.name, d0, names);
            if (implName) {
              const implInfo = rhsOf.get(implName);
              const impl = implInfo?.binder;
              if (impl) {
                // Primitive FromJSVal/FromJSValue methods are often emitted as
                // zero-argument aliases to a foreign import. They are values,
                // not lambda candidates, so canonicalise the alias here just
                // as GHC's Simplifier does when it selects the dictionary
                // field. Keeping the wrapper adds a closure entry on every
                // native event decode.
                const direct = lambdas(implInfo.rhs);
                if (direct.params.length === 0 && direct.body.tag === "Var")
                  return done.slice(1).reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), { tag: "Var", binder: direct.body.binder });
                return done.slice(1).reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), { tag: "Var", binder: impl });
              }
            }
            {
              const dicts: string[] = [];
              for (const a of done) {
                const n = dictName(a);
                if (!n) break;
                dicts.push(n);
              }
              const spec = ensure(head.binder.name, dicts);
              if (spec)
                if (options.inlineGenerated) {
                  const generated = rhsOf.get(spec.name);
                  const lam = generated && lambdas(generated.rhs);
                  const callArgs = done.slice(dicts.length);
                  // A specialisation that calls itself would be unrolled
                  // without end: GHC never inlines a loop breaker, and this
                  // one keeps a call to a copy already being unrolled as the
                  // call it is.
                  if (lam && lam.params.length === callArgs.length && !unrolling.has(spec.name)) {
                    const sub = new Map<number | Binder, CoreExpr>();
                    lam.params.forEach((p, i) => sub.set(p.unique, callArgs[i]!));
                    // The generated default may immediately call another
                    // class default (Integral.div -> divMod -> quotRem).
                    // Continue through the copied body so its now-concrete
                    // dictionary arguments are specialized as well.
                    unrolling.add(spec.name);
                    try {
                      return go(copy(lam.body, sub, new Map()));
                    } finally {
                      unrolling.delete(spec.name);
                    }
                  }
                }
              if (spec)
                return done
                  .slice(dicts.length)
                  .reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), { tag: "Var", binder: spec });
            }
          }
        }
        return done.reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), go(head));
      }
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: go(e.body) };
      case "Let": {
        const bind: CoreBind =
          e.bind.tag === "NonRec"
              ? { tag: "NonRec", binder: e.bind.binder, rhs: go(e.bind.rhs, lazy) }
            : { tag: "Rec", pairs: e.bind.pairs.map(([b, r]) => [b, go(r, lazy)] as [Binder, CoreExpr]) };
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
        return { tag: "Con", con: e.con, args: e.args.map((arg) => go(arg, true)) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((arg) => go(arg, false)) };
    }
  };

  const work = program.binds.map((b) =>
    b.tag === "NonRec"
      ? ({ tag: "NonRec" as const, binder: b.binder, rhs: go(b.rhs) } satisfies CoreBind)
      : ({ tag: "Rec" as const, pairs: b.pairs.map(([bd, r]) => [bd, go(r)] as [Binder, CoreExpr]) } satisfies CoreBind),
  );
  const added: CoreBind[] = [];
  while (extra.length) {
    const batch = extra.splice(0, extra.length);
    for (const b of batch) {
      const rhs = go(b.rhs);
      rhsOf.set(b.binder.name, { binder: b.binder, rhs });
      added.push({ tag: "NonRec", binder: b.binder, rhs });
    }
  }
  return { ...program, binds: [...added, ...work] };
}
