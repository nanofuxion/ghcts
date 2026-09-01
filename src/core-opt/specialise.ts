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
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "../core.js";
import { coreFreeVars, mkLams } from "../core.js";
import { mkBinder, type Binder } from "../stg.js";

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

function copy(e: CoreExpr, sub: Map<number, CoreExpr>, fresh: Map<number, Binder>): CoreExpr {
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
  const impl = `$c${dict.slice(2)}$${sel}`;
  return names.has(impl) ? impl : undefined;
};

export function specialiseKnownDicts(program: CoreProgram): CoreProgram {
  const rhsOf = new Map<string, { binder: Binder; rhs: CoreExpr }>();
  for (const b of program.binds) {
    const pairs = b.tag === "NonRec" ? [[b.binder, b.rhs] as const] : b.pairs.map((p) => [p[0], p[1]] as const);
    for (const [binder, rhs] of pairs) rhsOf.set(binder.name, { binder, rhs });
  }
  const names = new Set(rhsOf.keys());
  const topUniques = new Set<number>();
  for (const { binder } of rhsOf.values()) topUniques.add(binder.unique);
  const specs = new Map<string, Binder>();
  const extra: Array<{ binder: Binder; rhs: CoreExpr }> = [];

  const ensure = (fn: string, dicts: string[]): Binder | undefined => {
    const key = specKey(fn, dicts);
    const hit = specs.get(key);
    if (hit) return hit;
    if (names.has(key)) return rhsOf.get(key)?.binder;
    const src = rhsOf.get(fn);
    if (!src) return undefined;
    const { params, body } = lambdas(src.rhs);
    if (params.length < dicts.length) return undefined;
    const dictVars: CoreExpr[] = [];
    for (const d of dicts) {
      const found = rhsOf.get(d);
      if (!found) return undefined;
      dictVars.push({ tag: "Var", binder: found.binder });
    }
    const sub = new Map<number, CoreExpr>();
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

  const go = (e: CoreExpr): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App": {
        const { head, args } = spine(e);
        const done = args.map(go);
        if (head.tag === "Var" && done.length > 0) {
          const d0 = dictName(done[0]!);
          if (d0) {
            const implName = dictMethod(head.binder.name, d0, names);
            if (implName) {
              const impl = rhsOf.get(implName)?.binder;
              if (impl)
                return done.slice(1).reduce<CoreExpr>((fn, arg) => ({ tag: "App", fn, arg }), { tag: "Var", binder: impl });
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
