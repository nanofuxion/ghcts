/** Port of `references/ghc/compiler/GHC/StgToJS/Sinker.hs`.
 *
 * Unfloat some top-level unexported things.
 *
 * GHC floats constants to the top level. This is fine in native code, but with
 * JS they occupy some global variable name. We can unfloat some unexported
 * things:
 *
 *   - global constructors, as long as they're referenced only once by another
 *     global constructor and are not in a recursive binding group
 *   - literals (small literals may also be sunk if they are used more than once)
 *
 * The consuming half was already here: `gsUnfloated` (src/stg-js/monad.ts) and
 * `genArg`/`genStaticArg` (src/stg-js/arg.ts) have always known how to expand a
 * sunk binder back into the expression it stood for. This is the producer.
 *
 * `isLocal` is where the port is not literal. GHC asks for a name with no
 * module that is also not exported, which after CorePrep singles out exactly
 * the `sat_` binders CorePrep itself invented. ghcts's `Binder.exported` is
 * already spoken for as `isGlobalId` (see `liveVars` in ./utils.ts), so the
 * first half is carried by `Binder.internal` and the second needs nothing:
 * a name no module owns is a name no export list can hold. That leaves the
 * same set - the bindings `src/core-to-stg.ts` floated out, and nothing else.
 */
import type { Binder, Literal, StgArg, StgBinding, StgExpr, StgRhs } from "../stg.js";
import type { UnfloatedMap } from "./utils.js";
import { isUnboxableCon } from "./utils.js";

/** GHC.StgToJS.Sinker.sinkPgm, less the `StgTopStringLit` split: ghcts has no
 * top-level string literal binding, so every top binding is already lifted. */
export function sinkPgm(pgm: StgBinding[]): [UnfloatedMap, StgBinding[]] {
  const usedOnce = collectUsedOnce(pgm);
  // GHC builds one `listToUFM` from `alwaysSinkable ++ used-once onceSinkable`,
  // so a binder both lists name keeps the later entry. The two agree on every
  // such binder - both hand back the same `StgConApp`/`StgLit` - so inserting
  // in the same order is enough.
  // GHC gates only `onceSinkable` on `usedOnce`; ghcts gates both. A sunk
  // binding is rebuilt wherever `genArg` meets it, and `genArg` only ever
  // looks at an argument - so the binding may not be left named anywhere
  // else. GHC needs no gate on the always-sinkable boxes because SetLevels
  // leaves a small box where it is (`notWorthFloating`) and its one use is
  // static data; `floatConstants` lifts them and their uses can be an entered
  // thunk or a closure payload, which codegen resolves by name and which the
  // removed binding then leaves undefined
  // (`h$$mainZCMainzilvl_u_173 is not defined`).
  const sinkables: UnfloatedMap = new Map();
  for (const b of pgm)
    for (const [i, e] of alwaysSinkable(b)) if (usedOnce.has(i.unique)) sinkables.set(i.unique, e);
  for (const b of pgm)
    for (const [i, e] of onceSinkable(b)) if (usedOnce.has(i.unique)) sinkables.set(i.unique, e);
  const isSunkBind = (b: StgBinding): boolean => b.tag === "StgNonRec" && sinkables.has(b.binder.unique);
  return [sinkables, topSortDecls(pgm).filter((b) => !isSunkBind(b))];
}

/** GHC.StgToJS.Sinker.alwaysSinkable - values that may be duplicated in the
 * generated code (e.g. small literals). */
function alwaysSinkable(b: StgBinding): Array<[Binder, StgExpr]> {
  if (b.tag !== "StgNonRec" || !isLocal(b.binder)) return [];
  const rhs: StgRhs = b.rhs;
  if (rhs.tag === "StgRhsClosure")
    return rhs.body.tag === "StgLit" && isSmallSinkableLit(rhs.body.lit) ? [[b.binder, rhs.body]] : [];
  return isAlwaysSinkableCon(rhs) ? [[b.binder, { tag: "StgConApp", con: rhs.con, args: rhs.args }]] : [];
}

/** The `StgRhsCon` half of `alwaysSinkable`'s condition, with the binder left
 * out: it is also what `src/core-to-stg.ts` floats to the top level, and
 * sharing the predicate is what stops the float and the unfloat drifting
 * apart. */
export function isAlwaysSinkableCon(rhs: StgRhs): boolean {
  if (rhs.tag !== "StgRhsCon" || rhs.args.length !== 1) return false;
  const [a] = rhs.args;
  return a!.tag === "StgLitArg" && isSmallSinkableLit(a!.lit) && isUnboxableCon(rhs.con);
}

/** GHC.StgToJS.Sinker.isSmallSinkableLit. Only `LitChar` and `LitNumber`
 * qualify; a `Float`/`Double` literal is deliberately not sinkable, which is
 * why an unboxable `D# 1.0` is left where it is. */
function isSmallSinkableLit(l: Literal): boolean {
  switch (l.tag) {
    case "LitChar":
      return (l.value.codePointAt(0) ?? 0) < 100000;
    case "LitNumInt":
    case "LitNumInt8":
    case "LitNumInt16":
    case "LitNumInt32":
    case "LitNumInt64":
    case "LitNumWord":
    case "LitNumWord8":
    case "LitNumWord16":
    case "LitNumWord32":
    case "LitNumWord64":
      return (l.value < 0n ? -l.value : l.value) < 100000n;
    default:
      return false;
  }
}

/** GHC.StgToJS.Sinker.onceSinkable - may be sunk, but duplication is not ok. */
function onceSinkable(b: StgBinding): Array<[Binder, StgExpr]> {
  if (b.tag !== "StgNonRec" || !isLocal(b.binder)) return [];
  const rhs: StgRhs = b.rhs;
  if (rhs.tag === "StgRhsCon") return [[b.binder, { tag: "StgConApp", con: rhs.con, args: rhs.args }]];
  return rhs.body.tag === "StgLit" ? [[b.binder, rhs.body]] : [];
}

/** GHC.StgToJS.Sinker.collectUsedOnce - every ident used only once in an
 * argument at the top level and never anywhere else. */
function collectUsedOnce(binds: StgBinding[]): Set<number> {
  const usedOnce = (ids: Binder[]): Set<number> => {
    const seen = new Map<number, number>();
    for (const i of ids) seen.set(i.unique, (seen.get(i.unique) ?? 0) + 1);
    return new Set([...seen].filter(([, n]) => n === 1).map(([u]) => u));
  };
  const top = usedOnce(binds.flatMap(collectArgsTop));
  return new Set([...usedOnce(binds.flatMap(collectArgs))].filter((u) => top.has(u)));
}

/** GHC.StgToJS.Sinker.collectArgsTop: every Id in an StgArg of a *top-level*
 * StgRhsCon. */
const collectArgsTop = (b: StgBinding): Binder[] =>
  rhsList(b).flatMap((r) => (r.tag === "StgRhsCon" ? r.args.flatMap(collectArgsA) : []));

/** GHC.StgToJS.Sinker.collectArgs: every Id in an StgArg in the AST. */
const collectArgs = (b: StgBinding): Binder[] =>
  rhsList(b).flatMap((r) => (r.tag === "StgRhsCon" ? r.args.flatMap(collectArgsA) : collectArgsE(r.body)));

/** GHC.StgToJS.Sinker.collectArgsE. */
function collectArgsE(e: StgExpr): Binder[] {
  switch (e.tag) {
    case "StgApp":
      return [e.fn, ...e.args.flatMap(collectArgsA)];
    case "StgConApp":
    case "StgOpApp":
      return e.args.flatMap(collectArgsA);
    case "StgCase":
      return [...collectArgsE(e.scrutinee), ...e.alts.flatMap((a) => collectArgsE(a.body))];
    case "StgLet":
    case "StgLetNoEscape":
      return [...collectArgs(e.binding), ...collectArgsE(e.body)];
    case "StgLit":
      return [];
  }
}

const collectArgsA = (a: StgArg): Binder[] => (a.tag === "StgVarArg" ? [a.id] : []);

const rhsList = (b: StgBinding): StgRhs[] => (b.tag === "StgNonRec" ? [b.rhs] : b.pairs.map(([, r]) => r));

/** GHC.StgToJS.Sinker.isLocal - see this module's header. */
const isLocal = (i: Binder): boolean => i.internal === true;

/** GHC.StgToJS.Sinker.topSortDecls - since we have sequential initialization,
 * topsort the non-recursive constructor bindings.
 *
 * GHC's `graphFromVerticesAndAdjacency`/`topologicalSortG` leaves independent
 * vertices in the order they were handed over; this is that same
 * order-preserving sort written directly, and it fails on a cycle for the same
 * reason GHC's does - a cyclic constructor group would have had to be an
 * `StgRec`. */
function topSortDecls(binds: StgBinding[]): StgBinding[] {
  type NonRec = Extract<StgBinding, { tag: "StgNonRec" }>;
  const nr = binds.filter((b): b is NonRec => b.tag === "StgNonRec");
  const rest = binds.filter((b) => b.tag !== "StgNonRec");
  const byKey = new Map(nr.map((b) => [b.binder.unique, b]));
  const out: StgBinding[] = [];
  const state = new Map<number, "open" | "done">();
  const visit = (b: NonRec): void => {
    const s = state.get(b.binder.unique);
    if (s === "done") return;
    if (s === "open") throw new Error("topSortDecls: unexpected cycle");
    state.set(b.binder.unique, "open");
    if (b.rhs.tag === "StgRhsCon")
      for (const a of b.rhs.args) {
        const dep = a.tag === "StgVarArg" ? byKey.get(a.id.unique) : undefined;
        if (dep !== undefined) visit(dep);
      }
    state.set(b.binder.unique, "done");
    out.push(b);
  };
  for (const b of nr) visit(b);
  return [...rest, ...out];
}
