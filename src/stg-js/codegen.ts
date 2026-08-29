/** Port of GHC.StgToJS.CodeGen (ghc-9.12.2-release): the JavaScript code
 * generator's driver.
 *
 * `stgToJS` in GHC walks a module's top-level bindings into `LinkableUnit`s
 * and serialises them into a `.o` through GHC.StgToJS.Object. ghcts has no
 * Object.hs, Deps.hs or StaticPtr.hs, so this port stops at the
 * LinkableUnit and adds `renderModule`, which does what the linker would:
 * declare the statics, emit the code, install the info tables, run the static
 * initialisers. Those last two steps are `staticDeclStat`/`staticInitStat`
 * from GHC.StgToJS.Linker.Linker, transcribed here because there is nowhere
 * else for them to live yet.
 *
 * Not modelled, and dropped rather than faked: `SptEntry`/StaticPointers,
 * ForeignStubs, cost centres, dependency data, and the `-ddump-js` hook.
 */
import type { JStat } from "../js/syntax.js";
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { Var, global, mconcatJStgStat, memptyJStgStat } from "../js/jstg-syntax.js";
import { app, appS, declAssign_, jDouble, jInt, jString, returnStack, toJExpr } from "../js/make.js";
import { jsOptimize } from "../js/optimizer.js";
import { renderStat } from "../js/ppr.js";
import { jStgStatToJS } from "../js/transform.js";
import type { Binder, DataCon, StgBinding, StgRhs } from "../stg.js";
import { allocConStatic, jsStaticArgs } from "./arg.js";
import { closureInfoStat } from "./closure.js";
import { initExprCtx } from "./expr-ctx.js";
import { genBody, genEntryType, genStaticRefs, genStaticRefsRhs, loadLiveFun, stackState } from "./expr.js";
import { identForDataConEntryId, identForEntryId, identForId, unitModuleStringZ } from "./ids.js";
import type { StaticArg, StaticVal } from "./literal.js";
import type { GenState, GlobalOcc, Module, StaticInfo } from "./monad.js";
import { emitClosureInfo, emitStatic, emitToplevel, getSettings, globalOccs, resetGroup, runG } from "./monad.js";
import { R2 } from "./regs.js";
import { sinkPgm } from "./sinker.js";
import { resetSlots, updateThunk } from "./stack.js";
import type { ClosureInfo, StgToJSConfig } from "./types.js";
import { JSRep } from "./types.js";
import type { LiveVars } from "./utils.js";
import { collectIds, collectTopIds, fixedLayout, hasExport, stgRhsLive } from "./utils.js";

// ---------------------------------------------------------------------------
// GHC.StgToJS.Types: the two records genUnits produces
// ---------------------------------------------------------------------------

/** One toplevel block in the object file. `oiRaw`/`oiFExports`/`oiFImports`
 * are dropped: they only ever carry FFI data, and FFI is unported. */
export interface ObjBlock {
  /** toplevel symbols (stored in index) */
  oiSymbols: string[];
  /** closure information of all closures in block */
  oiClInfo: ClosureInfo[];
  /** static closure data */
  oiStatic: StaticInfo[];
  /** the code */
  oiStat: JStgStat;
}

/** Data used to generate one ObjBlock in our object file. */
export interface LinkableUnit {
  luObjBlock: ObjBlock;
  /** exported names from haskell identifiers */
  luIdExports: Binder[];
  /** other exports */
  luOtherExports: string[];
  /** identifiers this unit depends on */
  luIdDeps: Binder[];
  /** `luIdDeps`, resolved to the generated symbol strings each `Binder`
   * actually got - computed here, not later, because `identForId` reads a
   * mutable per-module identifier cache/counter (`GenState.gsIdents` /
   * `gsIdentMint`): calling it again with a *different* GenState (e.g. a
   * linker pass after every module has already been compiled) is not
   * guaranteed to reproduce the same name for a cross-module reference.
   * The linker's reachability pass (`src/linker/linker.ts`) consumes this
   * directly instead of re-deriving idents from rendered JS, which the
   * `oiStat`/`oiStatic`/`oiClInfo` AST alone cannot fully answer - GHC's own
   * `getDeps` doesn't either; it's exactly why GHC caches `bi_block_deps`. */
  luDepSymbols: string[];
  /** always link this unit */
  luRequired: boolean;
}

/** GHC.StgToJS.Symbols.moduleGlobalSymbol */
export const moduleGlobalSymbol = (m: Module): string => `h$${unitModuleStringZ(m)}_<global>`;

/** GHC.StgToJS.Symbols.moduleExportsSymbol */
export const moduleExportsSymbol = (m: Module): string => `h$${unitModuleStringZ(m)}_<exports>`;

// ---------------------------------------------------------------------------
// stgToJS
// ---------------------------------------------------------------------------

/** Code generator for JavaScript.
 *
 * GHC's `stgToJS` also sinks the program, computes dependency data and writes
 * a binary object file; here it stops at the linkable units.
 */
export function stgToJS(config: StgToJSConfig, thisMod: Module, stgBinds: StgBinding[]): LinkableUnit[] {
  // GHC: `let (unfloated, binds) = sinkPgm this_mod binds0`
  const [unfloated, binds] = sinkPgm(stgBinds);
  return runG(config, thisMod, unfloated, (gs) => genUnits(gs, thisMod, binds));
}

/** Generate the ingredients for the linkable units for this module */
export function genUnits(gs: GenState, m: Module, ss: StgBinding[]): LinkableUnit[] {
  const gbl = generateGlobalBlock(gs, m);
  const exports = generateExportsBlock(m);
  const others: LinkableUnit[] = [];
  for (const x of ss) {
    const mlu = generateBlock(gs, x);
    if (mlu !== undefined) others.push(mlu);
  }
  return [gbl, exports, ...others];
}

/** Generate the global unit that all other blocks in the module depend on;
 * used for cost centres and static initializers. The global unit has no
 * dependencies and exports the moduleGlobalSymbol. */
function generateGlobalBlock(gs: GenState, m: Module): LinkableUnit {
  // `initStaticPtrs spt_entries` is dropped with StaticPtr.hs
  const stat = mconcatJStgStat([...gs.gsGlobal].reverse());
  const syms = [moduleGlobalSymbol(m)];
  return {
    luObjBlock: { oiSymbols: syms, oiClInfo: [], oiStatic: [], oiStat: stat },
    luIdExports: [],
    luOtherExports: syms,
    luIdDeps: [],
    luDepSymbols: [],
    luRequired: false,
  };
}

function generateExportsBlock(m: Module): LinkableUnit {
  const syms = [moduleExportsSymbol(m)];
  return {
    luObjBlock: { oiSymbols: syms, oiClInfo: [], oiStatic: [], oiStat: memptyJStgStat },
    luIdExports: [],
    luOtherExports: syms,
    luIdDeps: [],
    luDepSymbols: [],
    luRequired: true,
  };
}

/** Generate the linkable unit for one binding or group of mutually recursive
 * bindings.
 *
 * GHC's `CgStgTopBinding` also has a `StgTopStringLit` constructor; stg.ts has
 * no top-level string literal, so only the lifted case exists here.
 */
function generateBlock(gs: GenState, topBind: StgBinding): LinkableUnit | undefined {
  const tl = genToplevel(gs, topBind);
  const extraTl = gs.gsGroup.ggsToplevelStats;
  const ci = gs.gsGroup.ggsClosureInfo;
  const si = gs.gsGroup.ggsStatic;
  const unf = gs.gsUnfloated;
  resetGroup(gs);

  const allDeps = collectIds(unf, topBind);
  const topDeps = collectTopIds(topBind);
  const required = hasExport(topBind);
  const stat = mconcatJStgStat([...[...extraTl].reverse(), tl]);
  const syms = topDeps.map((i) => identForId(gs, i));
  return {
    luObjBlock: { oiSymbols: syms, oiClInfo: [...ci].reverse(), oiStatic: [...si].reverse(), oiStat: stat },
    luIdExports: topDeps,
    luOtherExports: [],
    luIdDeps: allDeps,
    luDepSymbols: allDeps.map((i) => identForId(gs, i)),
    luRequired: required,
  };
}

export function genToplevel(gs: GenState, bnd: StgBinding): JStgStat {
  if (bnd.tag === "StgNonRec") return genToplevelDecl(gs, bnd.binder, bnd.rhs);
  return mconcatJStgStat(bnd.pairs.map(([bndr, rhs]) => genToplevelDecl(gs, bndr, rhs)));
}

function genToplevelDecl(gs: GenState, i: Binder, rhs: StgRhs): JStgStat {
  const st = stackState(gs);
  resetSlots(st, () => genToplevelConEntry(gs, i, rhs));
  return resetSlots(st, () => genToplevelRhs(gs, i, rhs));
}

/** Emit the constructor entry when this binder is a data constructor worker.
 *
 * GHC decides that with `isDataConWorkId`; stg.ts's Binder does not record
 * that it is a worker, so a binder whose RHS is a nullary-entry constructor
 * closure is never mistaken for one and this is driven by the RHS alone. */
function genToplevelConEntry(gs: GenState, i: Binder, rhs: StgRhs): void {
  if (rhs.tag === "StgRhsCon" && i.name === rhs.con.name) {
    genSetConInfo(gs, i, rhs.con, stgRhsLive(rhs)); // NoSRT
  }
}

function genSetConInfo(gs: GenState, i: Binder, d: DataCon, l: LiveVars): void {
  const ei = identForDataConEntryId(gs, i);
  const sr = genStaticRefs(gs, l);
  // GHC lists the rep types of `dataConRepArgTys d`; a ghcts DataCon knows
  // only its arity, and a constructor field is a pointer unless it is unboxed.
  const fields = Array.from({ length: d.arity }, () => JSRep.PtrV);
  emitClosureInfo(gs, {
    var: ei,
    regs: { tag: "CIRegs", skip: 0, types: [JSRep.PtrV] },
    name: d.name,
    layout: fixedLayout(fields),
    type: { tag: "CICon", constructor: d.tag },
    static: sr,
  });
  emitToplevel(gs, mkDataEntry(ei));
}

const mkDataEntry = (i: Ident): JStgStat => ({ tag: "FuncStat", ident: i, args: [], body: returnStack });

function genToplevelRhs(gs: GenState, i: Binder, rhs: StgRhs): JStgStat {
  if (rhs.tag === "StgRhsCon") {
    const ii = identForId(gs, i);
    allocConStatic(gs, ii, rhs.con, rhs.args);
    return memptyJStgStat;
  }
  /*
    algorithm:
     - collect all Id refs that are in the global id cache
     - count usage in body for each ref
     - order by increasing use
     - prepend loading lives var to body: body can stay the same
  */
  const eid = identForEntryId(gs, i);
  const idt = identForId(gs, i);
  // genBody's `Type` argument becomes explicit reps (see expr.ts); a top-level
  // binding's result is one lifted boxed value.
  const body = genBody(gs, initExprCtx(i), R2, rhs.args, rhs.body, [{ tag: "BoxedRep", levity: "Lifted" }]);
  const globalOccs_: GlobalOcc[] = globalOccs(gs, body);
  const eidt = eid;
  const lidents = globalOccs_.map((o) => o.global_ident);
  const lids = globalOccs_.map((o) => o.global_id);
  const lidents_ = lidents;
  const sr0 = genStaticRefsRhs(gs, rhs).staticRefs;
  const sr = { staticRefs: sr0.filter((x) => !lidents_.includes(x)) };
  const et = genEntryType(gs, rhs.args);
  const ll = loadLiveFun(gs, lids);

  const isThunk = et.tag === "CIThunk";
  const staticVal: StaticVal = isThunk
    ? { tag: "StaticThunk", init: { name: eidt, args: lidents_.map((l): StaticArg => ({ tag: "StaticObjArg", name: l })) } }
    : { tag: "StaticFun", name: eidt, args: lidents_.map((l): StaticArg => ({ tag: "StaticObjArg", name: l })) };
  const regs: ClosureInfo["regs"] = isThunk
    ? { tag: "CIRegs", skip: 0, types: [JSRep.PtrV] }
    : lidents.length === 0
      ? { tag: "CIRegs", skip: 1, types: rhs.args.flatMap(argJSRep) }
      : { tag: "CIRegs", skip: 0, types: [JSRep.PtrV, ...rhs.args.flatMap(argJSRep)] };
  const upd = isThunk ? updateThunk(stackState(gs), getSettings(gs)) : memptyJStgStat;

  emitClosureInfo(gs, {
    var: eid,
    regs,
    name: idt,
    layout: fixedLayout(lids.map(unaryJSRep)),
    type: et,
    static: sr,
  });
  emitStatic(gs, idt, staticVal);
  return { tag: "FuncStat", ident: eid, args: [], body: mconcatJStgStat([ll, upd, body]) };
}

/** `idJSRep`/`unaryTypeJSRep` stand-ins; see the same note in expr.ts. */
const argJSRep = (i: Binder): JSRep[] => {
  const n = i.arity ?? 1;
  return n === 0 ? [JSRep.VoidV] : n === 2 ? [JSRep.LongV] : [JSRep.PtrV];
};
const unaryJSRep = (i: Binder): JSRep => argJSRep(i)[0];

// ---------------------------------------------------------------------------
// GHC.StgToJS.Linker.Linker, transcribed for want of a Linker module
// ---------------------------------------------------------------------------

/** Declare and do first-pass init of a global object (create the JS object for
 * heap objects). */
export function staticDeclStat(si: StaticInfo): JStgStat {
  const globalIdent = name(si.siVar);
  const declInit = (v: JStgExpr): JStgStat => declAssign_(globalIdent, v);
  const v = si.siVal;
  if (v.tag === "StaticUnboxed") {
    switch (v.value.tag) {
      case "StaticUnboxedBool":
        return declInit(app("h$p", [toJExpr(v.value.value)]));
      case "StaticUnboxedInt":
        return declInit(app("h$p", [jInt(v.value.value)]));
      case "StaticUnboxedDouble":
        return declInit(app("h$p", [jDouble(v.value.value)]));
      case "StaticUnboxedString":
        return declInit(app("h$encodeModifiedUtf8", [jString(v.value.value)]));
      case "StaticUnboxedStringOffset":
        return declInit(jInt(0));
    }
  }
  // CAF initialized in an alternative way
  if (v.tag === "StaticThunk" && v.init === undefined) return appS("h$di", [Var(globalIdent)]);
  return declInit(app("h$d", []));
}

export function staticInitStat(si: StaticInfo): JStgStat {
  const addCcArg = (as: JStgExpr[]): JStgExpr[] => (si.siCC === undefined ? as : [...as, Var(si.siCC)]);
  const v = si.siVal;
  switch (v.tag) {
    case "StaticData":
      return appS("h$sti", addCcArg([global(si.siVar), global(v.name), jsStaticArgs(v.args)]));
    case "StaticFun":
      return appS("h$sti", addCcArg([global(si.siVar), global(v.name), jsStaticArgs(v.args)]));
    case "StaticList":
      return appS("h$stl", addCcArg([global(si.siVar), jsStaticArgs(v.args), v.tail === undefined ? global("null") : global(v.tail)]));
    case "StaticThunk":
      return v.init === undefined
        ? memptyJStgStat
        : appS("h$stc", addCcArg([global(si.siVar), global(v.init.name), jsStaticArgs(v.init.args)]));
    default:
      return memptyJStgStat;
  }
}

/** Assemble the linkable units of one module into runnable JS: declarations,
 * code, info tables, static initialisers - the order GHC's linker uses. */
export function renderModule(config: StgToJSConfig, units: LinkableUnit[]): string {
  const statics = units.flatMap((u) => u.luObjBlock.oiStatic);
  const infos = units.flatMap((u) => u.luObjBlock.oiClInfo);
  const stat: JStgStat = mconcatJStgStat([
    ...statics.map(staticDeclStat),
    ...units.map((u) => u.luObjBlock.oiStat),
    ...infos.map((ci) => closureInfoStat(config.prettyRender, ci)),
    ...statics.map(staticInitStat),
  ]);
  const js: JStat = jsOptimize(jStgStatToJS(stat));
  return renderStat(js);
}

/** Convenience for callers that hold a whole module. */
export function compileModule(config: StgToJSConfig, mod: Module, binds: StgBinding[]): string {
  return renderModule(config, stgToJS(config, mod, binds));
}
