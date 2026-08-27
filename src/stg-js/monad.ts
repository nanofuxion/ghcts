/** Ported from GHC/StgToJS/Monad.hs - the JS codegen state monad.
 *
 * GHC's `G` is `StateT GenState IO`. TypeScript has no monad transformers
 * worth emulating, so `GenState` is a mutable class and every `G a` becomes a
 * function taking it as an explicit first parameter - the same convention
 * `src/js/make.ts` uses for `JSM`.
 *
 * This module also carries the half of `GHC.StgToJS.Types` that is Core-facing
 * rather than RTS-facing (GenState, GenGroupState, IdType, IdCache,
 * GlobalIdCache, StackSlot, StaticInfo and friends, OtherSymb, ForeignJSRef);
 * `src/stg-js/types.ts` says in its header that those arrive with their own
 * modules, and GenState is where they are all consumed.
 */
import type { Binder, StgExpr } from "../stg.js";
import type { Ident } from "../js/ident.js";
import type { JStgExpr, JStgStat, JVal } from "../js/jstg-syntax.js";
import type { ClosureInfo, StgToJSConfig } from "./types.js";
// Types.hs's static vocabulary (StaticLit/StaticArg/StaticUnboxed/StaticVal)
// lives in ./literal.ts, with its producers. Type-only, so the cycle with
// literal.ts's `emitStatic` import is erased.
import type { StaticVal } from "./literal.js";

// ---------------------------------------------------------------------------
// Narrow local stand-ins for GHC types ghcts does not have yet
// ---------------------------------------------------------------------------

/** GHC.Unit.Module's `Module`: a unit id plus a module name. Only these two
 * components are ever observed by the JS backend (through
 * `unitModuleStringZ`), so the rest of GHC's Module is not modelled. */
export interface Module {
  unitId: string;
  moduleName: string;
}

/** GHC.Types.SrcLoc's `RealSrcSpan`, reduced to the fields `emitForeign`
 * renders. */
export interface RealSrcSpan {
  file: string;
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
}

/** GHC.Types.ForeignCall's `CCallConv`. */
export type CCallConv = "CCallConv" | "CApiConv" | "StdCallConv" | "PrimCallConv" | "JavaScriptCallConv";

/** GHC.Types.ForeignCall's `Safety`; spelled as in `src/stg.ts`'s ForeignCall. */
export type Safety = "unsafe" | "safe" | "interruptible";

// ---------------------------------------------------------------------------
// GHC.StgToJS.Types: the Core-facing declarations
// ---------------------------------------------------------------------------

/** The type of identifiers, which decides the suffix `makeIdentForId` adds. */
export enum IdType {
  IdPlain,
  IdEntry,
  IdConEntry,
}

/** `IdKey !Word64 !Int !IdType`, flattened to a string so it can key a Map.
 * GHC gets structural Ord for free from the tuple; TS does not. */
export type IdKey = string;

export const idKey = (unique: number, num: number, idType: IdType): IdKey => `${unique}|${num}|${idType}`;

/** `OtherSymb !Module !FastString`, likewise flattened for Set membership. */
export type OtherSymb = string;

export const otherSymb = (mod: Module, sym: string): OtherSymb => `${mod.unitId}:${mod.moduleName}|${sym}`;

/** A stack slot is either known or unknown. */
export type StackSlot = { tag: "SlotId"; id: Binder; size: number } | { tag: "SlotUnknown" };

export const slotUnknown: StackSlot = { tag: "SlotUnknown" };

export interface StaticInfo {
  /** global object */
  siVar: string;
  /** static initialization */
  siVal: StaticVal;
  /** optional CCS name */
  siCC?: Ident;
}

/** A foreign reference to some JS code. */
export interface ForeignJSRef {
  foreignRefSrcSpan: string;
  foreignRefPattern: string;
  foreignRefSafety: Safety;
  foreignRefCConv: CCallConv;
  foreignRefArgs: string[];
  foreignRefResult: string;
}

/** The identifier cache indexed on 'IdKey' local to a module. */
export type IdCache = Map<IdKey, Ident>;

/** The global Identifier Cache, keyed on the generated Ident. */
export type GlobalIdCache = Map<Ident, { key: IdKey; id: Binder }>;

/** The JS code generator state relevant for the current binding group. */
export class GenGroupState {
  /** extra toplevel statements for the binding group */
  ggsToplevelStats: JStgStat[] = [];
  /** closure metadata (info tables) for the binding group */
  ggsClosureInfo: ClosureInfo[] = [];
  /** static (CAF) data in our binding group */
  ggsStatic: StaticInfo[] = [];
  /** stack info for the current expression */
  ggsStack: StackSlot[] = [];
  /** current stack depth */
  ggsStackDepth = 0;
  /** extra dependencies for the linkable unit that contains this group */
  ggsExtraDeps: Set<OtherSymb> = new Set();
  ggsGlobalIdCache: GlobalIdCache = new Map();
  ggsForeignRefs: ForeignJSRef[] = [];
}

/** The JS code generator state. */
export class GenState {
  /** hash consing for identifiers from a Unique */
  gsIdents: IdCache = new Map();
  /** state for the current binding group */
  gsGroup = new GenGroupState();
  /** global (per module) statements (gets included when anything else from
   * the module is used) */
  gsGlobal: JStgStat[] = [];

  constructor(
    /** codegen settings, read-only */
    readonly gsSettings: StgToJSConfig,
    /** current module */
    readonly gsModule: Module,
    /** unique number for the id generator */
    public gsId: number,
    /** unfloated arguments */
    readonly gsUnfloated: Map<number, StgExpr>,
  ) {}
}

// ---------------------------------------------------------------------------
// GHC.StgToJS.Monad
// ---------------------------------------------------------------------------

function initState(config: StgToJSConfig, m: Module, unfloat: Map<number, StgExpr>): GenState {
  return new GenState(config, m, 1, unfloat);
}

export function runG<A>(
  config: StgToJSConfig,
  m: Module,
  unfloat: Map<number, StgExpr>,
  action: (s: GenState) => A,
): A {
  return action(initState(config, m, unfloat));
}

export function modifyGroup(s: GenState, f: (g: GenGroupState) => void): void {
  f(s.gsGroup);
}

/** emit a global (for the current module) toplevel statement */
export function emitGlobal(s: GenState, stat: JStgStat): void {
  s.gsGlobal.unshift(stat);
}

/** add a dependency on a particular symbol to the current group */
export function addDependency(s: GenState, symbol: OtherSymb): void {
  s.gsGroup.ggsExtraDeps.add(symbol);
}

/** emit a top-level statement for the current binding group */
export function emitToplevel(s: GenState, stat: JStgStat): void {
  s.gsGroup.ggsToplevelStats.unshift(stat);
}

/** emit static data for the binding group */
export function emitStatic(s: GenState, ident: string, val: StaticVal, cc?: Ident): void {
  s.gsGroup.ggsStatic.unshift({ siVar: ident, siVal: val, siCC: cc });
}

/** add closure info in our binding group. all heap objects must have closure info */
export function emitClosureInfo(s: GenState, ci: ClosureInfo): void {
  s.gsGroup.ggsClosureInfo.unshift(ci);
}

export function emitForeign(
  s: GenState,
  mbSpan: RealSrcSpan | undefined,
  pat: string,
  safety: Safety,
  cconv: CCallConv,
  argTys: string[],
  resTy: string,
): void {
  const spanTxt =
    mbSpan === undefined
      ? "<unknown>"
      : `${mbSpan.file} (${mbSpan.startLine},${mbSpan.startCol})-(${mbSpan.endLine},${mbSpan.endCol})`;
  s.gsGroup.ggsForeignRefs.unshift({
    foreignRefSrcSpan: spanTxt,
    foreignRefPattern: pat,
    foreignRefSafety: safety,
    foreignRefCConv: cconv,
    foreignRefArgs: argTys,
    foreignRefResult: resTy,
  });
}

/** start with a new binding group */
export function resetGroup(s: GenState): void {
  s.gsGroup = new GenGroupState();
}

export function assertRtsStat(s: GenState, stat: () => JStgStat): JStgStat {
  return s.gsSettings.assertRts ? stat() : { tag: "BlockStat", stats: [] };
}

export function getSettings(s: GenState): StgToJSConfig {
  return s.gsSettings;
}

export function getGlobalIdCache(s: GenState): GlobalIdCache {
  return s.gsGroup.ggsGlobalIdCache;
}

export function setGlobalIdCache(s: GenState, v: GlobalIdCache): void {
  s.gsGroup.ggsGlobalIdCache = v;
}

export interface GlobalOcc {
  global_ident: Ident;
  global_id: Binder;
  global_count: number;
}

/** Collect every Ident occurring in a statement, in occurrence order.
 *
 * GHC.JS.Transform owns this (`identsS`/`identsE`/`identsV`); ghcts has not
 * ported that module, and `globalOccs` is its only consumer here. The two
 * Raw* nodes are ghcts-only escape hatches holding pre-rendered source, so
 * there is nothing to walk inside them. */
function identsS(stat: JStgStat): Ident[] {
  const out: Ident[] = [];
  const goE = (e: JStgExpr): void => {
    switch (e.tag) {
      case "ValExpr":
        goV(e.value);
        return;
      case "SelExpr":
        goE(e.obj);
        out.push(e.field);
        return;
      case "IdxExpr":
        goE(e.obj);
        goE(e.index);
        return;
      case "InfixExpr":
        goE(e.left);
        goE(e.right);
        return;
      case "UOpExpr":
        goE(e.value);
        return;
      case "IfExpr":
        goE(e.cond);
        goE(e.then);
        goE(e.else);
        return;
      case "ApplExpr":
        goE(e.fn);
        e.args.forEach(goE);
        return;
      case "RawExpr":
        return;
    }
  };
  const goV = (v: JVal): void => {
    switch (v.tag) {
      case "JVar":
        out.push(v.ident);
        return;
      case "JList":
        v.values.forEach(goE);
        return;
      case "JHash":
        v.entries.forEach(([, e]) => goE(e));
        return;
      case "JFunc":
        v.args.forEach((i) => out.push(i));
        goS(v.body);
        return;
      default:
        return;
    }
  };
  const goS = (st: JStgStat): void => {
    switch (st.tag) {
      case "DeclStat":
        out.push(st.ident);
        if (st.value !== undefined) goE(st.value);
        return;
      case "ReturnStat":
      case "ThrowStat":
        goE(st.value);
        return;
      case "IfStat":
        goE(st.cond);
        goS(st.then);
        goS(st.else);
        return;
      case "WhileStat":
        goE(st.cond);
        goS(st.body);
        return;
      case "ForStat":
        goS(st.init);
        goE(st.cond);
        goS(st.step);
        goS(st.body);
        return;
      case "ForInStat":
        out.push(st.ident);
        goE(st.obj);
        goS(st.body);
        return;
      case "SwitchStat":
        goE(st.scrut);
        st.cases.forEach(([e, s2]) => {
          goE(e);
          goS(s2);
        });
        goS(st.default);
        return;
      case "TryStat":
        goS(st.body);
        out.push(st.ident);
        goS(st.catch);
        goS(st.finally);
        return;
      case "BlockStat":
        st.stats.forEach(goS);
        return;
      case "ApplStat":
        goE(st.fn);
        st.args.forEach(goE);
        return;
      case "UOpStat":
        goE(st.value);
        return;
      case "AssignStat":
        goE(st.lhs);
        goE(st.rhs);
        return;
      case "LabelStat":
        goS(st.body);
        return;
      case "FuncStat":
        out.push(st.ident);
        st.args.forEach((i) => out.push(i));
        goS(st.body);
        return;
      case "BreakStat":
      case "ContinueStat":
      case "RawStat":
        return;
    }
  };
  goS(stat);
  return out;
}

/** Return number of occurrences of every global id used in the given
 * JStgStat. Sort by increasing occurrence count. */
export function globalOccs(s: GenState, jst: JStgStat): GlobalOcc[] {
  const gidc = getGlobalIdCache(s);
  const gids = new Map<Ident, GlobalOcc>();
  for (const i of identsS(jst)) {
    const found = gidc.get(i);
    if (found === undefined) continue;
    const existing = gids.get(i);
    if (existing === undefined) gids.set(i, { global_ident: i, global_id: found.id, global_count: 1 });
    else existing.global_count += 1;
  }
  // Array.prototype.sort is stable in ES2019+, matching Data.List.sortBy.
  return [...gids.values()].sort((a, b) => a.global_count - b.global_count);
}
