/** Ported from GHC/StgToJS/Closure.hs.
 *
 * Emission of closures and their info tables: `closure`/`conClosure` build the
 * entry function plus its `h$o(...)` metadata, and the `Closure` record plus
 * `newClosure`/`assignClosure`/`copyClosure`/`mkClosure` are the safe way to
 * fill in a heap object's four (five, with the cost centre) fields.
 *
 * TS has no Data.Array, so the four name caches are plain arrays built with
 * the same bounds; the bounds checks in `dataFieldName` & co are kept verbatim
 * (including the pre-existing quirk that `dataName` guards against
 * `nFieldCache` while its cache only runs to `jsClosureCount`).
 */
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { global, memptyJStgStat, mconcatJStgStat } from "../js/jstg-syntax.js";
import type { JSM } from "../js/jstg-monad.js";
import { appS, assign_, jFunction_, jhFromList, jInt, jString, null_, returnStack, toJExpr } from "../js/make.js";
import {
  closureCC,
  closureCC_,
  closureField1,
  closureField1_,
  closureField2,
  closureField2_,
  closureInfo,
  closureInfo_,
  closureMeta,
  closureMeta_,
} from "./heap.js";
import type { CILayout, CIRegs, CIStatic, ClosureInfo } from "./types.js";
import { ciRegs, ClosureType, closureTypeToJExpr, JSRep, noStatic, varSize } from "./types.js";

/** GHC.StgToJS.Utils.mkArityTag - inlined, Utils.hs is not ported. */
const mkArityTag = (arity: number, registers: number): number => arity | (registers << 8);

/** GHC.StgToJS.Types' `instance ToJExpr CIStatic`. */
const ciStaticToJExpr = (s: CIStatic): JStgExpr =>
  s.staticRefs.length === 0 ? null_ : toJExpr(s.staticRefs.map((r) => global(r)));

/** Generate statements to set infotable field values for the given ClosureInfo
 *
 * Depending on debug flag, it generates h$setObjInfo(...) or h$o(...). The
 * latter form doesn't store the pretty-printed name in the closure to save
 * space. */
export function closureInfoStat(debug: boolean, ci: ClosureInfo): JStgStat {
  const t = ((): ClosureType => {
    switch (ci.type.tag) {
      case "CIThunk":
        return ClosureType.Thunk;
      case "CIFun":
        return ClosureType.Fun;
      case "CICon":
        return ClosureType.Con;
      case "CIBlackhole":
        return ClosureType.Blackhole;
      case "CIPap":
        return ClosureType.Pap;
      case "CIStackFrame":
        return ClosureType.StackFrame;
    }
  })();
  const tag = ((): number => {
    switch (ci.type.tag) {
      case "CIFun":
        return mkArityTag(ci.type.arity, ci.type.regs);
      case "CICon":
        return ci.type.constructor;
      default:
        return 0;
    }
  })();
  return setObjInfoL(debug, ci.var, ci.regs, ci.layout, t, ci.name, tag, ci.static);
}

function setObjInfoL(
  debug: boolean,
  obj: Ident,
  rs: CIRegs,
  layout: CILayout,
  t: ClosureType,
  n: string,
  a: number,
  static_: CIStatic,
): JStgStat {
  const size = layout.tag === "CILayoutVariable" ? -1 : layout.size;
  const toTypeList = (fs: JSRep[]): number[] =>
    fs.flatMap((x) => Array.from({ length: varSize(x) }, () => x as number));
  const fieldTypes =
    layout.tag === "CILayoutVariable"
      ? []
      : layout.tag === "CILayoutUnknown"
        ? toTypeList(Array.from({ length: layout.size }, () => JSRep.ObjV))
        : toTypeList(layout.fields);
  return setObjInfo(debug, obj, t, n, fieldTypes, a, size, rs, static_);
}

function setObjInfo(
  debug: boolean,
  obj: Ident,
  t: ClosureType,
  n: string,
  fields: number[],
  a: number,
  size: number,
  regs: CIRegs,
  static_: CIStatic,
): JStgStat {
  const regTag = regs.tag === "CIRegsUnknown" ? -1 : regs.skip + (regs.types.reduce((acc, x) => acc + varSize(x), 0) << 8);
  const objE = toJExpr(obj);
  if (debug) {
    return appS("h$setObjInfo", [
      objE,
      closureTypeToJExpr(t),
      jString(n),
      toJExpr(fields.map(jInt)),
      jInt(a),
      jInt(size),
      jInt(regTag),
      ciStaticToJExpr(static_),
    ]);
  }
  return appS("h$o", [objE, closureTypeToJExpr(t), jInt(a), jInt(size), jInt(regTag), ciStaticToJExpr(static_)]);
}

/** Special case of closures that do not need to generate any @fresh@ names */
export function closure(js: JSM, ci: ClosureInfo, body: (js: JSM) => JStgStat): JStgStat {
  const f = jFunction_(ci.var, body(js));
  return mconcatJStgStat([f, closureInfoStat(false, ci)]);
}

export function conClosure(js: JSM, symbol: Ident, n: string, layout: CILayout, constr: number): JStgStat {
  const ci: ClosureInfo = {
    var: symbol,
    regs: ciRegs(0, [JSRep.PtrV]),
    name: n,
    layout,
    type: { tag: "CICon", constructor: constr },
    static: noStatic,
  };
  return closure(js, ci, () => returnStack);
}

/** Used to pass arguments to newClosure with some safety */
export interface Closure {
  /** InfoTable object */
  clInfo: JStgExpr;
  /** Payload field 1 */
  clField1: JStgExpr;
  /** Payload field 2 */
  clField2: JStgExpr;
  clMeta: JStgExpr;
  clCC?: JStgExpr;
}

export function newClosure(c: Closure): JStgExpr {
  const xs: Array<[string, JStgExpr]> = [
    [closureInfo_, c.clInfo],
    [closureField1_, c.clField1],
    [closureField2_, c.clField2],
    [closureMeta_, c.clMeta],
  ];
  // CC field is optional (probably to minimize code size as we could assign
  // null_, but we get the same effect implicitly)
  const entries = c.clCC === undefined ? xs : [[closureCC_, c.clCC] as [string, JStgExpr], ...xs];
  return { tag: "ValExpr", value: jhFromList(entries) };
}

export function assignClosure(t: JStgExpr, c: Closure): JStgStat {
  return mconcatJStgStat([
    {
      tag: "BlockStat",
      stats: [
        assign_(closureInfo(t), c.clInfo),
        assign_(closureField1(t), c.clField1),
        assign_(closureField2(t), c.clField2),
        assign_(closureMeta(t), c.clMeta),
      ],
    },
    c.clCC === undefined ? memptyJStgStat : assign_(closureCC(t), c.clCC),
  ]);
}

export enum CopyCC {
  CopyCC = 0,
  DontCopyCC = 1,
}

export function copyClosure(copyCc: CopyCC, t: JStgExpr, s: JStgExpr): JStgStat {
  return mconcatJStgStat([
    {
      tag: "BlockStat",
      stats: [
        assign_(closureInfo(t), closureInfo(s)),
        assign_(closureField1(t), closureField1(s)),
        assign_(closureField2(t), closureField2(s)),
        assign_(closureMeta(t), closureMeta(s)),
      ],
    },
    copyCc === CopyCC.DontCopyCC ? memptyJStgStat : assign_(closureCC(t), closureCC(s)),
  ]);
}

export function mkClosure(info: JStgExpr, fields: JStgExpr[], meta: JStgExpr, cc?: JStgExpr): Closure {
  const x1 = fields.length === 0 ? null_ : fields[0];
  const x2 =
    fields.length <= 1
      ? null_
      : fields.length === 2
        ? fields[1]
        : ({
            tag: "ValExpr",
            value: jhFromList(fields.slice(1).map((f, i): [string, JStgExpr] => [dataFieldName(i + 1), f])),
          } as JStgExpr);
  return { clInfo: info, clField1: x1, clField2: x2, clMeta: meta, clCC: cc };
}

// ---------------------------------------------------------------------------
//                              Name Caches
// ---------------------------------------------------------------------------

/** Data names are used in the AST, and logging has determined that 255 is the
 * maximum number we see. */
export const nFieldCache = 255;

/** We use this in the RTS to determine the number of generated closures. These
 * closures use the names cached here, so we bind them to the same number. */
export const jsClosureCount = 24;

/** Cache "dXXX" field names */
const dataFieldCache: string[] = Array.from({ length: nFieldCache + 1 }, (_, i) => `d${i}`);

export function dataFieldName(i: number): string {
  return i < 0 || i > nFieldCache ? `d${i}` : dataFieldCache[i];
}

/** Cache "h$dXXX" names */
const dataCache: string[] = Array.from({ length: jsClosureCount + 1 }, (_, i) => `h$d${i}`);

export function dataName(i: number): string {
  // NB: guarded against nFieldCache, not jsClosureCount - faithful to Closure.hs,
  // where the same mismatch means indices in (jsClosureCount, nFieldCache] index
  // past the cache's upper bound.
  return i < 0 || i > nFieldCache ? `h$d${i}` : dataCache[i];
}

export const allocData = (i: number): JStgExpr => global(dataName(i));

/** Cache "h$cXXX" names */
const clsCache: string[] = Array.from({ length: jsClosureCount + 1 }, (_, i) => `h$c${i}`);

export function clsName(i: number): string {
  return i < 0 || i > jsClosureCount ? `h$c${i}` : clsCache[i];
}

export const allocClsA = (i: number): JStgExpr => global(clsName(i));

/** Cache "xXXX" names */
const varCache: Ident[] = Array.from({ length: jsClosureCount + 1 }, (_, i) => name(`x${i}`));

export function varName(i: number): Ident {
  return i < 0 || i > jsClosureCount ? name(`x${i}`) : varCache[i];
}
