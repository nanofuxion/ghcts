/** Ported from GHC/StgToJS/Types.hs.
 *
 * The shared vocabulary of GHC's JavaScript backend: closure kinds, the JS
 * primitive representations, the register/return files, and the closure
 * metadata the RTS reads back at run time. Only the declarations the RTS and
 * codegen layers actually consume are ported here; the Core-facing halves of
 * Types.hs (GenState, StaticInfo, StackSlot, ...) arrive with their own
 * modules.
 *
 * The numbering below is load-bearing - it is the wire format between
 * generated code and the RTS, not an internal detail. Note the asymmetry:
 * JSRep marshals through the derived `Enum`, but ClosureType marshals
 * through `ctNum`, which is a different numbering entirely.
 */
import type { JStgExpr } from "../js/jstg-syntax.js";

/** ClosureType, in declaration order (the derived `Enum`). Generated code
 * never sees these values: `toJExpr` goes through `ctNum` instead. Both
 * numberings are kept, exactly as in Types.hs. */
export enum ClosureType {
  Thunk = 0,
  Fun = 1,
  Pap = 2,
  Con = 3,
  Blackhole = 4,
  StackFrame = 5,
}

/** `ctNum` - the closure-type tag stored in a closure's info table. This is
 * deliberately different from the derived Enum above (Con is 2 here, 3 there,
 * and StackFrame is -1). */
export function ctNum(t: ClosureType): number {
  switch (t) {
    case ClosureType.Fun:
      return 1;
    case ClosureType.Con:
      return 2;
    case ClosureType.Thunk:
      return 0;
    case ClosureType.Pap:
      return 3;
    case ClosureType.Blackhole:
      return 5;
    case ClosureType.StackFrame:
      return -1;
  }
}

/** GHC emits `show ct` here, i.e. the derived Show - the constructor name
 * exactly as spelled in Types.hs, not an upper-cased variant. */
export function closureTypeName(t: ClosureType): string {
  switch (t) {
    case ClosureType.Thunk:
      return "Thunk";
    case ClosureType.Fun:
      return "Fun";
    case ClosureType.Pap:
      return "Pap";
    case ClosureType.Con:
      return "Con";
    case ClosureType.Blackhole:
      return "Blackhole";
    case ClosureType.StackFrame:
      return "StackFrame";
  }
}

/** JSRep - GHC's JS primitive representations. The numbering is the derived
 * `Enum` ordering, which `instance ToJExpr JSRep` sends to generated code. */
export enum JSRep {
  PtrV = 0,
  VoidV = 1,
  DoubleV = 2,
  IntV = 3,
  LongV = 4,
  AddrV = 5,
  ObjV = 6,
  ArrV = 7,
}

/** Number of JS fields a value of this representation occupies. */
export function varSize(r: JSRep): number {
  switch (r) {
    case JSRep.VoidV:
      return 0;
    case JSRep.LongV:
    case JSRep.AddrV:
      return 2;
    default:
      return 1;
  }
}

export function isVoid(r: JSRep): boolean {
  return r === JSRep.VoidV;
}
export function isPtr(r: JSRep): boolean {
  return r === JSRep.PtrV;
}

/** Registers: R1..R32, in GHC's order. `Regs.hs` maps these onto `h$r1`.. */
export const registerCount = 32;

/** Return registers: h$ret1..h$ret2 plus the special ones. */
export enum StgRet {
  Ret1 = 0,
  Ret2 = 1,
  Ret3 = 2,
  Ret4 = 3,
  Ret5 = 4,
  Ret6 = 5,
  Ret7 = 6,
  Ret8 = 7,
  Ret9 = 8,
  Ret10 = 9,
}

/** CIRegs - how many registers a closure's arguments occupy. */
export type CIRegs =
  | { tag: "CIRegsUnknown" }
  | { tag: "CIRegs"; skip: number; types: JSRep[] };

export const ciRegsUnknown: CIRegs = { tag: "CIRegsUnknown" };
export const ciRegs = (skip: number, types: JSRep[]): CIRegs => ({ tag: "CIRegs", skip, types });

/** CILayout - what the RTS knows about a closure's field layout. */
export type CILayout =
  | { tag: "CILayoutVariable" }
  | { tag: "CILayoutUnknown"; size: number }
  | { tag: "CILayoutFixed"; size: number; fields: JSRep[] };

export const ciLayoutVariable: CILayout = { tag: "CILayoutVariable" };
export const ciLayoutUnknown = (size: number): CILayout => ({ tag: "CILayoutUnknown", size });
export const ciLayoutFixed = (size: number, fields: JSRep[]): CILayout => ({ tag: "CILayoutFixed", size, fields });

/** CIType - which kind of closure this info table describes. */
export type CIType =
  | { tag: "CIFun"; arity: number; regs: number }
  | { tag: "CIThunk" }
  | { tag: "CICon"; constructor: number }
  | { tag: "CIPap" }
  | { tag: "CIBlackhole" }
  | { tag: "CIStackFrame" };

export const ciFun = (arity: number, regs: number): CIType => ({ tag: "CIFun", arity, regs });
export const ciThunk: CIType = { tag: "CIThunk" };
export const ciCon = (constructor: number): CIType => ({ tag: "CICon", constructor });
export const ciPap: CIType = { tag: "CIPap" };
export const ciBlackhole: CIType = { tag: "CIBlackhole" };
export const ciStackFrame: CIType = { tag: "CIStackFrame" };

/** The ClosureType this info table's CIType corresponds to. */
export function ciTypeClosureType(t: CIType): ClosureType {
  switch (t.tag) {
    case "CIFun":
      return ClosureType.Fun;
    case "CIThunk":
      return ClosureType.Thunk;
    case "CICon":
      return ClosureType.Con;
    case "CIPap":
      return ClosureType.Pap;
    case "CIBlackhole":
      return ClosureType.Blackhole;
    case "CIStackFrame":
      return ClosureType.StackFrame;
  }
}

/** CIStatic - static references that must be kept alive. */
export interface CIStatic {
  staticRefs: string[];
}
export const noStatic: CIStatic = { staticRefs: [] };

/** ClosureInfo - the info-table record emitted alongside every closure. */
export interface ClosureInfo {
  /** Name of the JS variable this info table describes. */
  var: string;
  regs: CIRegs;
  /** Descriptive name, used by the RTS only for tracing. */
  name: string;
  layout: CILayout;
  type: CIType;
  static: CIStatic;
}

export function closureInfo(
  var_: string,
  regs: CIRegs,
  name: string,
  layout: CILayout,
  type: CIType,
  static_: CIStatic = noStatic,
): ClosureInfo {
  return { var: var_, regs, name, layout, type, static: static_ };
}

/** StgToJSConfig - the codegen flags. Only the fields the JS-emitting layers
 * read are modelled; GHC's SDocContext/LinkerConfig settings have no TS
 * counterpart. Defaults match GHC's own (-O0, no profiling, no RTS asserts). */
export interface StgToJSConfig {
  inlinePush: boolean;
  inlineBlackhole: boolean;
  inlineLoadRegs: boolean;
  inlineEnter: boolean;
  inlineAlloc: boolean;
  prettyRender: boolean;
  traceRts: boolean;
  assertRts: boolean;
  boundsCheck: boolean;
  debugAlloc: boolean;
  traceForeign: boolean;
  prof: boolean;
  runtimeAssert: boolean;
}

export const defaultStgToJSConfig: StgToJSConfig = {
  inlinePush: false,
  inlineBlackhole: false,
  inlineLoadRegs: false,
  inlineEnter: false,
  inlineAlloc: false,
  prettyRender: false,
  traceRts: false,
  assertRts: false,
  boundsCheck: false,
  debugAlloc: false,
  traceForeign: false,
  prof: false,
  runtimeAssert: false,
};

/** GHC marshals ClosureType/JSRep to JS through `toJExpr . fromEnum`. */
export function repToJExpr(r: JSRep): JStgExpr {
  return { tag: "ValExpr", value: { tag: "JInt", value: BigInt(r) } };
}
/** `instance ToJExpr ClosureType` is `toJExpr . ctNum` - NOT the derived
 * Enum. That is why a closure tag of 4 names no type at all and 5 is
 * Blackhole: ctNum skips 4 and gives StackFrame -1. */
export function closureTypeToJExpr(t: ClosureType): JStgExpr {
  return { tag: "ValExpr", value: { tag: "JInt", value: BigInt(ctNum(t)) } };
}
