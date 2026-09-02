/** Ported from GHC/StgToJS/Prim.hs (GHC 9.12.2).
 *
 * The primop half of the code generator: `genPrim` maps every GHC primitive
 * operation onto the JavaScript that implements it. The port is deliberately
 * literal - same order, same helper names, same generated JS - so that output
 * can be diffed against GHC's own. Optimisation is a separate pass.
 *
 * Two Haskell-isms have no counterpart here:
 *   - `PrimOp` is a large sum type in GHC.Builtin.PrimOps. ghcts models a
 *     primop as its constructor name (`StgOp`'s `StgPrimOp { op: string }`),
 *     so the giant `case op of` becomes a `switch` over those names.
 *   - `genPrim` takes a Core `Type`, used for exactly one thing: `isBoolTy ty`
 *     in TagToEnumOp. ghcts has no Core types, so the caller passes that one
 *     bit directly (see `PrimOpType`).
 */
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import {
  Add, Sub, Mul, Div, Mod, BOr, BAnd, BXor, BNot, Not, Negate, LAnd, LOr,
  Int, New, PreInc, global, mconcatJStgStat as mconcat, memptyJStgStat as mempty,
} from "../js/jstg-syntax.js";
import type { JSM } from "../js/jstg-monad.js";
import {
  app, appS, assign_, declAssign_, gt_, ge_, lt_, le_, strictEq_, strictNeq_, neq_,
  shl_, shr_, ushr_, land_, lor_, idx_, sel_, if_, ifS, ifBlockS, if10, if01, jwhenS,
  jVar, mask8, mask16, signExtend8, signExtend16, off8, off16, off32, off64,
  returnS, preIncrS, postIncrS, postDecrS, zero_, one_, two_, three_, null_, true_, false_,
  math_abs, math_min, math_max, math_fround, math_exp, math_expm1, math_log, math_log1p,
  math_sqrt, math_sin, math_cos, math_tan, math_asin, math_acos, math_atan,
  math_sinh, math_cosh, math_tanh, math_asinh, math_acosh, math_atanh, math_pow,
  jString,
} from "../js/make.js";
import { isObject } from "./heap.js";
import { foreignRegister, sp, stack } from "./regs.js";
import { StgRet } from "./types.js";
import { zEncodeString } from "./ids.js";
import {
  hdAtomicallyStr, hdAtomicModifyMutVar2Str, hdAtomicModifyMutVarStr, hdBSwap64Str,
  hdBuildCCSPtrStr, hdCastDoubleToWord64Str, hdCastFloatToWord32Str, hdCastWord32ToFloatStr,
  hdCastWord64ToDoubleStr, hdCatchStmStr, hdCatchStr, hdCheckOverlapByteArrayStr,
  hdClearCCSStr, hdClz16Str, hdClz32Str, hdClz64Str, hdClz8Str, hdCompactAdd,
  hdCompactAddWithSharing, hdCompactAllocateBlock, hdCompactContains, hdCompactContainsAny,
  hdCompactFixupPointers, hdCompactGetFirstBlock, hdCompactGetNextBlock, hdCompactNew,
  hdCompactResize, hdCompactSize, hdCompareByteArraysStr, hdComparePointerStr,
  hdCopyMutableArrayStr, hdCopyMutableByteArrayStr, hdCtz16Str, hdCtz32Str, hdCtz64Str,
  hdCtz8Str, hdCurrentThread, hdDataToTagEntryStr, hdDecodeDouble2IntStr,
  hdDecodeDoubleInt64Str, hdDecodeFloatIntStr, hdDelayThread, hdDeRefStablePtr, hdEntryStr,
  hdExitProcess, hdFinalizeWeak, hdFork, hdGetThreadLabel, hdHsMinusInt64Str,
  hdHsMinusWord64Str, hdHsPlusInt64Str, hdHsPlusWord64Str, hdHsQuotInt64Str, hdHsQuotWord64Str,
  hdHsRemInt64Str, hdHsRemWord64Str, hdHsTimesInt2Str, hdHsTimesInt64Str, hdHsTimesWord64Str,
  hdHsUncheckedShiftLLInt64Str, hdHsUncheckedShiftLWord64Str, hdHsUncheckedShiftRAInt64Str,
  hdHsUncheckedShiftRLInt64Str, hdHsUncheckedShiftRWord64Str,
  hdInternalExceptionTypeDivZero, hdInternalExceptionTypeOverflow,
  hdInternalExceptionTypeUnderflow, hdKeepAlive, hdKillThread, hdListThreads, hdLogStr,
  hdMakeStableName, hdMakeStablePtrStr, hdMakeWeak, hdMakeWeakNoFinalizer, hdMaskAsyncStr,
  hdMaskUnintAsyncStr, hdMul2Word32Str, hdMulImulStr, hdMutVarStr, hdMVarStr, hdNewArrayStr,
  hdNewByteArrayStr, hdNewTVar, hdPDep16Str, hdPDep32Str, hdPDep64Str, hdPDep8Str,
  hdPExit16Str, hdPExit32Str, hdPExit64Str, hdPExit8Str, hdPopCnt32Str, hdPopCnt64Str,
  hdPopCntTab, hdPrimOpStr, hdPutMVarStr, hdQuotRem2Word32Str, hdQuotRemWord32Str,
  hdQuotWord32Str, hdReadMVarStr, hdReadTVar, hdReadTVarIO, hdRemWord32Str,
  hdResizeMutableByteArrayStr, hdReverseWordStr, hdShrinkMutableByteArrayStr,
  hdShrinkMutableCharArrayStr, hdSliceArrayStr, hdStableNameInt, hdStablePtrBuf,
  hdStmCatchRetryStr, hdStmRetryStr, hdTagToEnum, hdTakeMVarStr, hdThreadStatus, hdThrowStr,
  hdTraceEventBinaryStr, hdTraceEventStr, hdTraceMarkerStr, hdTryPutMVarStr, hdTryTakeMVarStr,
  hdUnmaskAsyncStr, hdWaitRead, hdWaitWrite, hdWordAdd2, hdWriteTVar, hdYield,
} from "./symbols.js";

// --------------------------------------------------------------------------
// Accessor field names. These live in GHC.StgToJS.Symbols as bare FastStrings
// (not h$-prefixed symbols), so scripts/gen-symbols.mjs - which only harvests
// the hd* symbol bindings - does not emit them. Spellings are Symbols.hs's.
// --------------------------------------------------------------------------
const lngth = "length";
const len = "len";
const slice = "slice";
const arr = "arr";
const dv = "dv";
const val = "val";
const label = "label";
const i3 = "i3";
const u8 = "u8";
const u1 = "u1";
const f6 = "f6";
const f3 = "f3";
const getInt16 = "getInt16";
const getUint16 = "getUint16";
const getInt32 = "getInt32";
const getUint32 = "getUint32";
const getFloat32 = "getFloat32";
const getFloat64 = "getFloat64";
const setInt16 = "setInt16";
const setUint16 = "setUint16";
const setInt32 = "setInt32";
const setUint32 = "setUint32";
const setFloat32 = "setFloat32";
const setFloat64 = "setFloat64";
/** GHC.StgToJS.Symbols.ccStr / ghcjsArray. */
const ccStr = "cc";
const ghcjsArray = "__ghcjsArray";
/** GHC.StgToJS.Heap.closureMeta_. */
const closureMeta_ = "m";
/** GHC.StgToJS.Profiling.jCurrentCCS = SelExpr hdCurrentThread ccs. */
const jCurrentCCS: JStgExpr = sel_(hdCurrentThread, "ccs");

// --------------------------------------------------------------------------
// Result of generating a primop
// --------------------------------------------------------------------------

/** GHC.StgToJS.Types.PrimRes. */
export type PrimRes =
  /** primop is inline, result is assigned directly */
  | { tag: "PrimInline"; stat: JStgStat }
  /** primop is functionlike, argument(s) and result are on the stack */
  | { tag: "PRPrimCall"; stat: JStgStat };

const PrimInline = (stat: JStgStat): PrimRes => ({ tag: "PrimInline", stat });
const PRPrimCall = (stat: JStgStat): PrimRes => ({ tag: "PRPrimCall", stat });

/** A primop, identified by its GHC.Builtin.PrimOps constructor name
 * ("IntAddOp", "ReadArrayOp", ...) - see the module header. */
export type PrimOp = string;

/** The single fact `genPrim` needs from the Core `Type` it is passed in GHC:
 * whether the result type of a TagToEnumOp is Bool. */
export interface PrimOpType {
  isBoolTy: boolean;
}

/**
 * @param js     fresh-identifier supply (Haskell's JSM)
 * @param prof   profiling (cost-centres) enabled
 * @param bound  array bounds-checking enabled
 * @param ty     the primop's result type (only `isBoolTy` is consulted)
 * @param op     the primitive operation
 * @param rs     where to store the result
 * @param as     arguments
 */
export function genPrim(
  js: JSM,
  prof: boolean,
  bound: boolean,
  ty: PrimOpType,
  op: PrimOp,
  rs: JStgExpr[],
  as: JStgExpr[],
): PrimRes {
  const recur = (op2: PrimOp, rs2: JStgExpr[], as2: JStgExpr[]): PrimRes =>
    genPrim(js, prof, bound, ty, op2, rs2, as2);

  switch (op) {
    case "CharGtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(x, y)))); }
    case "CharGeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(x, y)))); }
    case "CharEqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "CharNeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }
    case "CharLtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(x, y)))); }
    case "CharLeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(x, y)))); }
    case "OrdOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }

    case "Int8ToWord8Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, mask8(x))); }
    case "Word8ToInt8Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend8(x))); }
    case "Int16ToWord16Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, mask16(x))); }
    case "Word16ToInt16Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend16(x))); }
    case "Int32ToWord32Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, ushr_(x, zero_))); }
    case "Word32ToInt32Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toI32(x))); }

    // ---------------------------- Int ------------------------------------

    case "IntAddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toI32(Add(x, y)))); }
    case "IntSubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toI32(Sub(x, y)))); }
    case "IntMulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, app(hdMulImulStr, [x, y]))); }
    case "IntMul2Op": { const [c, hr, lr] = rs, [x, y] = as; return PrimInline(appT([c, hr, lr], hdHsTimesInt2Str, [x, y])); }
    case "IntMulMayOfloOp": {
      const [r] = rs, [x, y] = as;
      return PrimInline(jVar(js, (tmp) => mconcat([
        assign_(tmp, Mul(x, y)),
        assign_(r, if01(strictEq_(tmp, toI32(tmp)))),
      ])));
    }
    // GHC's Cmm optimizer may replace a signed quotient by a power of two
    // with a sign-corrected shift before this backend sees it. Keep the
    // general operation exact here; the pattern rewrite belongs in the STG
    // lowering pass because it must know whether the result is quot/rem or a
    // boxed `div` projection.
    case "IntQuotOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toI32(Div(x, y)))); }
    case "IntRemOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, Mod(x, y))); }
    case "IntQuotRemOp": {
      const [q, r] = rs, [x, y] = as;
      return PrimInline(mconcat([
        assign_(q, toI32(Div(x, y))),
        assign_(r, Sub(x, Mul(y, q))),
      ]));
    }
    case "IntAndOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BAnd(x, y))); }
    case "IntOrOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BOr(x, y))); }
    case "IntXorOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BXor(x, y))); }
    case "IntNotOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, BNot(x))); }

    case "IntNegOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toI32(Negate(x)))); }
    // add with carry: overflow == 0 iff no overflow
    case "IntAddCOp": {
      const [r, overf] = rs, [x, y] = as;
      return PrimInline(jVar(js, (tmp) => mconcat([
        assign_(tmp, Add(x, y)),
        assign_(r, toI32(tmp)),
        assign_(overf, if10(neq_(r, tmp))),
      ])));
    }
    case "IntSubCOp": {
      const [r, overf] = rs, [x, y] = as;
      return PrimInline(jVar(js, (tmp) => mconcat([
        assign_(tmp, Sub(x, y)),
        assign_(r, toI32(tmp)),
        assign_(overf, if10(neq_(r, tmp))),
      ])));
    }
    case "IntGtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(x, y)))); }
    case "IntGeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(x, y)))); }
    case "IntEqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "IntNeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }
    case "IntLtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(x, y)))); }
    case "IntLeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(x, y)))); }
    case "ChrOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "IntToWordOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, ushr_(x, zero_))); }
    case "IntToFloatOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "IntToDoubleOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "IntSllOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, shl_(x, y))); }
    case "IntSraOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, shr_(x, y))); }
    case "IntSrlOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toI32(ushr_(x, y)))); }

    // ---------------------------- Int8 ------------------------------------

    case "Int8ToIntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "IntToInt8Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend8(x))); }
    case "Int8NegOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend8(Negate(x)))); }
    case "Int8AddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend8(Add(x, y)))); }
    case "Int8SubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend8(Sub(x, y)))); }
    case "Int8MulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend8(Mul(x, y)))); }
    case "Int8QuotOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend8(quotShortInt(8, x, y)))); }
    case "Int8RemOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend8(remShortInt(8, x, y)))); }
    case "Int8QuotRemOp": {
      const [r1, r2] = rs, [x, y] = as;
      return PrimInline(mconcat([
        assign_(r1, signExtend8(quotShortInt(8, x, y))),
        assign_(r2, signExtend8(remShortInt(8, x, y))),
      ]));
    }
    case "Int8EqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "Int8GeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(shl_(x, Int(24)), shl_(y, Int(24)))))); }
    case "Int8GtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(shl_(x, Int(24)), shl_(y, Int(24)))))); }
    case "Int8LeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(shl_(x, Int(24)), shl_(y, Int(24)))))); }
    case "Int8LtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(shl_(x, Int(24)), shl_(y, Int(24)))))); }
    case "Int8NeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }

    case "Int8SraOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, shr_(x, i))); }
    case "Int8SrlOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, signExtend8(ushr_(mask8(x), i)))); }
    case "Int8SllOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, signExtend8(mask8(shl_(x, i))))); }

    // ---------------------------- Word8 -----------------------------------

    case "Word8ToWordOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, mask8(x))); }
    case "WordToWord8Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, mask8(x))); }

    case "Word8AddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask8(Add(x, y)))); }
    case "Word8SubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask8(Sub(x, y)))); }
    case "Word8MulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask8(Mul(x, y)))); }
    case "Word8QuotOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask8(Div(x, y)))); }
    case "Word8RemOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, Mod(x, y))); }
    case "Word8QuotRemOp": {
      const [r1, r2] = rs, [x, y] = as;
      return PrimInline(mconcat([assign_(r1, toI32(Div(x, y))), assign_(r2, Mod(x, y))]));
    }
    case "Word8EqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "Word8GeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(x, y)))); }
    case "Word8GtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(x, y)))); }
    case "Word8LeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(x, y)))); }
    case "Word8LtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(x, y)))); }
    case "Word8NeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }

    case "Word8AndOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BAnd(x, y))); }
    case "Word8OrOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BOr(x, y))); }
    case "Word8XorOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BXor(x, y))); }
    case "Word8NotOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, BXor(x, Int(0xff)))); }

    case "Word8SllOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, mask8(shl_(x, i)))); }
    case "Word8SrlOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, ushr_(x, i))); }

    // ---------------------------- Int16 -----------------------------------

    case "Int16ToIntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "IntToInt16Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend16(x))); }

    case "Int16NegOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend16(Negate(x)))); }
    case "Int16AddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend16(Add(x, y)))); }
    case "Int16SubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend16(Sub(x, y)))); }
    case "Int16MulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend16(Mul(x, y)))); }
    case "Int16QuotOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend16(quotShortInt(16, x, y)))); }
    case "Int16RemOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, signExtend16(remShortInt(16, x, y)))); }
    case "Int16QuotRemOp": {
      const [r1, r2] = rs, [x, y] = as;
      return PrimInline(mconcat([
        assign_(r1, signExtend16(quotShortInt(16, x, y))),
        assign_(r2, signExtend16(remShortInt(16, x, y))),
      ]));
    }
    case "Int16EqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "Int16GeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(shl_(x, Int(16)), shl_(y, Int(16)))))); }
    case "Int16GtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(shl_(x, Int(16)), shl_(y, Int(16)))))); }
    case "Int16LeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(shl_(x, Int(16)), shl_(y, Int(16)))))); }
    case "Int16LtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(shl_(x, Int(16)), shl_(y, Int(16)))))); }
    case "Int16NeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }

    case "Int16SraOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, shr_(x, i))); }
    case "Int16SrlOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, signExtend16(ushr_(mask16(x), i)))); }
    case "Int16SllOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, signExtend16(shl_(x, i)))); }

    // ---------------------------- Word16 ----------------------------------

    case "Word16ToWordOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "WordToWord16Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, mask16(x))); }

    case "Word16AddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask16(Add(x, y)))); }
    case "Word16SubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask16(Sub(x, y)))); }
    case "Word16MulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask16(Mul(x, y)))); }
    case "Word16QuotOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, mask16(Div(x, y)))); }
    case "Word16RemOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, Mod(x, y))); }
    case "Word16QuotRemOp": {
      const [r1, r2] = rs, [x, y] = as;
      return PrimInline(mconcat([assign_(r1, toI32(Div(x, y))), assign_(r2, Mod(x, y))]));
    }
    case "Word16EqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "Word16GeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(x, y)))); }
    case "Word16GtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(x, y)))); }
    case "Word16LeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(x, y)))); }
    case "Word16LtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(x, y)))); }
    case "Word16NeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }

    case "Word16AndOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BAnd(x, y))); }
    case "Word16OrOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BOr(x, y))); }
    case "Word16XorOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, BXor(x, y))); }
    case "Word16NotOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, BXor(x, Int(0xffff)))); }

    case "Word16SllOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, mask16(shl_(x, i)))); }
    case "Word16SrlOp": { const [r] = rs, [x, i] = as; return PrimInline(assign_(r, ushr_(x, i))); }

    // ---------------------------- Int32 -----------------------------------

    case "Int32ToIntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "IntToInt32Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }

    case "Int32NegOp": return recur("IntNegOp", rs, as);
    case "Int32AddOp": return recur("IntAddOp", rs, as);
    case "Int32SubOp": return recur("IntSubOp", rs, as);
    case "Int32MulOp": return recur("IntMulOp", rs, as);
    case "Int32QuotOp": return recur("IntQuotOp", rs, as);
    case "Int32RemOp": return recur("IntRemOp", rs, as);
    case "Int32QuotRemOp": return recur("IntQuotRemOp", rs, as);

    case "Int32EqOp": return recur("IntEqOp", rs, as);
    case "Int32GeOp": return recur("IntGeOp", rs, as);
    case "Int32GtOp": return recur("IntGtOp", rs, as);
    case "Int32LeOp": return recur("IntLeOp", rs, as);
    case "Int32LtOp": return recur("IntLtOp", rs, as);
    case "Int32NeOp": return recur("IntNeOp", rs, as);

    case "Int32SraOp": return recur("IntSraOp", rs, as);
    case "Int32SrlOp": return recur("IntSrlOp", rs, as);
    case "Int32SllOp": return recur("IntSllOp", rs, as);

    // ---------------------------- Word32 ----------------------------------

    case "Word32ToWordOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "WordToWord32Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }

    case "Word32AddOp": return recur("WordAddOp", rs, as);
    case "Word32SubOp": return recur("WordSubOp", rs, as);
    case "Word32MulOp": return recur("WordMulOp", rs, as);
    case "Word32QuotOp": return recur("WordQuotOp", rs, as);
    case "Word32RemOp": return recur("WordRemOp", rs, as);
    case "Word32QuotRemOp": return recur("WordQuotRemOp", rs, as);

    case "Word32EqOp": return recur("WordEqOp", rs, as);
    case "Word32GeOp": return recur("WordGeOp", rs, as);
    case "Word32GtOp": return recur("WordGtOp", rs, as);
    case "Word32LeOp": return recur("WordLeOp", rs, as);
    case "Word32LtOp": return recur("WordLtOp", rs, as);
    case "Word32NeOp": return recur("WordNeOp", rs, as);

    case "Word32AndOp": return recur("WordAndOp", rs, as);
    case "Word32OrOp": return recur("WordOrOp", rs, as);
    case "Word32XorOp": return recur("WordXorOp", rs, as);
    case "Word32NotOp": return recur("WordNotOp", rs, as);

    case "Word32SllOp": return recur("WordSllOp", rs, as);
    case "Word32SrlOp": return recur("WordSrlOp", rs, as);

    // ---------------------------- Int64 -----------------------------------

    case "Int64ToIntOp": { const [r] = rs, l = as[1]; return PrimInline(assign_(r, toI32(l))); }

    case "Int64NegOp": {
      const [r_h, r_l] = rs, [h, l] = as;
      return PrimInline(mconcat([
        assign_(r_l, toU32(Add(BNot(l), one_))),
        assign_(r_h, toI32(Add(BNot(h), Not(r_l)))),
      ]));
    }

    case "Int64AddOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsPlusInt64Str, [h0, l0, h1, l1])); }
    case "Int64SubOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsMinusInt64Str, [h0, l0, h1, l1])); }
    case "Int64MulOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsTimesInt64Str, [h0, l0, h1, l1])); }
    case "Int64QuotOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsQuotInt64Str, [h0, l0, h1, l1])); }
    case "Int64RemOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsRemInt64Str, [h0, l0, h1, l1])); }

    case "Int64SllOp": { const [hr, lr] = rs, [h, l, n] = as; return PrimInline(appT([hr, lr], hdHsUncheckedShiftLLInt64Str, [h, l, n])); }
    case "Int64SraOp": { const [hr, lr] = rs, [h, l, n] = as; return PrimInline(appT([hr, lr], hdHsUncheckedShiftRAInt64Str, [h, l, n])); }
    case "Int64SrlOp": { const [hr, lr] = rs, [h, l, n] = as; return PrimInline(appT([hr, lr], hdHsUncheckedShiftRLInt64Str, [h, l, n])); }

    case "Int64ToWord64Op": {
      const [r1, r2] = rs, [x1, x2] = as;
      return PrimInline(mconcat([assign_(r1, toU32(x1)), assign_(r2, x2)]));
    }
    case "IntToInt64Op": {
      const [r1, r2] = rs, [x] = as;
      return PrimInline(mconcat([
        assign_(r1, if_(lt_(x, zero_), Negate(one_), zero_)), // sign-extension
        assign_(r2, toU32(x)),
      ]));
    }

    case "Int64EqOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LAnd(strictEq_(l0, l1), strictEq_(h0, h1))))); }
    case "Int64NeOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(strictNeq_(l0, l1), strictNeq_(h0, h1))))); }
    case "Int64GeOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(gt_(h0, h1), LAnd(strictEq_(h0, h1), ge_(l0, l1)))))); }
    case "Int64GtOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(gt_(h0, h1), LAnd(strictEq_(h0, h1), gt_(l0, l1)))))); }
    case "Int64LeOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(lt_(h0, h1), LAnd(strictEq_(h0, h1), le_(l0, l1)))))); }
    case "Int64LtOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(lt_(h0, h1), LAnd(strictEq_(h0, h1), lt_(l0, l1)))))); }

    // ---------------------------- Word64 ----------------------------------

    case "Word64ToWordOp": { const [r] = rs, x2 = as[1]; return PrimInline(assign_(r, x2)); }

    case "WordToWord64Op": {
      const [rh, rl] = rs, [x] = as;
      return PrimInline(mconcat([assign_(rh, zero_), assign_(rl, x)]));
    }

    case "Word64ToInt64Op": {
      const [r1, r2] = rs, [x1, x2] = as;
      return PrimInline(mconcat([assign_(r1, toI32(x1)), assign_(r2, x2)]));
    }

    case "Word64EqOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LAnd(strictEq_(l0, l1), strictEq_(h0, h1))))); }
    case "Word64NeOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(strictNeq_(l0, l1), strictNeq_(h0, h1))))); }
    case "Word64GeOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(gt_(h0, h1), LAnd(strictEq_(h0, h1), ge_(l0, l1)))))); }
    case "Word64GtOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(gt_(h0, h1), LAnd(strictEq_(h0, h1), gt_(l0, l1)))))); }
    case "Word64LeOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(lt_(h0, h1), LAnd(strictEq_(h0, h1), le_(l0, l1)))))); }
    case "Word64LtOp": { const [r] = rs, [h0, l0, h1, l1] = as; return PrimInline(assign_(r, if10(LOr(lt_(h0, h1), LAnd(strictEq_(h0, h1), lt_(l0, l1)))))); }

    case "Word64SllOp": { const [hr, lr] = rs, [h, l, n] = as; return PrimInline(appT([hr, lr], hdHsUncheckedShiftLWord64Str, [h, l, n])); }
    case "Word64SrlOp": { const [hr, lr] = rs, [h, l, n] = as; return PrimInline(appT([hr, lr], hdHsUncheckedShiftRWord64Str, [h, l, n])); }

    case "Word64OrOp": {
      const [hr, hl] = rs, [h0, l0, h1, l1] = as;
      return PrimInline(mconcat([assign_(hr, toU32(BOr(h0, h1))), assign_(hl, toU32(BOr(l0, l1)))]));
    }
    case "Word64AndOp": {
      const [hr, hl] = rs, [h0, l0, h1, l1] = as;
      return PrimInline(mconcat([assign_(hr, toU32(BAnd(h0, h1))), assign_(hl, toU32(BAnd(l0, l1)))]));
    }
    case "Word64XorOp": {
      const [hr, hl] = rs, [h0, l0, h1, l1] = as;
      return PrimInline(mconcat([assign_(hr, toU32(BXor(h0, h1))), assign_(hl, toU32(BXor(l0, l1)))]));
    }
    case "Word64NotOp": {
      const [hr, hl] = rs, [h, l] = as;
      return PrimInline(mconcat([assign_(hr, toU32(BNot(h))), assign_(hl, toU32(BNot(l)))]));
    }

    case "Word64AddOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsPlusWord64Str, [h0, l0, h1, l1])); }
    case "Word64SubOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsMinusWord64Str, [h0, l0, h1, l1])); }
    case "Word64MulOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsTimesWord64Str, [h0, l0, h1, l1])); }
    case "Word64QuotOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsQuotWord64Str, [h0, l0, h1, l1])); }
    case "Word64RemOp": { const [hr, lr] = rs, [h0, l0, h1, l1] = as; return PrimInline(appT([hr, lr], hdHsRemWord64Str, [h0, l0, h1, l1])); }

    // ---------------------------- Word -----------------------------------

    case "WordAddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, ushr_(Add(x, y), zero_))); }
    case "WordAddCOp": {
      const [r, c] = rs, [x, y] = as;
      return PrimInline(jVar(js, (tmp) => mconcat([
        assign_(tmp, Add(x, y)),
        assign_(r, toU32(tmp)),
        assign_(c, if10(strictNeq_(tmp, r))),
      ])));
    }
    case "WordSubCOp": {
      const [r, c] = rs, [x, y] = as;
      return PrimInline(mconcat([assign_(r, toU32(Sub(x, y))), assign_(c, if10(gt_(y, x)))]));
    }
    case "WordAdd2Op": { const [h, l] = rs, [x, y] = as; return PrimInline(appT([h, l], hdWordAdd2, [x, y])); }
    case "WordSubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toU32(Sub(x, y)))); }
    case "WordMulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toU32(app(hdMulImulStr, [x, y])))); }
    case "WordMul2Op": { const [h, l] = rs, [x, y] = as; return PrimInline(appT([h, l], hdMul2Word32Str, [x, y])); }
    case "WordQuotOp": { const [q] = rs, [x, y] = as; return PrimInline(assign_(q, app(hdQuotWord32Str, [x, y]))); }
    case "WordRemOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, app(hdRemWord32Str, [x, y]))); }
    case "WordQuotRemOp": { const [q, r] = rs, [x, y] = as; return PrimInline(appT([q, r], hdQuotRemWord32Str, [x, y])); }
    case "WordQuotRem2Op": { const [q, r] = rs, [xh, xl, y] = as; return PrimInline(appT([q, r], hdQuotRem2Word32Str, [xh, xl, y])); }
    case "WordAndOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toU32(BAnd(x, y)))); }
    case "WordOrOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toU32(BOr(x, y)))); }
    case "WordXorOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toU32(BXor(x, y)))); }
    case "WordNotOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toU32(BNot(x)))); }
    case "WordSllOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, toU32(shl_(x, y)))); }
    case "WordSrlOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, ushr_(x, y))); }
    case "WordToIntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toI32(x))); }
    case "WordGtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(x, y)))); }
    case "WordGeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(x, y)))); }
    case "WordEqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "WordNeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }
    case "WordLtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(x, y)))); }
    case "WordLeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(x, y)))); }
    case "WordToDoubleOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "WordToFloatOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([x]))); }
    case "PopCnt8Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, idx_(hdPopCntTab, mask8(x)))); }
    case "PopCnt16Op": {
      const [r] = rs, [x] = as;
      return PrimInline(assign_(r, Add(idx_(hdPopCntTab, mask8(x)), idx_(hdPopCntTab, mask8(ushr_(x, Int(8)))))));
    }

    case "PopCnt32Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdPopCnt32Str, [x]))); }
    case "PopCnt64Op": { const [r] = rs, [x1, x2] = as; return PrimInline(assign_(r, app(hdPopCnt64Str, [x1, x2]))); }
    case "PopCntOp": { const [r] = rs, [x] = as; return recur("PopCnt32Op", [r], [x]); }
    case "Pdep8Op": { const [r] = rs, [s, m] = as; return PrimInline(assign_(r, app(hdPDep8Str, [s, m]))); }
    case "Pdep16Op": { const [r] = rs, [s, m] = as; return PrimInline(assign_(r, app(hdPDep16Str, [s, m]))); }
    case "Pdep32Op": { const [r] = rs, [s, m] = as; return PrimInline(assign_(r, app(hdPDep32Str, [s, m]))); }
    case "Pdep64Op": { const [ra, rb] = rs, [sa, sb, ma, mb] = as; return PrimInline(appT([ra, rb], hdPDep64Str, [sa, sb, ma, mb])); }
    case "PdepOp": return recur("Pdep32Op", rs, as);
    case "Pext8Op": { const [r] = rs, [s, m] = as; return PrimInline(assign_(r, app(hdPExit8Str, [s, m]))); }
    case "Pext16Op": { const [r] = rs, [s, m] = as; return PrimInline(assign_(r, app(hdPExit16Str, [s, m]))); }
    case "Pext32Op": { const [r] = rs, [s, m] = as; return PrimInline(assign_(r, app(hdPExit32Str, [s, m]))); }
    case "Pext64Op": { const [ra, rb] = rs, [sa, sb, ma, mb] = as; return PrimInline(appT([ra, rb], hdPExit64Str, [sa, sb, ma, mb])); }
    case "PextOp": return recur("Pext32Op", rs, as);

    case "ClzOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdClz32Str, [x]))); }
    case "Clz8Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdClz8Str, [x]))); }
    case "Clz16Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdClz16Str, [x]))); }
    case "Clz32Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdClz32Str, [x]))); }
    case "Clz64Op": { const [r] = rs, [x1, x2] = as; return PrimInline(assign_(r, app(hdClz64Str, [x1, x2]))); }
    case "CtzOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdCtz32Str, [x]))); }
    case "Ctz8Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdCtz8Str, [x]))); }
    case "Ctz16Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdCtz16Str, [x]))); }
    case "Ctz32Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, app(hdCtz32Str, [x]))); }
    case "Ctz64Op": { const [r] = rs, [x1, x2] = as; return PrimInline(assign_(r, app(hdCtz64Str, [x1, x2]))); }

    case "BSwap16Op": {
      const [r] = rs, [x] = as;
      return PrimInline(assign_(r, BOr(shl_(mask8(x), Int(8)), mask8(ushr_(x, Int(8))))));
    }
    case "BSwap32Op": {
      const [r] = rs, [x] = as;
      return PrimInline(assign_(r, toU32(
        BOr(BOr(BOr(shl_(x, Int(24)), shl_(BAnd(x, Int(0xff00)), Int(8))),
                shr_(BAnd(x, Int(0xff0000)), Int(8))),
            ushr_(x, Int(24))))));
    }
    case "BSwap64Op": { const [r1, r2] = rs, [x, y] = as; return PrimInline(appT([r1, r2], hdBSwap64Str, [x, y])); }
    case "BSwapOp": { const [r] = rs, [x] = as; return recur("BSwap32Op", [r], [x]); }

    case "BRevOp": { const [r] = rs, [w] = as; return recur("BRev32Op", [r], [w]); }
    case "BRev8Op": { const [r] = rs, [w] = as; return PrimInline(assign_(r, ushr_(app(hdReverseWordStr, [w]), Int(24)))); }
    case "BRev16Op": { const [r] = rs, [w] = as; return PrimInline(assign_(r, ushr_(app(hdReverseWordStr, [w]), Int(16)))); }
    case "BRev32Op": { const [r] = rs, [w] = as; return PrimInline(assign_(r, app(hdReverseWordStr, [w]))); }
    case "BRev64Op": {
      const [rh, rl] = rs, [h, l] = as;
      return PrimInline(mconcat([
        assign_(rl, app(hdReverseWordStr, [h])),
        assign_(rh, app(hdReverseWordStr, [l])),
      ]));
    }

    // ---------------------------- Narrow ---------------------------------

    case "Narrow8IntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend8(x))); }
    case "Narrow16IntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, signExtend16(x))); }
    case "Narrow32IntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toI32(x))); }
    case "Narrow8WordOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, mask8(x))); }
    case "Narrow16WordOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, mask16(x))); }
    case "Narrow32WordOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toU32(x))); }

    // ---------------------------- Double ---------------------------------

    case "DoubleGtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(x, y)))); }
    case "DoubleGeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(x, y)))); }
    case "DoubleEqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "DoubleNeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }
    case "DoubleLtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(x, y)))); }
    case "DoubleLeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(x, y)))); }
    case "DoubleAddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, Add(x, y))); }
    case "DoubleSubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, Sub(x, y))); }
    case "DoubleMulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, Mul(x, y))); }
    case "DoubleDivOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, Div(x, y))); }
    case "DoubleNegOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, Negate(x))); }
    case "DoubleFabsOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_abs([x]))); }
    case "DoubleMinOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_min([x, y]))); }
    case "DoubleMaxOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_max([x, y]))); }
    case "DoubleToIntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toI32(x))); }
    case "DoubleToFloatOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([x]))); }
    case "DoubleExpOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_exp([x]))); }
    case "DoubleExpM1Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_expm1([x]))); }
    case "DoubleLogOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_log([x]))); }
    case "DoubleLog1POp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_log1p([x]))); }
    case "DoubleSqrtOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_sqrt([x]))); }
    case "DoubleSinOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_sin([x]))); }
    case "DoubleCosOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_cos([x]))); }
    case "DoubleTanOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_tan([x]))); }
    case "DoubleAsinOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_asin([x]))); }
    case "DoubleAcosOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_acos([x]))); }
    case "DoubleAtanOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_atan([x]))); }
    case "DoubleSinhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_sinh([x]))); }
    case "DoubleCoshOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_cosh([x]))); }
    case "DoubleTanhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_tanh([x]))); }
    case "DoubleAsinhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_asinh([x]))); }
    case "DoubleAcoshOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_acosh([x]))); }
    case "DoubleAtanhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_atanh([x]))); }
    case "DoublePowerOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_pow([x, y]))); }
    case "DoubleDecode_2IntOp": { const [s, h, l, e] = rs, [x] = as; return PrimInline(appT([s, h, l, e], hdDecodeDouble2IntStr, [x])); }
    case "DoubleDecode_Int64Op": { const [s1, s2, e] = rs, [d] = as; return PrimInline(appT([e, s1, s2], hdDecodeDoubleInt64Str, [d])); }
    case "CastDoubleToWord64Op": { const [rh, rl] = rs, [x] = as; return PrimInline(appT([rh, rl], hdCastDoubleToWord64Str, [x])); }
    case "CastWord64ToDoubleOp": { const [r] = rs, [h, l] = as; return PrimInline(appT([r], hdCastWord64ToDoubleStr, [h, l])); }

    case "DoubleFMAdd":
    case "DoubleFMSub":
    case "DoubleFNMAdd":
    case "DoubleFNMSub":
      return unhandledPrimop(op, rs, as);

    // ---------------------------- Float ----------------------------------

    case "FloatGtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(gt_(x, y)))); }
    case "FloatGeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(ge_(x, y)))); }
    case "FloatEqOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictEq_(x, y)))); }
    case "FloatNeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(strictNeq_(x, y)))); }
    case "FloatLtOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(lt_(x, y)))); }
    case "FloatLeOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, if10(le_(x, y)))); }
    case "FloatAddOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_fround([Add(x, y)]))); }
    case "FloatSubOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_fround([Sub(x, y)]))); }
    case "FloatMulOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_fround([Mul(x, y)]))); }
    case "FloatDivOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_fround([Div(x, y)]))); }
    case "FloatNegOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, Negate(x))); }
    case "FloatMinOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_min([x, y]))); }
    case "FloatMaxOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_max([x, y]))); }
    case "FloatFabsOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_abs([x]))); }
    case "FloatToIntOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, toI32(x))); }
    case "FloatExpOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_exp([x])]))); }
    case "FloatExpM1Op": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_expm1([x])]))); }
    case "FloatLogOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_log([x])]))); }
    case "FloatLog1POp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_log1p([x])]))); }
    case "FloatSqrtOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_sqrt([x])]))); }
    case "FloatSinOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_sin([x])]))); }
    case "FloatCosOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_cos([x])]))); }
    case "FloatTanOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_tan([x])]))); }
    case "FloatAsinOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_asin([x])]))); }
    case "FloatAcosOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_acos([x])]))); }
    case "FloatAtanOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_atan([x])]))); }
    case "FloatSinhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_sinh([x])]))); }
    case "FloatCoshOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_cosh([x])]))); }
    case "FloatTanhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_tanh([x])]))); }
    case "FloatAsinhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_asinh([x])]))); }
    case "FloatAcoshOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_acosh([x])]))); }
    case "FloatAtanhOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, math_fround([math_atanh([x])]))); }
    case "FloatPowerOp": { const [r] = rs, [x, y] = as; return PrimInline(assign_(r, math_fround([math_pow([x, y])]))); }
    case "FloatToDoubleOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, x)); }
    case "FloatDecode_IntOp": { const [s, e] = rs, [x] = as; return PrimInline(appT([s, e], hdDecodeFloatIntStr, [x])); }
    case "CastFloatToWord32Op": { const [r] = rs, [x] = as; return PrimInline(appT([r], hdCastFloatToWord32Str, [x])); }
    case "CastWord32ToFloatOp": { const [r] = rs, [x] = as; return PrimInline(appT([r], hdCastWord32ToFloatStr, [x])); }

    case "FloatFMAdd":
    case "FloatFMSub":
    case "FloatFNMAdd":
    case "FloatFNMSub":
      return unhandledPrimop(op, rs, as);

    // ---------------------------- Arrays ---------------------------------

    case "NewArrayOp": { const [r] = rs, [l, e] = as; return PrimInline(assign_(r, app(hdNewArrayStr, [l, e]))); }
    case "ReadArrayOp": { const [r] = rs, [a, i] = as; return PrimInline(bnd_arr(bound, a, i, assign_(r, idx_(a, i)))); }
    case "WriteArrayOp": { const [a, i, v] = as; return PrimInline(bnd_arr(bound, a, i, assign_(idx_(a, i), v))); }
    case "SizeofArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, lngth))); }
    case "SizeofMutableArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, lngth))); }
    case "IndexArrayOp": { const [r] = rs, [a, i] = as; return PrimInline(bnd_arr(bound, a, i, assign_(r, idx_(a, i)))); }
    case "UnsafeFreezeArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, a)); }
    case "UnsafeThawArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, a)); }
    case "CopyArrayOp": {
      const [a, o1, ma, o2, n] = as;
      return PrimInline(jVar(js, (tmp) =>
        bnd_arr_range(bound, a, o1, n,
          bnd_arr_range(bound, ma, o2, n,
            mconcat([
              assign_(tmp, Int(0)),
              { tag: "WhileStat", isDo: false, cond: lt_(tmp, n), body: mconcat([
                assign_(idx_(ma, Add(tmp, o2)), idx_(a, Add(tmp, o1))),
                preIncrS(tmp),
              ]) },
            ])))));
    }
    case "CopyMutableArrayOp": {
      const [a1, o1, a2, o2, n] = as;
      return PrimInline(bnd_arr_range(bound, a1, o1, n,
        bnd_arr_range(bound, a2, o2, n,
          appS(hdCopyMutableArrayStr, [a1, o1, a2, o2, n]))));
    }
    case "CloneArrayOp":
    case "CloneMutableArrayOp":
    case "FreezeArrayOp":
    case "ThawArrayOp": {
      const [r] = rs, [a, start, n] = as;
      return PrimInline(bnd_arr_range(bound, a, start, n,
        assign_(r, app(hdSliceArrayStr, [a, start, n]))));
    }

    case "CasArrayOp": {
      const [s, o] = rs, [a, i, old, nw] = as;
      return PrimInline(jVar(js, (tmp) => bnd_arr(bound, a, i, mconcat([
        assign_(tmp, idx_(a, i)),
        ifBlockS(strictEq_(tmp, old),
          [assign_(o, nw), assign_(idx_(a, i), nw), assign_(s, zero_)],
          [assign_(s, one_), assign_(o, tmp)]),
      ]))));
    }

    // ------------------------- Small Arrays ------------------------------

    case "NewSmallArrayOp": { const [a] = rs, [n, e] = as; return PrimInline(assign_(a, app(hdNewArrayStr, [n, e]))); }
    case "ReadSmallArrayOp": { const [r] = rs, [a, i] = as; return PrimInline(bnd_arr(bound, a, i, assign_(r, idx_(a, i)))); }
    case "WriteSmallArrayOp": { const [a, i, e] = as; return PrimInline(bnd_arr(bound, a, i, assign_(idx_(a, i), e))); }
    case "SizeofSmallArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, lngth))); }
    case "SizeofSmallMutableArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, lngth))); }
    case "IndexSmallArrayOp": { const [r] = rs, [a, i] = as; return PrimInline(bnd_arr(bound, a, i, assign_(r, idx_(a, i)))); }
    case "UnsafeFreezeSmallArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, a)); }
    case "UnsafeThawSmallArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, a)); }
    case "CopySmallArrayOp": {
      const [s, si, d, di, n] = as;
      return PrimInline(jVar(js, (tmp) =>
        bnd_arr_range(bound, s, si, n,
          bnd_arr_range(bound, d, di, n,
            mconcat([
              assign_(tmp, Sub(n, one_)),
              { tag: "WhileStat", isDo: false, cond: ge_(tmp, zero_), body: mconcat([
                assign_(idx_(d, Add(di, tmp)), idx_(s, Add(si, tmp))),
                postDecrS(tmp),
              ]) },
            ])))));
    }
    case "CopySmallMutableArrayOp": {
      const [s, si, d, di, n] = as;
      return PrimInline(bnd_arr_range(bound, s, si, n,
        bnd_arr_range(bound, d, di, n,
          appS(hdCopyMutableArrayStr, [s, si, d, di, n]))));
    }

    case "CloneSmallArrayOp":
    case "CloneSmallMutableArrayOp":
    case "FreezeSmallArrayOp":
    case "ThawSmallArrayOp": {
      const [r] = rs, [a, o, n] = as;
      return PrimInline(cloneArray(bound, r, a, o, n));
    }

    case "CasSmallArrayOp": {
      const [s, o] = rs, [a, i, old, nw] = as;
      return PrimInline(jVar(js, (tmp) => bnd_arr(bound, a, i, mconcat([
        assign_(tmp, idx_(a, i)),
        ifBlockS(strictEq_(tmp, old),
          [assign_(o, nw), assign_(idx_(a, i), nw), assign_(s, zero_)],
          [assign_(s, one_), assign_(o, tmp)]),
      ]))));
    }

    // ------------------------- Byte Arrays -------------------------------

    case "NewByteArrayOp_Char": { const [r] = rs, [l] = as; return PrimInline(newByteArray(r, l)); }
    case "NewPinnedByteArrayOp_Char": { const [r] = rs, [l] = as; return PrimInline(newByteArray(r, l)); }
    case "NewAlignedPinnedByteArrayOp_Char": { const [r] = rs, [l] = as; return PrimInline(newByteArray(r, l)); }
    case "MutableByteArrayIsPinnedOp": { const [r] = rs; return PrimInline(assign_(r, one_)); }
    case "ByteArrayIsPinnedOp": { const [r] = rs; return PrimInline(assign_(r, one_)); }
    case "ByteArrayIsWeaklyPinnedOp": { const [r] = rs; return PrimInline(assign_(r, one_)); }
    case "MutableByteArrayIsWeaklyPinnedOp": { const [r] = rs; return PrimInline(assign_(r, one_)); }
    case "ByteArrayContents_Char": { const [a, o] = rs, [b] = as; return PrimInline(mconcat([assign_(a, b), assign_(o, zero_)])); }
    case "MutableByteArrayContents_Char": { const [a, o] = rs, [b] = as; return PrimInline(mconcat([assign_(a, b), assign_(o, zero_)])); }
    case "ShrinkMutableByteArrayOp_Char": { const [a, n] = as; return PrimInline(appS(hdShrinkMutableByteArrayStr, [a, n])); }
    case "ResizeMutableByteArrayOp_Char": { const [r] = rs, [a, n] = as; return PrimInline(assign_(r, app(hdResizeMutableByteArrayStr, [a, n]))); }
    case "UnsafeFreezeByteArrayOp": { const [a] = rs, [b] = as; return PrimInline(assign_(a, b)); }
    case "UnsafeThawByteArrayOp": { const [a] = rs, [b] = as; return PrimInline(assign_(a, b)); }
    case "SizeofByteArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, len))); }
    case "SizeofMutableByteArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, len))); }
    case "GetSizeofMutableByteArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, len))); }

    case "IndexByteArrayOp_Char":
    case "ReadByteArrayOp_Char": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix8(bound, a, i, assign_(r, read_u8(a, i)))); }
    case "IndexByteArrayOp_WideChar":
    case "ReadByteArrayOp_WideChar": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, assign_(r, read_i32(a, i)))); }
    case "IndexByteArrayOp_Int":
    case "ReadByteArrayOp_Int": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, assign_(r, read_i32(a, i)))); }
    case "IndexByteArrayOp_Word":
    case "ReadByteArrayOp_Word": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, assign_(r, read_u32(a, i)))); }
    case "IndexByteArrayOp_Addr":
    case "ReadByteArrayOp_Addr": { const [r, o] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, read_addr(a, i, r, o))); }
    case "IndexByteArrayOp_Float":
    case "ReadByteArrayOp_Float": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, assign_(r, read_f32(a, i)))); }
    case "IndexByteArrayOp_Double":
    case "ReadByteArrayOp_Double": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix64(bound, a, i, assign_(r, read_f64(a, i)))); }
    case "IndexByteArrayOp_StablePtr":
    case "ReadByteArrayOp_StablePtr": { const [r, o] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, read_stableptr(a, i, r, o))); }
    case "IndexByteArrayOp_Int8":
    case "ReadByteArrayOp_Int8": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix8(bound, a, i, assign_(r, read_i8(a, i)))); }
    case "IndexByteArrayOp_Int16":
    case "ReadByteArrayOp_Int16": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix16(bound, a, i, assign_(r, read_i16(a, i)))); }
    case "IndexByteArrayOp_Int32":
    case "ReadByteArrayOp_Int32": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, assign_(r, read_i32(a, i)))); }
    case "IndexByteArrayOp_Int64":
    case "ReadByteArrayOp_Int64": { const [h, l] = rs, [a, i] = as; return PrimInline(bnd_ix64(bound, a, i, read_i64(a, i, h, l))); }
    case "IndexByteArrayOp_Word8":
    case "ReadByteArrayOp_Word8": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix8(bound, a, i, assign_(r, read_u8(a, i)))); }
    case "IndexByteArrayOp_Word16":
    case "ReadByteArrayOp_Word16": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix16(bound, a, i, assign_(r, read_u16(a, i)))); }
    case "IndexByteArrayOp_Word32":
    case "ReadByteArrayOp_Word32": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, assign_(r, read_u32(a, i)))); }
    case "IndexByteArrayOp_Word64":
    case "ReadByteArrayOp_Word64": { const [h, l] = rs, [a, i] = as; return PrimInline(bnd_ix64(bound, a, i, read_u64(a, i, h, l))); }

    case "WriteByteArrayOp_Char": { const [a, i, e] = as; return PrimInline(bnd_ix8(bound, a, i, write_u8(a, i, e))); }
    case "WriteByteArrayOp_WideChar": { const [a, i, e] = as; return PrimInline(bnd_ix32(bound, a, i, write_i32(a, i, e))); }
    case "WriteByteArrayOp_Int": { const [a, i, e] = as; return PrimInline(bnd_ix32(bound, a, i, write_i32(a, i, e))); }
    case "WriteByteArrayOp_Word": { const [a, i, e] = as; return PrimInline(bnd_ix32(bound, a, i, write_u32(a, i, e))); }
    case "WriteByteArrayOp_Addr": { const [a, i, r, o] = as; return PrimInline(bnd_ix32(bound, a, i, write_addr(a, i, r, o))); }
    case "WriteByteArrayOp_Float": { const [a, i, e] = as; return PrimInline(bnd_ix32(bound, a, i, write_f32(a, i, e))); }
    case "WriteByteArrayOp_Double": { const [a, i, e] = as; return PrimInline(bnd_ix64(bound, a, i, write_f64(a, i, e))); }
    case "WriteByteArrayOp_StablePtr": { const [a, i, r, o] = as; return PrimInline(bnd_ix32(bound, a, i, write_stableptr(a, i, r, o))); }
    case "WriteByteArrayOp_Int8": { const [a, i, e] = as; return PrimInline(bnd_ix8(bound, a, i, write_i8(a, i, e))); }
    case "WriteByteArrayOp_Int16": { const [a, i, e] = as; return PrimInline(bnd_ix16(bound, a, i, write_i16(a, i, e))); }
    case "WriteByteArrayOp_Int32": { const [a, i, e] = as; return PrimInline(bnd_ix32(bound, a, i, write_i32(a, i, e))); }
    case "WriteByteArrayOp_Int64": { const [a, i, h, l] = as; return PrimInline(bnd_ix64(bound, a, i, write_i64(a, i, h, l))); }
    case "WriteByteArrayOp_Word8": { const [a, i, e] = as; return PrimInline(bnd_ix8(bound, a, i, write_u8(a, i, e))); }
    case "WriteByteArrayOp_Word16": { const [a, i, e] = as; return PrimInline(bnd_ix16(bound, a, i, write_u16(a, i, e))); }
    case "WriteByteArrayOp_Word32": { const [a, i, e] = as; return PrimInline(bnd_ix32(bound, a, i, write_u32(a, i, e))); }
    case "WriteByteArrayOp_Word64": { const [a, i, h, l] = as; return PrimInline(bnd_ix64(bound, a, i, write_u64(a, i, h, l))); }

    case "CompareByteArraysOp": {
      const [r] = rs, [a1, o1, a2, o2, n] = as;
      return PrimInline(bnd_ba_range(bound, a1, o1, n,
        bnd_ba_range(bound, a2, o2, n,
          assign_(r, app(hdCompareByteArraysStr, [a1, o1, a2, o2, n])))));
    }

    // We assume the arrays aren't overlapping since they're of different types
    // (ByteArray vs MutableByteArray, Addr# vs MutableByteArray#, ...)
    case "CopyByteArrayOp":
    case "CopyAddrToByteArrayOp":
    case "CopyMutableByteArrayToAddrOp":
    case "CopyMutableByteArrayNonOverlappingOp":
    case "CopyAddrToAddrNonOverlappingOp":
    case "CopyByteArrayToAddrOp": {
      const [a1, o1, a2, o2, n] = as;
      return copyByteArray(false, bound, a1, o1, a2, o2, n);
    }

    case "CopyMutableByteArrayOp":
    case "CopyAddrToAddrOp": {
      const [a1, o1, a2, o2, n] = as;
      return copyByteArray(true, bound, a1, o1, a2, o2, n);
    }

    case "SetByteArrayOp": {
      const [a, o, n, v] = as;
      const tmpIdent = js.newIdent();
      const tmp = global(tmpIdent);
      return PrimInline(bnd_ba_range(bound, a, o, n, mconcat([
        declAssign_(tmpIdent, zero_),
        { tag: "WhileStat", isDo: false, cond: lt_(tmp, n), body: mconcat([
          write_u8(a, Add(o, tmp), v),
          postIncrS(tmp),
        ]) },
      ])));
    }
    case "SetAddrRangeOp": return recur("SetByteArrayOp", [], as);

    case "AtomicReadByteArrayOp_Int": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ix32(bound, a, i, assign_(r, read_i32(a, i)))); }
    case "AtomicWriteByteArrayOp_Int": { const [a, i, v] = as; return PrimInline(bnd_ix32(bound, a, i, write_i32(a, i, v))); }
    case "FetchAddByteArrayOp_Int": { const [r] = rs, [a, i, v] = as; return PrimInline(bnd_ix32(bound, a, i, fetchOpByteArray(Add, r, a, i, v))); }
    case "FetchSubByteArrayOp_Int": { const [r] = rs, [a, i, v] = as; return PrimInline(bnd_ix32(bound, a, i, fetchOpByteArray(Sub, r, a, i, v))); }
    case "FetchAndByteArrayOp_Int": { const [r] = rs, [a, i, v] = as; return PrimInline(bnd_ix32(bound, a, i, fetchOpByteArray(BAnd, r, a, i, v))); }
    case "FetchOrByteArrayOp_Int": { const [r] = rs, [a, i, v] = as; return PrimInline(bnd_ix32(bound, a, i, fetchOpByteArray(BOr, r, a, i, v))); }
    case "FetchNandByteArrayOp_Int": { const [r] = rs, [a, i, v] = as; return PrimInline(bnd_ix32(bound, a, i, fetchOpByteArray((x, y) => BNot(BAnd(x, y)), r, a, i, v))); }
    case "FetchXorByteArrayOp_Int": { const [r] = rs, [a, i, v] = as; return PrimInline(bnd_ix32(bound, a, i, fetchOpByteArray(BXor, r, a, i, v))); }

    // ---------------------------- Addr# ----------------------------------

    case "AddrAddOp": { const [a2, o2] = rs, [a, o, i] = as; return PrimInline(mconcat([assign_(a2, a), assign_(o2, Add(o, i))])); }
    case "AddrSubOp": { const [i] = rs, o1 = as[1], o2 = as[3]; return PrimInline(assign_(i, Sub(o1, o2))); }
    case "AddrRemOp": { const [r] = rs, o = as[1], i = as[2]; return PrimInline(assign_(r, Mod(o, i))); }
    // only usable for comparisons within one range
    case "AddrToIntOp": { const [i] = rs, o = as[1]; return PrimInline(assign_(i, o)); }
    case "IntToAddrOp": { const [a, o] = rs, [i] = as; return PrimInline(mconcat([assign_(a, null_), assign_(o, i)])); }
    case "AddrGtOp": { const [r] = rs, [a1, o1, a2, o2] = as; return PrimInline(assign_(r, if10(gt_(app(hdComparePointerStr, [a1, o1, a2, o2]), zero_)))); }
    case "AddrGeOp": { const [r] = rs, [a1, o1, a2, o2] = as; return PrimInline(assign_(r, if10(ge_(app(hdComparePointerStr, [a1, o1, a2, o2]), zero_)))); }
    case "AddrEqOp": { const [r] = rs, [a1, o1, a2, o2] = as; return PrimInline(assign_(r, if10(strictEq_(app(hdComparePointerStr, [a1, o1, a2, o2]), zero_)))); }
    case "AddrNeOp": { const [r] = rs, [a1, o1, a2, o2] = as; return PrimInline(assign_(r, if10(strictNeq_(app(hdComparePointerStr, [a1, o1, a2, o2]), zero_)))); }
    case "AddrLtOp": { const [r] = rs, [a1, o1, a2, o2] = as; return PrimInline(assign_(r, if10(lt_(app(hdComparePointerStr, [a1, o1, a2, o2]), zero_)))); }
    case "AddrLeOp": { const [r] = rs, [a1, o1, a2, o2] = as; return PrimInline(assign_(r, if10(le_(app(hdComparePointerStr, [a1, o1, a2, o2]), zero_)))); }

    // ---------------- Addr Indexing: Unboxed Arrays ----------------------

    case "IndexOffAddrOp_Char":
    case "ReadOffAddrOp_Char": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u8(a, off8(o, i)))); }
    case "IndexOffAddrOp_WideChar":
    case "ReadOffAddrOp_WideChar": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i32(a, off32(o, i)))); }
    case "IndexOffAddrOp_Int":
    case "ReadOffAddrOp_Int": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i32(a, off32(o, i)))); }
    case "IndexOffAddrOp_Word":
    case "ReadOffAddrOp_Word": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u32(a, off32(o, i)))); }
    case "IndexOffAddrOp_Addr":
    case "ReadOffAddrOp_Addr": { const [ra, ro] = rs, [a, o, i] = as; return PrimInline(read_boff_addr(a, off32(o, i), ra, ro)); }
    case "IndexOffAddrOp_Float":
    case "ReadOffAddrOp_Float": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_f32(a, off32(o, i)))); }
    case "IndexOffAddrOp_Double":
    case "ReadOffAddrOp_Double": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_f64(a, off64(o, i)))); }
    case "IndexOffAddrOp_StablePtr":
    case "ReadOffAddrOp_StablePtr": { const [ra, ro] = rs, [a, o, i] = as; return PrimInline(read_boff_stableptr(a, off32(o, i), ra, ro)); }
    case "IndexOffAddrOp_Int8":
    case "ReadOffAddrOp_Int8": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i8(a, off8(o, i)))); }
    case "IndexOffAddrOp_Int16":
    case "ReadOffAddrOp_Int16": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i16(a, off16(o, i)))); }
    case "IndexOffAddrOp_Int32":
    case "ReadOffAddrOp_Int32": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i32(a, off32(o, i)))); }
    case "IndexOffAddrOp_Int64":
    case "ReadOffAddrOp_Int64": { const [h, l] = rs, [a, o, i] = as; return PrimInline(read_boff_i64(a, off64(o, i), h, l)); }
    case "IndexOffAddrOp_Word8":
    case "ReadOffAddrOp_Word8": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u8(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word16":
    case "ReadOffAddrOp_Word16": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u16(a, off16(o, i)))); }
    case "IndexOffAddrOp_Word32":
    case "ReadOffAddrOp_Word32": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u32(a, off32(o, i)))); }
    case "IndexOffAddrOp_Word64":
    case "ReadOffAddrOp_Word64": { const [h, l] = rs, [a, o, i] = as; return PrimInline(read_boff_u64(a, off64(o, i), h, l)); }

    case "WriteOffAddrOp_Char": { const [a, o, i, v] = as; return PrimInline(write_boff_u8(a, off8(o, i), v)); }
    case "WriteOffAddrOp_WideChar": { const [a, o, i, v] = as; return PrimInline(write_boff_i32(a, off32(o, i), v)); }
    case "WriteOffAddrOp_Int": { const [a, o, i, v] = as; return PrimInline(write_boff_i32(a, off32(o, i), v)); }
    case "WriteOffAddrOp_Word": { const [a, o, i, v] = as; return PrimInline(write_boff_u32(a, off32(o, i), v)); }
    case "WriteOffAddrOp_Addr": { const [a, o, i, va, vo] = as; return PrimInline(write_boff_addr(a, off32(o, i), va, vo)); }
    case "WriteOffAddrOp_Float": { const [a, o, i, v] = as; return PrimInline(write_boff_f32(a, off32(o, i), v)); }
    case "WriteOffAddrOp_Double": { const [a, o, i, v] = as; return PrimInline(write_boff_f64(a, off64(o, i), v)); }
    case "WriteOffAddrOp_StablePtr": { const [a, o, i, va, vo] = as; return PrimInline(write_boff_stableptr(a, off32(o, i), va, vo)); }
    case "WriteOffAddrOp_Int8": { const [a, o, i, v] = as; return PrimInline(write_boff_i8(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Int16": { const [a, o, i, v] = as; return PrimInline(write_boff_i16(a, off16(o, i), v)); }
    case "WriteOffAddrOp_Int32": { const [a, o, i, v] = as; return PrimInline(write_boff_i32(a, off32(o, i), v)); }
    case "WriteOffAddrOp_Int64": { const [a, o, i, h, l] = as; return PrimInline(write_boff_i64(a, off64(o, i), h, l)); }
    case "WriteOffAddrOp_Word8": { const [a, o, i, v] = as; return PrimInline(write_boff_u8(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word16": { const [a, o, i, v] = as; return PrimInline(write_boff_u16(a, off16(o, i), v)); }
    case "WriteOffAddrOp_Word32": { const [a, o, i, v] = as; return PrimInline(write_boff_u32(a, off32(o, i), v)); }
    case "WriteOffAddrOp_Word64": { const [a, o, i, h, l] = as; return PrimInline(write_boff_u64(a, off64(o, i), h, l)); }

    case "IndexOffAddrOp_Word8AsChar":
    case "ReadOffAddrOp_Word8AsChar": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u8(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsWideChar":
    case "ReadOffAddrOp_Word8AsWideChar": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i32(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsInt":
    case "ReadOffAddrOp_Word8AsInt": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i32(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsWord":
    case "ReadOffAddrOp_Word8AsWord": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u32(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsAddr":
    case "ReadOffAddrOp_Word8AsAddr": { const [ra, ro] = rs, [a, o, i] = as; return PrimInline(read_boff_addr(a, off8(o, i), ra, ro)); }
    case "IndexOffAddrOp_Word8AsFloat":
    case "ReadOffAddrOp_Word8AsFloat": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_f32(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsDouble":
    case "ReadOffAddrOp_Word8AsDouble": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_f64(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsStablePtr":
    case "ReadOffAddrOp_Word8AsStablePtr": { const [ra, ro] = rs, [a, o, i] = as; return PrimInline(read_boff_stableptr(a, off8(o, i), ra, ro)); }
    case "IndexOffAddrOp_Word8AsInt16":
    case "ReadOffAddrOp_Word8AsInt16": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i16(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsInt32":
    case "ReadOffAddrOp_Word8AsInt32": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_i32(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsInt64":
    case "ReadOffAddrOp_Word8AsInt64": { const [h, l] = rs, [a, o, i] = as; return PrimInline(read_boff_i64(a, off8(o, i), h, l)); }
    case "IndexOffAddrOp_Word8AsWord16":
    case "ReadOffAddrOp_Word8AsWord16": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u16(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsWord32":
    case "ReadOffAddrOp_Word8AsWord32": { const [r] = rs, [a, o, i] = as; return PrimInline(assign_(r, read_boff_u32(a, off8(o, i)))); }
    case "IndexOffAddrOp_Word8AsWord64":
    case "ReadOffAddrOp_Word8AsWord64": { const [h, l] = rs, [a, o, i] = as; return PrimInline(read_boff_u64(a, off8(o, i), h, l)); }

    case "WriteOffAddrOp_Word8AsChar": { const [a, o, i, v] = as; return PrimInline(write_boff_u8(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsWideChar": { const [a, o, i, v] = as; return PrimInline(write_boff_i32(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsInt": { const [a, o, i, v] = as; return PrimInline(write_boff_i32(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsWord": { const [a, o, i, v] = as; return PrimInline(write_boff_u32(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsAddr": { const [a, o, i, va, vo] = as; return PrimInline(write_boff_addr(a, off8(o, i), va, vo)); }
    case "WriteOffAddrOp_Word8AsFloat": { const [a, o, i, v] = as; return PrimInline(write_boff_f32(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsDouble": { const [a, o, i, v] = as; return PrimInline(write_boff_f64(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsStablePtr": { const [a, o, i, va, vo] = as; return PrimInline(write_boff_stableptr(a, off8(o, i), va, vo)); }
    case "WriteOffAddrOp_Word8AsInt16": { const [a, o, i, v] = as; return PrimInline(write_boff_i16(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsInt32": { const [a, o, i, v] = as; return PrimInline(write_boff_i32(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsInt64": { const [a, o, i, h, l] = as; return PrimInline(write_boff_i64(a, off8(o, i), h, l)); }
    case "WriteOffAddrOp_Word8AsWord16": { const [a, o, i, v] = as; return PrimInline(write_boff_u16(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsWord32": { const [a, o, i, v] = as; return PrimInline(write_boff_u32(a, off8(o, i), v)); }
    case "WriteOffAddrOp_Word8AsWord64": { const [a, o, i, h, l] = as; return PrimInline(write_boff_u64(a, off8(o, i), h, l)); }

    // ------------------------ Mutable variables --------------------------

    case "NewMutVarOp": { const [r] = rs, [x] = as; return PrimInline(assign_(r, New(app(hdMutVarStr, [x])))); }
    case "ReadMutVarOp": { const [r] = rs, [m] = as; return PrimInline(assign_(r, sel_(m, val))); }
    case "WriteMutVarOp": { const [m, x] = as; return PrimInline(assign_(sel_(m, val), x)); }
    case "AtomicModifyMutVar2Op": { const [r1, r2] = rs, [m, f] = as; return PrimInline(appT([r1, r2], hdAtomicModifyMutVar2Str, [m, f])); }
    case "AtomicModifyMutVar_Op": { const [r1, r2] = rs, [m, f] = as; return PrimInline(appT([r1, r2], hdAtomicModifyMutVarStr, [m, f])); }

    case "AtomicSwapMutVarOp": {
      const [r] = rs, [mv, v] = as;
      return PrimInline(mconcat([assign_(r, sel_(mv, val)), assign_(sel_(mv, val), v)]));
    }
    case "CasMutVarOp": {
      const [status, r] = rs, [mv, o, n] = as;
      return PrimInline(ifS(strictEq_(sel_(mv, val), o),
        mconcat([assign_(status, zero_), assign_(r, n), assign_(sel_(mv, val), n)]),
        mconcat([assign_(status, one_), assign_(r, sel_(mv, val))])));
    }

    // ---------------------------- Exceptions -----------------------------

    case "CatchOp": { const [a, handler] = as; return PRPrimCall(returnS(app(hdCatchStr, [a, handler]))); }

    // fully ignore the result arity as it can use 1 or 2 slots, depending on
    // the return type.
    case "RaiseOp": { const [a] = as; return PRPrimCall(returnS(app(hdThrowStr, [a, false_]))); }
    case "RaiseIOOp": { const [a] = as; return PRPrimCall(returnS(app(hdThrowStr, [a, false_]))); }
    case "RaiseUnderflowOp": return PRPrimCall(returnS(app(hdThrowStr, [hdInternalExceptionTypeUnderflow, false_])));
    case "RaiseOverflowOp": return PRPrimCall(returnS(app(hdThrowStr, [hdInternalExceptionTypeOverflow, false_])));
    case "RaiseDivZeroOp": return PRPrimCall(returnS(app(hdThrowStr, [hdInternalExceptionTypeDivZero, false_])));
    case "MaskAsyncExceptionsOp": { const [a] = as; return PRPrimCall(returnS(app(hdMaskAsyncStr, [a]))); }
    case "MaskUninterruptibleOp": { const [a] = as; return PRPrimCall(returnS(app(hdMaskUnintAsyncStr, [a]))); }
    case "UnmaskAsyncExceptionsOp": { const [a] = as; return PRPrimCall(returnS(app(hdUnmaskAsyncStr, [a]))); }

    case "MaskStatus": { const [r] = rs; return PrimInline(assign_(r, app("h$maskStatus", []))); }

    // ------------- STM-accessible Mutable Variables ----------------------

    case "AtomicallyOp": { const [a] = as; return PRPrimCall(returnS(app(hdAtomicallyStr, [a]))); }
    case "RetryOp": return PRPrimCall(returnS(app(hdStmRetryStr, [])));
    case "CatchRetryOp": { const [a, b] = as; return PRPrimCall(returnS(app(hdStmCatchRetryStr, [a, b]))); }
    case "CatchSTMOp": { const [a, h] = as; return PRPrimCall(returnS(app(hdCatchStmStr, [a, h]))); }
    case "NewTVarOp": { const [tv] = rs, [v] = as; return PrimInline(assign_(tv, app(hdNewTVar, [v]))); }
    case "ReadTVarOp": { const [r] = rs, [tv] = as; return PrimInline(assign_(r, app(hdReadTVar, [tv]))); }
    case "ReadTVarIOOp": { const [r] = rs, [tv] = as; return PrimInline(assign_(r, app(hdReadTVarIO, [tv]))); }
    case "WriteTVarOp": { const [tv, v] = as; return PrimInline(appS(hdWriteTVar, [tv, v])); }

    // ------------ Synchronized Mutable Variables -------------------------

    case "NewMVarOp": { const [r] = rs; return PrimInline(assign_(r, New(app(hdMVarStr, [])))); }
    case "TakeMVarOp": { const [m] = as; return PRPrimCall(returnS(app(hdTakeMVarStr, [m]))); }
    case "TryTakeMVarOp": { const [r, v] = rs, [m] = as; return PrimInline(appT([r, v], hdTryTakeMVarStr, [m])); }
    case "PutMVarOp": { const [m, v] = as; return PRPrimCall(returnS(app(hdPutMVarStr, [m, v]))); }
    case "TryPutMVarOp": { const [r] = rs, [m, v] = as; return PrimInline(assign_(r, app(hdTryPutMVarStr, [m, v]))); }
    case "ReadMVarOp": { const [m] = as; return PRPrimCall(returnS(app(hdReadMVarStr, [m]))); }
    case "TryReadMVarOp": {
      const [r, v] = rs, [m] = as;
      return PrimInline(mconcat([
        assign_(v, sel_(m, val)),
        assign_(r, if01(strictEq_(v, null_))),
      ]));
    }
    case "IsEmptyMVarOp": { const [r] = rs, [m] = as; return PrimInline(assign_(r, if10(strictEq_(sel_(m, val), null_)))); }

    // ------------------------- Delay/Wait Ops ----------------------------

    case "DelayOp": { const [t] = as; return PRPrimCall(returnS(app(hdDelayThread, [t]))); }
    case "WaitReadOp": { const [fd] = as; return PRPrimCall(returnS(app(hdWaitRead, [fd]))); }
    case "WaitWriteOp": { const [fd] = as; return PRPrimCall(returnS(app(hdWaitWrite, [fd]))); }

    // -------------------- Concurrency Primitives -------------------------

    case "ForkOp": { const [x] = as; return PRPrimCall(returnS(app(hdFork, [x, true_]))); }
    // ignore processor argument
    case "ForkOnOp": { const x = as[1]; return PRPrimCall(returnS(app(hdFork, [x, true_]))); }
    case "KillThreadOp": { const [tid, ex] = as; return PRPrimCall(returnS(app(hdKillThread, [tid, ex]))); }
    case "YieldOp": return PRPrimCall(returnS(app(hdYield, [])));
    case "MyThreadIdOp": { const [r] = rs; return PrimInline(assign_(r, hdCurrentThread)); }
    case "IsCurrentThreadBoundOp": { const [r] = rs; return PrimInline(assign_(r, one_)); }
    // don't need to do anything as long as we have eager blackholing
    case "NoDuplicateOp": return PrimInline(mempty);
    case "ThreadStatusOp": { const [stat, cap, locked] = rs, [tid] = as; return PrimInline(appT([stat, cap, locked], hdThreadStatus, [tid])); }
    case "ListThreadsOp": { const [r] = rs; return PrimInline(appT([r], hdListThreads, [])); }
    case "GetThreadLabelOp": { const [r1, r2] = rs, [t] = as; return PrimInline(appT([r1, r2], hdGetThreadLabel, [t])); }
    case "LabelThreadOp": { const [t, l] = as; return PrimInline(assign_(sel_(t, label), l)); }

    // -------------------------- Weak Pointers ----------------------------

    case "MkWeakOp": { const [r] = rs, [o, b, c] = as; return PrimInline(assign_(r, app(hdMakeWeak, [o, b, c]))); }
    case "MkWeakNoFinalizerOp": { const [r] = rs, [o, b] = as; return PrimInline(assign_(r, app(hdMakeWeakNoFinalizer, [o, b]))); }
    case "AddCFinalizerToWeakOp": { const [r] = rs; return PrimInline(assign_(r, one_)); }
    case "DeRefWeakOp": {
      const [f, v] = rs, [w] = as;
      return PrimInline(mconcat([
        assign_(v, sel_(w, val)),
        assign_(f, if01(strictEq_(v, null_))),
      ]));
    }
    case "FinalizeWeakOp": { const [fl, fin] = rs, [w] = as; return PrimInline(appT([fin, fl], hdFinalizeWeak, [w])); }
    case "TouchOp": return PrimInline(mempty);
    case "KeepAliveOp": { const [x, f] = as; return PRPrimCall(returnS(app(hdKeepAlive, [x, f]))); }

    // ----------------- Stable pointers and names -------------------------

    case "MakeStablePtrOp": {
      const [s1, s2] = rs, [a] = as;
      return PrimInline(mconcat([
        assign_(s1, hdStablePtrBuf),
        assign_(s2, app(hdMakeStablePtrStr, [a])),
      ]));
    }
    case "DeRefStablePtrOp": { const [r] = rs, s2 = as[1]; return PrimInline(assign_(r, app(hdDeRefStablePtr, [s2]))); }
    case "EqStablePtrOp": { const [r] = rs, sa2 = as[1], sb2 = as[3]; return PrimInline(assign_(r, if10(strictEq_(sa2, sb2)))); }

    case "MakeStableNameOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, app(hdMakeStableName, [a]))); }
    case "StableNameToIntOp": { const [r] = rs, [s] = as; return PrimInline(assign_(r, app(hdStableNameInt, [s]))); }

    // ----------------------- Compact normal form -------------------------

    case "CompactNewOp": { const [c] = rs, [s] = as; return PrimInline(assign_(c, app(hdCompactNew, [s]))); }
    case "CompactResizeOp": { const [c, s] = as; return PrimInline(appS(hdCompactResize, [c, s])); }
    case "CompactContainsOp": { const [r] = rs, [c, v] = as; return PrimInline(assign_(r, app(hdCompactContains, [c, v]))); }
    case "CompactContainsAnyOp": { const [r] = rs, [v] = as; return PrimInline(assign_(r, app(hdCompactContainsAny, [v]))); }
    case "CompactGetFirstBlockOp": { const [ra, ro, s] = rs, [c] = as; return PrimInline(appT([ra, ro, s], hdCompactGetFirstBlock, [c])); }
    case "CompactGetNextBlockOp": { const [ra, ro, s] = rs, [c, a, o] = as; return PrimInline(appT([ra, ro, s], hdCompactGetNextBlock, [c, a, o])); }
    case "CompactAllocateBlockOp": { const [ra, ro] = rs, [size, sa, so] = as; return PrimInline(appT([ra, ro], hdCompactAllocateBlock, [size, sa, so])); }
    case "CompactFixupPointersOp": {
      const [c, newroota, newrooto] = rs, [blocka, blocko, roota, rooto] = as;
      return PrimInline(appT([c, newroota, newrooto], hdCompactFixupPointers, [blocka, blocko, roota, rooto]));
    }
    case "CompactAdd": { const [c, o] = as; return PRPrimCall(returnS(app(hdCompactAdd, [c, o]))); }
    case "CompactAddWithSharing": { const [c, o] = as; return PRPrimCall(returnS(app(hdCompactAddWithSharing, [c, o]))); }
    case "CompactSize": { const [s] = rs, [c] = as; return PrimInline(assign_(s, app(hdCompactSize, [c]))); }

    // ------------------- Unsafe pointer equality -------------------------

    case "ReallyUnsafePtrEqualityOp": { const [r] = rs, [p1, p2] = as; return PrimInline(assign_(r, if10(strictEq_(p1, p2)))); }

    // ---------------------------- Parallelism ----------------------------

    case "ParOp": { const [r] = rs; return PrimInline(assign_(r, zero_)); }
    case "SparkOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, a)); }
    case "NumSparks": { const [r] = rs; return PrimInline(assign_(r, zero_)); }

    // ----------------------- Tag to enum stuff ---------------------------

    case "DataToTagSmallOp":
    case "DataToTagLargeOp": {
      const [d] = as;
      return PRPrimCall(mconcat([
        assign_(idx_(stack, PreInc(sp)), global(hdDataToTagEntryStr)),
        returnS(app(hdEntryStr, [d])),
      ]));
    }
    case "TagToEnumOp": {
      const [r] = rs, [tag] = as;
      return PrimInline(ty.isBoolTy
        ? assign_(r, if_(tag, true_, false_))
        : assign_(r, app(hdTagToEnum, [tag])));
    }

    // ----------------------- Bytecode operations -------------------------

    case "AddrToAnyOp": { const [r] = rs, [d] = as; return PrimInline(assign_(r, d)); }

    // ------------------------- Profiling (CCS) ---------------------------

    case "GetCCSOfOp": {
      const [a, o] = rs, [obj] = as;
      return PrimInline(mconcat(prof
        ? [
          assign_(a, if_(isObject(obj), app(hdBuildCCSPtrStr, [sel_(obj, ccStr)]), null_)),
          assign_(o, zero_),
        ]
        : [assign_(a, null_), assign_(o, zero_)]));
    }

    case "GetCurrentCCSOp": {
      const [a, o] = rs;
      const ptr = prof ? app(hdBuildCCSPtrStr, [jCurrentCCS]) : null_;
      return PrimInline(mconcat([assign_(a, ptr), assign_(o, zero_)]));
    }

    case "ClearCCSOp": { const [x] = as; return PRPrimCall(returnS(app(hdClearCCSStr, [x]))); }

    // ---------------------------- Eventlog -------------------------------

    case "TraceEventOp": { const [ed, eo] = as; return PrimInline(appS(hdTraceEventStr, [ed, eo])); }
    case "TraceEventBinaryOp": { const [ed, eo, l] = as; return PrimInline(appS(hdTraceEventBinaryStr, [ed, eo, l])); }
    case "TraceMarkerOp": { const [ed, eo] = as; return PrimInline(appS(hdTraceMarkerStr, [ed, eo])); }

    // ---------------------------- ByteArray ------------------------------

    case "IndexByteArrayOp_Word8AsChar":
    case "ReadByteArrayOp_Word8AsChar": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba8(bound, a, i, assign_(r, read_boff_u8(a, i)))); }
    case "IndexByteArrayOp_Word8AsWideChar":
    case "ReadByteArrayOp_Word8AsWideChar": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, assign_(r, read_boff_i32(a, i)))); }
    case "IndexByteArrayOp_Word8AsAddr":
    case "ReadByteArrayOp_Word8AsAddr": { const [r, o] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, read_boff_addr(a, i, r, o))); }
    case "IndexByteArrayOp_Word8AsFloat":
    case "ReadByteArrayOp_Word8AsFloat": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, assign_(r, read_boff_f32(a, i)))); }
    case "IndexByteArrayOp_Word8AsDouble":
    case "ReadByteArrayOp_Word8AsDouble": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba64(bound, a, i, assign_(r, read_boff_f64(a, i)))); }
    case "IndexByteArrayOp_Word8AsStablePtr":
    case "ReadByteArrayOp_Word8AsStablePtr": { const [r, o] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, read_boff_stableptr(a, i, r, o))); }
    case "IndexByteArrayOp_Word8AsInt16":
    case "ReadByteArrayOp_Word8AsInt16": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba16(bound, a, i, assign_(r, read_boff_i16(a, i)))); }
    case "IndexByteArrayOp_Word8AsInt32":
    case "ReadByteArrayOp_Word8AsInt32": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, assign_(r, read_boff_i32(a, i)))); }
    case "IndexByteArrayOp_Word8AsInt64":
    case "ReadByteArrayOp_Word8AsInt64": { const [h, l] = rs, [a, i] = as; return PrimInline(bnd_ba64(bound, a, i, read_boff_i64(a, i, h, l))); }
    case "IndexByteArrayOp_Word8AsInt":
    case "ReadByteArrayOp_Word8AsInt": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, assign_(r, read_boff_i32(a, i)))); }
    case "IndexByteArrayOp_Word8AsWord16":
    case "ReadByteArrayOp_Word8AsWord16": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba16(bound, a, i, assign_(r, read_boff_u16(a, i)))); }
    case "IndexByteArrayOp_Word8AsWord32":
    case "ReadByteArrayOp_Word8AsWord32": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, assign_(r, read_boff_u32(a, i)))); }
    case "IndexByteArrayOp_Word8AsWord64":
    case "ReadByteArrayOp_Word8AsWord64": { const [h, l] = rs, [a, i] = as; return PrimInline(bnd_ba64(bound, a, i, read_boff_u64(a, i, h, l))); }
    case "IndexByteArrayOp_Word8AsWord":
    case "ReadByteArrayOp_Word8AsWord": { const [r] = rs, [a, i] = as; return PrimInline(bnd_ba32(bound, a, i, assign_(r, read_boff_u32(a, i)))); }

    // Note the asymmetry with the Index/Read cases above: GHC writes an *i8*
    // here, not a u8. Kept verbatim.
    case "WriteByteArrayOp_Word8AsChar": { const [a, i, e] = as; return PrimInline(bnd_ba8(bound, a, i, write_boff_i8(a, i, e))); }
    case "WriteByteArrayOp_Word8AsWideChar": { const [a, i, e] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_i32(a, i, e))); }
    case "WriteByteArrayOp_Word8AsAddr": { const [a, i, r, o] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_addr(a, i, r, o))); }
    case "WriteByteArrayOp_Word8AsFloat": { const [a, i, e] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_f32(a, i, e))); }
    case "WriteByteArrayOp_Word8AsDouble": { const [a, i, e] = as; return PrimInline(bnd_ba64(bound, a, i, write_boff_f64(a, i, e))); }
    case "WriteByteArrayOp_Word8AsStablePtr": { const [a, i, , o] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_i32(a, i, o))); }
    case "WriteByteArrayOp_Word8AsInt16": { const [a, i, e] = as; return PrimInline(bnd_ba16(bound, a, i, write_boff_i16(a, i, e))); }
    case "WriteByteArrayOp_Word8AsInt32": { const [a, i, e] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_i32(a, i, e))); }
    case "WriteByteArrayOp_Word8AsInt64": { const [a, i, h, l] = as; return PrimInline(bnd_ba64(bound, a, i, write_boff_i64(a, i, h, l))); }
    case "WriteByteArrayOp_Word8AsInt": { const [a, i, e] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_i32(a, i, e))); }
    case "WriteByteArrayOp_Word8AsWord16": { const [a, i, e] = as; return PrimInline(bnd_ba16(bound, a, i, write_boff_u16(a, i, e))); }
    case "WriteByteArrayOp_Word8AsWord32": { const [a, i, e] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_u32(a, i, e))); }
    case "WriteByteArrayOp_Word8AsWord64": { const [a, i, h, l] = as; return PrimInline(bnd_ba64(bound, a, i, write_boff_u64(a, i, h, l))); }
    case "WriteByteArrayOp_Word8AsWord": { const [a, i, e] = as; return PrimInline(bnd_ba32(bound, a, i, write_boff_u32(a, i, e))); }

    case "CasByteArrayOp_Int": { const [r] = rs, [a, i, o, n] = as; return PrimInline(bnd_ix32(bound, a, i, casOp(read_i32, write_i32, r, a, i, o, n))); }
    case "CasByteArrayOp_Int8": { const [r] = rs, [a, i, o, n] = as; return PrimInline(bnd_ix8(bound, a, i, casOp(read_i8, write_i8, r, a, i, o, n))); }
    case "CasByteArrayOp_Int16": { const [r] = rs, [a, i, o, n] = as; return PrimInline(bnd_ix16(bound, a, i, casOp(read_i16, write_i16, r, a, i, o, n))); }
    case "CasByteArrayOp_Int32": { const [r] = rs, [a, i, o, n] = as; return PrimInline(bnd_ix32(bound, a, i, casOp(read_i32, write_i32, r, a, i, o, n))); }

    case "CasByteArrayOp_Int64": {
      const [rh, rl] = rs, [a, i, oh, ol, nh, nl] = as;
      return PrimInline(bnd_ix64(bound, a, i, casOp2(read_i64, write_i64, [rh, rl], a, i, [oh, ol], [nh, nl])));
    }

    case "CasAddrOp_Addr": {
      const [ra, ro] = rs, [a, o, oa, oo, na, no] = as;
      return PrimInline(casOp2(read_boff_addr, write_boff_addr, [ra, ro], a, o, [oa, oo], [na, no]));
    }
    case "CasAddrOp_Word": { const [r] = rs, [a, o, old, nw] = as; return PrimInline(casOp(read_u32, write_u32, r, a, o, old, nw)); }
    case "CasAddrOp_Word8": { const [r] = rs, [a, o, old, nw] = as; return PrimInline(casOp(read_u8, write_u8, r, a, o, old, nw)); }
    case "CasAddrOp_Word16": { const [r] = rs, [a, o, old, nw] = as; return PrimInline(casOp(read_u16, write_u16, r, a, o, old, nw)); }
    case "CasAddrOp_Word32": { const [r] = rs, [a, o, old, nw] = as; return PrimInline(casOp(read_u32, write_u32, r, a, o, old, nw)); }
    case "CasAddrOp_Word64": {
      const [rh, rl] = rs, [a, o, oh, ol, nh, nl] = as;
      return PrimInline(casOp2(read_u64, write_u64, [rh, rl], a, o, [oh, ol], [nh, nl]));
    }

    case "FetchAddAddrOp_Word": { const [r] = rs, [a, o, v] = as; return PrimInline(fetchOpAddr(Add, r, a, o, v)); }
    case "FetchSubAddrOp_Word": { const [r] = rs, [a, o, v] = as; return PrimInline(fetchOpAddr(Sub, r, a, o, v)); }
    case "FetchAndAddrOp_Word": { const [r] = rs, [a, o, v] = as; return PrimInline(fetchOpAddr(BAnd, r, a, o, v)); }
    case "FetchNandAddrOp_Word": { const [r] = rs, [a, o, v] = as; return PrimInline(fetchOpAddr((x, y) => BNot(BAnd(x, y)), r, a, o, v)); }
    case "FetchOrAddrOp_Word": { const [r] = rs, [a, o, v] = as; return PrimInline(fetchOpAddr(BOr, r, a, o, v)); }
    case "FetchXorAddrOp_Word": { const [r] = rs, [a, o, v] = as; return PrimInline(fetchOpAddr(BXor, r, a, o, v)); }

    case "InterlockedExchange_Addr": {
      const [ra, ro] = rs, [a1, o1, a2, o2] = as;
      return PrimInline(mconcat([
        read_boff_addr(a1, o1, ra, ro),
        write_boff_addr(a1, o1, a2, o2),
      ]));
    }
    case "InterlockedExchange_Word": {
      const [r] = rs, [a, o, w] = as;
      return PrimInline(mconcat([
        assign_(r, read_boff_u32(a, o)),
        write_boff_u32(a, o, w),
      ]));
    }

    case "ShrinkSmallMutableArrayOp_Char": { const [a, n] = as; return PrimInline(appS(hdShrinkMutableCharArrayStr, [a, n])); }
    case "GetSizeofSmallMutableArrayOp": { const [r] = rs, [a] = as; return PrimInline(assign_(r, sel_(a, lngth))); }

    case "AtomicReadAddrOp_Word": { const [r] = rs, [a, o] = as; return PrimInline(assign_(r, read_boff_u32(a, o))); }
    case "AtomicWriteAddrOp_Word": { const [a, o, w] = as; return PrimInline(write_boff_u32(a, o, w)); }

    // ------------------------ Unhandled primops --------------------------

    case "NewPromptTagOp":
    case "PromptOp":
    case "Control0Op":
    case "NewIOPortOp":
    case "ReadIOPortOp":
    case "WriteIOPortOp":
    case "GetSparkOp":
    case "AnyToAddrOp":
    case "MkApUpd0_Op":
    case "NewBCOOp":
    case "UnpackClosureOp":
    case "ClosureSizeOp":
    case "GetApStackValOp":
    // should be easily implementable with o.f.n
    case "WhereFromOp":
    case "SetThreadAllocationCounter":
      return unhandledPrimop(op, rs, as);

    // ---------------------------- Prefetch -------------------------------

    case "PrefetchByteArrayOp3":
    case "PrefetchMutableByteArrayOp3":
    case "PrefetchAddrOp3":
    case "PrefetchValueOp3":
    case "PrefetchByteArrayOp2":
    case "PrefetchMutableByteArrayOp2":
    case "PrefetchAddrOp2":
    case "PrefetchValueOp2":
    case "PrefetchByteArrayOp1":
    case "PrefetchMutableByteArrayOp1":
    case "PrefetchAddrOp1":
    case "PrefetchValueOp1":
    case "PrefetchByteArrayOp0":
    case "PrefetchMutableByteArrayOp0":
    case "PrefetchAddrOp0":
    case "PrefetchValueOp0":
      return noOp();

    default:
      // Vectors are unsupported on the JS backend: they do not make much sense
      // given support for arrays and the lack of SIMD in JS, and any rolled
      // implementation would carry no performance guarantee.
      if (op.startsWith("Vec")) return unhandledPrimop(op, rs, as);
      throw new Error(`genPrim: unknown primop ${op}`);
  }
}

/** Warn at runtime and dispatch to the h$primop_* fallback in the RTS.
 *
 * GHC renders the primop with `ppr`, giving its *source* name ("int8ToInt#");
 * ghcts only carries the constructor name, so that is what is logged and
 * z-encoded here. */
function unhandledPrimop(op: PrimOp, rs: JStgExpr[], as: JStgExpr[]): PrimRes {
  return PrimInline(mconcat([
    appS(hdLogStr, [jString(`warning, unhandled primop: ${op} (${rs.length},${as.length})`)]),
    appS(hdPrimOpStr + zEncodeString(op), as),
    // copyRes
    mconcat(rs.map((r, n) => assign_(r, foreignRegister(StgRet.Ret1 + n)))),
  ]));
}

/** A No Op, used for primops the JS platform cannot or does not support. For
 * example, the prefetching primops do not make sense on the JS platform
 * because we do not have enough control over memory. */
const noOp = (): PrimRes => PrimInline(mempty);

/** tuple returns */
function appT(rrs: JStgExpr[], f: string, xs: JStgExpr[]): JStgStat {
  if (rrs.length === 0) return appS(f, xs);
  const [r, ...rest] = rrs;
  return mconcat([
    assign_(r, app(f, xs)),
    mconcat(rest.map((r2, n) => assign_(r2, foreignRegister(StgRet.Ret1 + n)))),
  ]);
}

// --------------------------------------------------------------------------
//                          ByteArray indexing
//
// For every ByteArray, the RTS creates the following views:
//  i3: Int32 view
//  u8: Word8 view
//  u1: Word16 view
//  f3: Float32 view
//  f6: Float64 view
//  dv: generic DataView
// It seems a bit weird to mix Int and Word views like this, but perhaps they
// are the more common.
//
// See 'h$newByteArray' in 'ghc/rts/js/mem.js' for details.
//
// Note that *byte* indexing can only be done with the generic DataView. Use
// read_boff_* and write_boff_* for this.
// --------------------------------------------------------------------------

const idx_i32 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_(sel_(a, i3), i);
const idx_u8 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_(sel_(a, u8), i);
const idx_u16 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_(sel_(a, u1), i);
const idx_f64 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_(sel_(a, f6), i);
const idx_f32 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_(sel_(a, f3), i);

const read_u8 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_u8(a, i);
const read_u16 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_u16(a, i);
const read_u32 = (a: JStgExpr, i: JStgExpr): JStgExpr => toU32(idx_i32(a, i));
const read_i8 = (a: JStgExpr, i: JStgExpr): JStgExpr => signExtend8(idx_u8(a, i));
const read_i16 = (a: JStgExpr, i: JStgExpr): JStgExpr => signExtend16(idx_u16(a, i));
const read_i32 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_i32(a, i);
const read_f32 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_f32(a, i);
const read_f64 = (a: JStgExpr, i: JStgExpr): JStgExpr => idx_f64(a, i);

const read_u64 = (a: JStgExpr, i: JStgExpr, rh: JStgExpr, rl: JStgExpr): JStgStat => mconcat([
  assign_(rl, read_u32(a, shl_(i, one_))),
  assign_(rh, read_u32(a, Add(one_, shl_(i, one_)))),
]);

const read_i64 = (a: JStgExpr, i: JStgExpr, rh: JStgExpr, rl: JStgExpr): JStgStat => mconcat([
  assign_(rl, read_u32(a, shl_(i, one_))),
  assign_(rh, read_i32(a, Add(one_, shl_(i, one_)))),
]);

// --------------------------------------------------------------------------
//                                 Addr#
// --------------------------------------------------------------------------

const write_addr = (a: JStgExpr, i: JStgExpr, r: JStgExpr, o: JStgExpr): JStgStat => mconcat([
  write_i32(a, i, o),
  // create the hidden array for arrays if it doesn't exist
  ifS(Not(sel_(a, arr)), assign_(sel_(a, arr), { tag: "ValExpr", value: { tag: "JList", values: [] } }), mempty),
  assign_(idx_(sel_(a, arr), shl_(i, two_)), r),
]);

const read_addr = (a: JStgExpr, i: JStgExpr, r: JStgExpr, o: JStgExpr): JStgStat => mconcat([
  assign_(o, read_i32(a, i)),
  assign_(r, if_(land_(sel_(a, arr), idx_(sel_(a, arr), shl_(i, two_))),
    idx_(sel_(a, arr), shl_(i, two_)),
    null_)),
]);

const read_boff_addr = (a: JStgExpr, i: JStgExpr, r: JStgExpr, o: JStgExpr): JStgStat => mconcat([
  assign_(o, read_boff_i32(a, i)),
  assign_(r, if_(land_(sel_(a, arr), idx_(sel_(a, arr), i)),
    idx_(sel_(a, arr), i),
    null_)),
]);

const write_boff_addr = (a: JStgExpr, i: JStgExpr, r: JStgExpr, o: JStgExpr): JStgStat => mconcat([
  write_boff_i32(a, i, o),
  // create the hidden array for arrays if it doesn't exist
  ifS(Not(sel_(a, arr)), assign_(sel_(a, arr), { tag: "ValExpr", value: { tag: "JList", values: [] } }), mempty),
  assign_(idx_(sel_(a, arr), i), r),
]);

// --------------------------------------------------------------------------
//                               StablePtr
// --------------------------------------------------------------------------

const read_stableptr = (a: JStgExpr, i: JStgExpr, r: JStgExpr, o: JStgExpr): JStgStat => mconcat([
  assign_(o, read_i32(a, i)),
  ifS(strictEq_(o, zero_), assign_(r, null_), assign_(r, hdStablePtrBuf)),
]);

const read_boff_stableptr = (a: JStgExpr, i: JStgExpr, r: JStgExpr, o: JStgExpr): JStgStat => mconcat([
  assign_(o, read_boff_i32(a, i)),
  ifS(strictEq_(o, zero_), assign_(r, null_), assign_(r, hdStablePtrBuf)),
]);

// don't store "r" as it must be h$stablePtrBuf or null
const write_stableptr = (a: JStgExpr, i: JStgExpr, _r: JStgExpr, o: JStgExpr): JStgStat => write_i32(a, i, o);
const write_boff_stableptr = (a: JStgExpr, i: JStgExpr, _r: JStgExpr, o: JStgExpr): JStgStat => write_boff_i32(a, i, o);

const write_u8 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_u8(a, i), v);
const write_u16 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_u16(a, i), v);
const write_u32 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_i32(a, i), v);
const write_i8 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_u8(a, i), v);
const write_i16 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_u16(a, i), v);
const write_i32 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_i32(a, i), v);
const write_f32 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_f32(a, i), v);
const write_f64 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => assign_(idx_f64(a, i), v);

const write_u64 = (a: JStgExpr, i: JStgExpr, h: JStgExpr, l: JStgExpr): JStgStat => mconcat([
  write_u32(a, shl_(i, one_), l),
  write_u32(a, Add(one_, shl_(i, one_)), h),
]);

const write_i64 = (a: JStgExpr, i: JStgExpr, h: JStgExpr, l: JStgExpr): JStgStat => mconcat([
  write_u32(a, shl_(i, one_), l),
  write_i32(a, Add(one_, shl_(i, one_)), h),
]);

// Data View helper functions: byte indexed!

const write_boff_i8 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => write_i8(a, i, v);
const write_boff_u8 = (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => write_u8(a, i, v);
const dvSet = (m: string) => (a: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat =>
  ({ tag: "ApplStat", fn: sel_(sel_(a, dv), m), args: [i, v, true_] });
const write_boff_i16 = dvSet(setInt16);
const write_boff_u16 = dvSet(setUint16);
const write_boff_i32 = dvSet(setInt32);
const write_boff_u32 = dvSet(setUint32);
const write_boff_f32 = dvSet(setFloat32);
const write_boff_f64 = dvSet(setFloat64);

const write_boff_i64 = (a: JStgExpr, i: JStgExpr, h: JStgExpr, l: JStgExpr): JStgStat => mconcat([
  write_boff_i32(a, Add(i, Int(4)), h),
  write_boff_u32(a, i, l),
]);
const write_boff_u64 = (a: JStgExpr, i: JStgExpr, h: JStgExpr, l: JStgExpr): JStgStat => mconcat([
  write_boff_u32(a, Add(i, Int(4)), h),
  write_boff_u32(a, i, l),
]);

const read_boff_i8 = (a: JStgExpr, i: JStgExpr): JStgExpr => read_i8(a, i);
const read_boff_u8 = (a: JStgExpr, i: JStgExpr): JStgExpr => read_u8(a, i);
const dvGet = (m: string) => (a: JStgExpr, i: JStgExpr): JStgExpr =>
  ({ tag: "ApplExpr", fn: sel_(sel_(a, dv), m), args: [i, true_] });
const read_boff_i16 = dvGet(getInt16);
const read_boff_u16 = dvGet(getUint16);
const read_boff_i32 = dvGet(getInt32);
const read_boff_u32 = dvGet(getUint32);
const read_boff_f32 = dvGet(getFloat32);
const read_boff_f64 = dvGet(getFloat64);

const read_boff_i64 = (a: JStgExpr, i: JStgExpr, rh: JStgExpr, rl: JStgExpr): JStgStat => mconcat([
  assign_(rh, read_boff_i32(a, Add(i, Int(4)))),
  assign_(rl, read_boff_u32(a, i)),
]);
const read_boff_u64 = (a: JStgExpr, i: JStgExpr, rh: JStgExpr, rl: JStgExpr): JStgStat => mconcat([
  assign_(rh, read_boff_u32(a, Add(i, Int(4)))),
  assign_(rl, read_boff_u32(a, i)),
]);

type BinOp = (x: JStgExpr, y: JStgExpr) => JStgExpr;

const fetchOpByteArray = (op2: BinOp, tgt: JStgExpr, src: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => mconcat([
  assign_(tgt, read_i32(src, i)),
  write_i32(src, i, op2(tgt, v)),
]);

const fetchOpAddr = (op2: BinOp, tgt: JStgExpr, src: JStgExpr, i: JStgExpr, v: JStgExpr): JStgStat => mconcat([
  assign_(tgt, read_boff_u32(src, i)),
  write_boff_u32(src, i, op2(tgt, v)),
]);

function casOp(
  read: (a: JStgExpr, i: JStgExpr) => JStgExpr,
  write: (a: JStgExpr, i: JStgExpr, v: JStgExpr) => JStgStat,
  tgt: JStgExpr,
  src: JStgExpr,
  i: JStgExpr,
  old: JStgExpr,
  nw: JStgExpr,
): JStgStat {
  return mconcat([
    assign_(tgt, read(src, i)),
    ifS(strictEq_(tgt, old), write(src, i, nw), mempty),
  ]);
}

function casOp2(
  read: (a: JStgExpr, i: JStgExpr, r1: JStgExpr, r2: JStgExpr) => JStgStat,
  write: (a: JStgExpr, i: JStgExpr, v1: JStgExpr, v2: JStgExpr) => JStgStat,
  [tgt1, tgt2]: [JStgExpr, JStgExpr],
  src: JStgExpr,
  i: JStgExpr,
  [old1, old2]: [JStgExpr, JStgExpr],
  [new1, new2]: [JStgExpr, JStgExpr],
): JStgStat {
  return mconcat([
    read(src, i, tgt1, tgt2),
    ifS(land_(strictEq_(tgt2, old2), strictEq_(tgt1, old1)), write(src, i, new1, new2), mempty),
  ]);
}

// --------------------------------------------------------------------------
//                             Lifted Arrays
// --------------------------------------------------------------------------

function cloneArray(bound_check: boolean, tgt: JStgExpr, src: JStgExpr, start: JStgExpr, length_: JStgExpr): JStgStat {
  return bnd_arr_range(bound_check, src, start, length_, mconcat([
    assign_(tgt, { tag: "ApplExpr", fn: sel_(src, slice), args: [start, Add(length_, start)] }),
    assign_(sel_(tgt, closureMeta_), zero_),
    assign_(sel_(tgt, ghcjsArray), true_),
  ]));
}

const newByteArray = (tgt: JStgExpr, length_: JStgExpr): JStgStat =>
  assign_(tgt, app(hdNewByteArrayStr, [length_]));

/** Check that index is positive and below a max value. Halt the process with
 * error code 134 otherwise. This is used to implement -fcheck-prim-bounds */
function check_bound(max_index: JStgExpr, do_check: boolean, i: JStgExpr, r: JStgStat): JStgStat {
  if (!do_check) return r;
  return mconcat([
    jwhenS(lor_(lt_(i, zero_), ge_(i, max_index)), returnS(app(hdExitProcess, [Int(134)]))),
    r,
  ]);
}

/** Bounds checking using ".length" property (Arrays) */
const bnd_arr = (do_check: boolean, a: JStgExpr, i: JStgExpr, r: JStgStat): JStgStat =>
  check_bound(sel_(a, lngth), do_check, i, r);

/** Range bounds checking using ".length" property (Arrays). Empty ranges
 * trivially pass the check. */
function bnd_arr_range(do_check: boolean, a: JStgExpr, i: JStgExpr, n: JStgExpr, r: JStgStat): JStgStat {
  if (!do_check) return r;
  return ifS(lt_(n, zero_), returnS(app(hdExitProcess, [Int(134)])),
    ifS(strictEq_(n, zero_), r,
      bnd_arr(true, a, i, bnd_arr(true, a, Add(i, Sub(n, one_)), r))));
}

/** Bounds checking using ".len" property (ByteArrays) */
const bnd_ba = (do_check: boolean, a: JStgExpr, i: JStgExpr, r: JStgStat): JStgStat =>
  check_bound(sel_(a, len), do_check, i, r);

/** ByteArray bounds checking (byte offset, 8-bit value) */
const bnd_ba8 = bnd_ba;

/** ByteArray bounds checking (byte offset, 16-bit value). Checks the
 * un-incremented index too: (idx + 1) may be in range while idx isn't. */
const bnd_ba16 = (do_check: boolean, a: JStgExpr, idx: JStgExpr, r: JStgStat): JStgStat =>
  bnd_ba(do_check, a, idx, bnd_ba(do_check, a, Add(idx, one_), r));

/** ByteArray bounds checking (byte offset, 32-bit value) */
const bnd_ba32 = (do_check: boolean, a: JStgExpr, idx: JStgExpr, r: JStgStat): JStgStat =>
  bnd_ba(do_check, a, idx, bnd_ba(do_check, a, Add(idx, three_), r));

/** ByteArray bounds checking (byte offset, 64-bit value) */
const bnd_ba64 = (do_check: boolean, a: JStgExpr, idx: JStgExpr, r: JStgStat): JStgStat =>
  bnd_ba(do_check, a, idx, bnd_ba(do_check, a, Add(idx, Int(7)), r));

/** ByteArray bounds checking (8-bit offset, 8-bit value) */
const bnd_ix8 = bnd_ba8;

/** ByteArray bounds checking (16-bit offset, 16-bit value) */
const bnd_ix16 = (do_check: boolean, a: JStgExpr, idx: JStgExpr, r: JStgStat): JStgStat =>
  bnd_ba16(do_check, a, shl_(idx, one_), r);

/** ByteArray bounds checking (32-bit offset, 32-bit value) */
const bnd_ix32 = (do_check: boolean, a: JStgExpr, idx: JStgExpr, r: JStgStat): JStgStat =>
  bnd_ba32(do_check, a, shl_(idx, two_), r);

/** ByteArray bounds checking (64-bit offset, 64-bit value) */
const bnd_ix64 = (do_check: boolean, a: JStgExpr, idx: JStgExpr, r: JStgStat): JStgStat =>
  bnd_ba64(do_check, a, shl_(idx, three_), r);

/** Bounds checking on a range and using ".len" property (ByteArrays). Empty
 * ranges trivially pass the check. */
function bnd_ba_range(do_check: boolean, xs: JStgExpr, i: JStgExpr, n: JStgExpr, r: JStgStat): JStgStat {
  if (!do_check) return r;
  return ifS(lt_(n, zero_), returnS(app(hdExitProcess, [Int(134)])),
    ifS(strictEq_(n, zero_), r,
      bnd_ba(true, xs, Add(i, Sub(n, one_)), bnd_ba(true, xs, i, r))));
}

function checkOverlapByteArray(
  do_check: boolean, a1: JStgExpr, o1: JStgExpr, a2: JStgExpr, o2: JStgExpr, n: JStgExpr, r: JStgStat,
): JStgStat {
  if (!do_check) return r;
  return ifS(app(hdCheckOverlapByteArrayStr, [a1, o1, a2, o2, n]), r,
    returnS(app(hdExitProcess, [Int(134)])));
}

function copyByteArray(
  allow_overlap: boolean, bound: boolean,
  a1: JStgExpr, o1: JStgExpr, a2: JStgExpr, o2: JStgExpr, n: JStgExpr,
): PrimRes {
  const body = appS(hdCopyMutableByteArrayStr, [a1, o1, a2, o2, n]);
  const overlap = allow_overlap ? body : checkOverlapByteArray(bound, a1, o1, a2, o2, n, body);
  return PrimInline(bnd_ba_range(bound, a1, o1, n, bnd_ba_range(bound, a2, o2, n, overlap)));
}

/** e|0 (32 bit signed integer truncation) required because of JS numbers. e|0
 * converts e to an Int32. Note that e|0 _is still a Double_ because
 * JavaScript. So (x|0) * (y|0) can still return values outside of the Int32
 * range. You have been warned! */
const toI32 = (e: JStgExpr): JStgExpr => BOr(e, zero_);

/** e>>>0 (32 bit unsigned integer truncation), required because of JS numbers.
 * e>>>0 converts e to a Word32, so (-2147483648) >>> 0 = 2147483648 and
 * ((-2147483648) >>> 0) | 0 = -2147483648. */
const toU32 = (e: JStgExpr): JStgExpr => ushr_(e, zero_);

function quotShortInt(bits: number, x: JStgExpr, y: JStgExpr): JStgExpr {
  const shift = Int(32 - bits);
  const signed = (z: JStgExpr): JStgExpr => shr_(shl_(z, shift), shift);
  return BAnd(Div(signed(x), signed(y)), Int(2n ** BigInt(bits) - 1n));
}

function remShortInt(bits: number, x: JStgExpr, y: JStgExpr): JStgExpr {
  const shift = Int(32 - bits);
  const signed = (z: JStgExpr): JStgExpr => shr_(shl_(z, shift), shift);
  return BAnd(Mod(signed(x), signed(y)), Int(2n ** BigInt(bits) - 1n));
}
