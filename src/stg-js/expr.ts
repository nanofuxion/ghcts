/** Port of GHC.StgToJS.Expr (ghc-9.12.2-release): code generation of
 * expressions.
 *
 * Structure, names and case order follow Expr.hs literally. `G a` becomes a
 * function taking the mutable `GenState` as its first argument, matching the
 * convention the rest of src/stg-js uses.
 *
 * Where Expr.hs consults Core facilities ghcts has no counterpart for
 * (`idType`, `idDetails`, `idFunRepArity`, `isStrictType`, `isJoinId`,
 * `isOneShotBndr`, `primOpIsReallyInline`), this port takes the *slower
 * correct* branch rather than guessing. Each such spot is marked
 * `CONSERVATIVE:`. None of them changes what the emitted code computes; they
 * only cost a heap entry, a stack frame, or an unelided update.
 *
 * One signature deviates, because the information simply is not in the STG
 * that stg.ts models: `genBody` takes the result's `PrimRep[]` explicitly
 * where Expr.hs derives it from a `Type` via `resultSize`. `genEntry` and
 * `genEntryLne` supply it from the entry's own binder (`idPrimReps`).
 */
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { Sub, Var, global, mconcatJStgStat, memptyJStgStat } from "../js/jstg-syntax.js";
import {
  app,
  appS,
  assignAll,
  assignAllReverseOrder,
  declAssignAll,
  decl,
  declAssign_,
  assign_,
  if_,
  jInt,
  jString,
  jhFromList,
  null_,
  returnS,
  returnStack,
  undefined_,
  zero_,
} from "../js/make.js";
import { identsE } from "../js/transform.js";
import type { Binder, DataCon, StgAlt, StgArg, StgBinding, StgExpr, StgRhs } from "../stg.js";
import { UpdateFlag } from "../stg.js";
import { genArg, genIdArg, genIdArgI, genIdStackArgI } from "./arg.js";
import { allocDynamic, allocCon, genCon } from "./datacon.js";
import { allocData, dataFieldName, jsClosureCount } from "./closure.js";
import type { ExprCtx } from "./expr-ctx.js";
import {
  ctxClearLneFrame,
  ctxIsEvaluated,
  ctxIsLneBinding,
  ctxIsLneLiveVar,
  ctxLneBindingStackSize,
  ctxLneFrameSize,
  ctxLneFrameVars,
  ctxLneShrinkStack,
  ctxSetTarget,
  ctxSetTop,
  ctxTarget,
  ctxUpdateLneFrame,
} from "./expr-ctx.js";
import { genForeignCall, genPrimCall } from "./ffi.js";
import { closureField1, closureField2, closureInfo, closureInfo_, closureField1_, closureField2_, closureMeta_, isObject } from "./heap.js";
import {
  declVarsForId,
  freshIdent,
  identForEntryId,
  identForId,
  identsForId,
  varForDataConWorker,
  varForEntryId,
  varForId,
  varsForId,
} from "./ids.js";
import { genLit } from "./literal.js";
import type { GenState, StackSlot } from "./monad.js";
import {
  assertRtsStat,
  emitClosureInfo,
  emitToplevel,
  getSettings,
  slotUnknown,
} from "./monad.js";
import { genPrim } from "./prim.js";
import { R1, R2, register, regsFromR1, sp } from "./regs.js";
import type { StackState } from "./stack.js";
import {
  adjSp,
  getSlots,
  isolateSlots,
  popSkipI,
  pushOptimized,
  push,
  resetSlots,
  setSlots,
  updateThunk,
} from "./stack.js";
import { hdBlackHoleLNE, hdBlackHoleTrap, hdC, hdEntryStr } from "./symbols.js";
import type { CIStatic, CIType, ClosureInfo, StgToJSConfig } from "./types.js";
import { JSRep } from "./types.js";
import type { LiveVars, PrimRep, TypedExpr, UnfloatedMap } from "./utils.js";
import {
  assignCoerce1,
  assignToExprCtx,
  assocExprs,
  exprRefs,
  fixedLayout,
  idSlotCount,
  isBoolDataCon,
  isUnboxable,
  isUnboxableCon,
  liveStatic,
  liveVars,
  isUpdatableRhs,
  primRepToJSRep,
  slotCount,
  primRepSize,
  stackSlotType,
  stgExprLive,
  stgLneLive_,
  stgLneLiveExpr,
  stgRhsLive,
  typedExpr,
} from "./utils.js";
import { initJSM, runJSM, withTag } from "../js/jstg-monad.js";
import { specTagExpr, selectApply, ApplyConv } from "./apply.js";
import type { ApplySpec } from "./apply.js";

// ---------------------------------------------------------------------------
// GHC.StgToJS.Types.ExprResult
// ---------------------------------------------------------------------------

/** `data ExprResult = ExprCont | ExprInline`. */
export type ExprResult = "ExprCont" | "ExprInline";

// ---------------------------------------------------------------------------
// Core stand-ins
//
// Everything in this block replaces a query on a Core `Type`/`IdDetails` that
// stg.ts's Binder does not carry. See the module header.
// ---------------------------------------------------------------------------

/** `typeSize . idType` - how many JS slots the binder occupies. */
const typeSizeId = (i: Binder): number => idSlotCount(i);

/** `idJSRep`. A binder records only its slot count, so the rep is recovered
 * from that: one slot is a pointer (by far the common case), two slots is a
 * LongV pair. Only ever consulted for info-table register/layout metadata and
 * for `-fjs-runtime-assert` checks. */
function idJSRep(i: Binder): JSRep[] {
  const n = idSlotCount(i);
  if (n === 0) return [JSRep.VoidV];
  if (n === 2) return [JSRep.LongV];
  return [JSRep.PtrV];
}

/** `unaryTypeJSRep . idType`. */
const unaryTypeJSRepId = (i: Binder): JSRep => idJSRep(i)[0];

/** The PrimReps a binder's value occupies. A two-slot binder is treated as
 * Int64Rep rather than AddrRep: both are two slots, and Int64Rep is the one
 * `assignCoerce` never rewrites, so a wrong guess cannot introduce a bogus
 * StablePtr/Addr coercion. */
function idPrimReps(i: Binder): PrimRep[] {
  const n = idSlotCount(i);
  if (n === 0) return [];
  if (n === 2) return [{ tag: "Int64Rep" }];
  return [{ tag: "BoxedRep", levity: "Lifted" }];
}

/** `GHC.StgToJS.Utils.assocIdExprs`. */
const assocIdExprs = (i: Binder, es: JStgExpr[]): TypedExpr[] => assocExprs(idPrimReps(i), es);

/** `GHC.StgToJS.Apply.getIdFields` - an expression for every field of the Id. */
export const getIdFields = (gs: GenState, i: Binder): TypedExpr[] => assocIdExprs(i, varsForId(gs, i));

/** `GHC.StgToJS.Apply.storeIdFields` - store the Id's fields into `dst`. */
export function storeIdFields(gs: GenState, i: Binder, dst: TypedExpr[]): JStgStat {
  return assignCoerce1(dst, getIdFields(gs, i));
}

/** `GHC.StgToJS.Utils.isInlineExpr`. */
export function isInlineExpr(e: StgExpr): boolean {
  switch (e.tag) {
    case "StgApp":
      return isInlineApp(e.fn, e.args);
    case "StgLit":
      return true;
    case "StgConApp":
      return true;
    case "StgOpApp":
      if (e.op.tag === "StgPrimCallOp") return true;
      if (e.op.tag === "StgFCallOp") return e.op.target.safety !== "interruptible";
      return false;
    case "StgCase":
      return isInlineExpr(e.scrutinee) && e.alts.every((a) => isInlineExpr(a.body));
    case "StgLet":
    case "StgLetNoEscape":
      return isInlineExpr(e.body);
  }
}

/** `GHC.StgToJS.Utils.isInlineApp`. */
function isInlineApp(i: Binder, args: StgArg[]): boolean {
  if (i.join) return false;
  if (args.length === 0) return isUnboxedTupleId(i) || isStrictTypeId(i) || ctxIsEvaluated(i);
  return false;
}

/** The stack state Stack.hs threads through `G`, projected onto the two
 * GenGroupState fields that hold it. */
export function stackState(gs: GenState): StackState {
  const g = gs.gsGroup;
  return {
    get stackDepth() {
      return g.ggsStackDepth;
    },
    set stackDepth(v: number) {
      g.ggsStackDepth = v;
    },
    get slots() {
      return g.ggsStack;
    },
    set slots(v: StackSlot[]) {
      g.ggsStack = v;
    },
  };
}

/** `GHC.StgToJS.Stack.pushLneFrame`. Left unported with the rest of Stack.hs
 * because it needs ExprCtx; both of its callers are here. */
function pushLneFrame(gs: GenState, size: number, ctx: ExprCtx): JStgStat {
  const ctx_ = ctxLneShrinkStack(ctx, size);
  return pushOptimized_(gs, ctxLneFrameVars(ctx_));
}

/** `GHC.StgToJS.Stack.pushOptimized'`. */
function pushOptimized_(gs: GenState, xs: ReadonlyArray<readonly [Binder, number]>): JStgStat {
  const st = stackState(gs);
  const slots = getSlots(st);
  const zipped = xs.map(([i1, n1], k): [JStgExpr, boolean] => {
    const vs = varsForId(gs, i1);
    const idN1 = vs[n1 - 1];
    const slot = slots[k] ?? slotUnknown;
    return [idN1, slot.tag === "SlotId" && slot.id.unique === i1.unique && slot.size === n1];
  });
  return pushOptimized(st, getSettings(gs), zipped);
}

/** Profiling is not modelled (Profiling.hs is unported and `csProf` is False),
 * so every `ifProfiling`/`ifProfilingM` site collapses to mempty. */
const ifProfiling = (gs: GenState, stat: () => JStgStat): JStgStat =>
  getSettings(gs).prof ? stat() : memptyJStgStat;

// ---------------------------------------------------------------------------
// Expr.hs proper
// ---------------------------------------------------------------------------

/** Evaluate an expression in the given expression context (continuation) */
export function genExpr(gs: GenState, ctx: ExprCtx, stg: StgExpr): [JStgStat, ExprResult] {
  switch (stg.tag) {
    case "StgApp":
      return genApp(gs, ctx, stg.fn, stg.args);
    case "StgLit": {
      const ls = genLit(gs, stg.lit);
      return [assignToExprCtx(ctx, ls), "ExprInline"];
    }
    case "StgConApp": {
      const as = stg.args.flatMap((a) => genArg(gs, a));
      return [genCon(gs, ctx, stg.con, as), "ExprInline"];
    }
    case "StgOpApp":
      switch (stg.op.tag) {
        case "StgFCallOp":
          return genForeignCall(gs, ctx, stg.op.target, ctxTarget(ctx).flatMap((t) => t.expr), stg.args);
        case "StgPrimOp":
          return genPrimOp(gs, ctx, stg.op.op, stg.args);
        case "StgPrimCallOp":
          return genPrimCall(gs, ctx, stg.op.name, stg.args);
      }
      break;
    case "StgCase":
      return genCase(gs, ctx, stg.binder, stg.scrutinee, stg.altType, stg.alts, liveVars(stgExprLive(false, stg)));
    case "StgLet": {
      const [b_, ctx_] = genBind(gs, ctx, stg.binding);
      const [s, r] = genExpr(gs, ctx_, stg.body);
      return [mconcatJStgStat([b_, s]), r];
    }
    case "StgLetNoEscape": {
      const [b_, ctx_] = genBindLne(gs, ctx, stg.binding);
      const [s, r] = genExpr(gs, ctx_, stg.body);
      return [mconcatJStgStat([b_, s]), r];
    }
  }
  throw new Error("genExpr: unreachable");
}

/** GHC's `isStrictId`: join points are never treated as evaluated; otherwise
 * a function closure, a post-case binder, or an explicit strict bit. */
function isStrictId(i: Binder): boolean {
  if (i.join) return false;
  return i.strict === true || i.evaluated === true || (i.funRepArity ?? 0) > 0;
}

/** Unlifted / void / prim-suffixed names stand in for `isStrictType`. */
function isStrictTypeId(i: Binder): boolean {
  return i.arity === 0 || i.name.endsWith("#");
}

function isUnboxedTupleId(i: Binder): boolean {
  return i.name.startsWith("(#");
}

function isLocalId(i: Binder): boolean {
  return i.exported !== true || i.internal === true;
}

/** GHC.StgToJS.Apply.jumpToII - avoid one indirection for global ids. */
function jumpToII(gs: GenState, i: Binder, vars: JStgExpr[], loadAppInR1: JStgStat): JStgStat {
  const loadArgs = assignAllReverseOrder([...regsFromR1.slice(1).map(register)], vars);
  if (isLocalId(i)) {
    return mconcatJStgStat([loadArgs, loadAppInR1, returnS(closureInfo(varForId(gs, i)))]);
  }
  return mconcatJStgStat([loadArgs, loadAppInR1, returnS(varForEntryId(gs, i))]);
}

/** GHC.StgToJS.Apply.genApp - generate an application of some args to an Id.
 *
 * Case order follows Apply.hs. Binder facts (`funRepArity`, `strict`,
 * `evaluated`, `mightBeFun`) stand in for the Core `Id` queries GHC makes. */
export function genApp(gs: GenState, ctx: ExprCtx, i: Binder, args: StgArg[]): [JStgStat, ExprResult] {
  const st = stackState(gs);
  const ghc = getSettings(gs).optimization !== "none";

  // let-no-escape
  const n = ctxLneBindingStackSize(ctx, i);
  if (n !== undefined) {
    const as_ = args.flatMap((a) => genArg(gs, a));
    const ei = varForEntryId(gs, i);
    const ra = mconcatJStgStat(as_.map((a, k) => assign_(register(regsFromR1[k]), a)).reverse());
    const p = pushLneFrame(gs, n, ctx);
    const a = adjSp(st, 1);
    return [mconcatJStgStat([ra, p, a, returnS(ei)]), "ExprCont"];
  }

  // proxy#
  if (args.length === 0 && i.name === "proxy#") {
    const tops = ctxTarget(ctx).flatMap((t) => t.expr);
    if (tops.length === 1) return [assign_(tops[0], null_), "ExprInline"];
  }

  const targets = ctxTarget(ctx);

  // unboxed tuple or strict type: return fields individually
  if (args.length === 0 && targets.length > 0 && (isUnboxedTupleId(i) || isStrictTypeId(i))) {
    return [storeIdFields(gs, i, targets), "ExprInline"];
  }

  // unboxable heap object already evaluated: Int/Double payload, or the box
  const vt = idJSRep(i);
  if (args.length === 0 && vt.length === 1 && isUnboxable(vt[0]!) && ctxIsEvaluated(i)) {
    const fields = targets.flatMap((t) => t.expr);
    const is = varsForId(gs, i);
    if (fields.length === 1 && is.length === 1) {
      return [assign_(fields[0]!, if_(isObject(is[0]!), closureField1(is[0]!), is[0]!)), "ExprInline"];
    }
  }

  // known evaluated (or strict type): return fields without entering
  if (args.length === 0 && targets.length > 0 && (ctxIsEvaluated(i) || isStrictTypeId(i))) {
    return [storeIdFields(gs, i, targets), "ExprInline"];
  }

  // no args and Id can't be a function: just enter it
  if (args.length === 0 && i.mightBeFun === false) {
    const enterId = genIdArg(gs, i);
    if (enterId.length === 1) return [returnS(app(hdEntryStr, [enterId[0]!])), "ExprCont"];
  }

  const arity = i.funRepArity;
  const loadFun = assignAll([...regsFromR1.map(register)], varsForId(gs, i));

  // fully saturated global function
  if (ghc && args.length !== 0 && arity === args.length && !isLocalId(i) && isStrictId(i)) {
    const vars = args.flatMap((a) => genArg(gs, a));
    return [jumpToII(gs, i, vars, loadFun), "ExprCont"];
  }

  // oversaturated function: push extra args as a continuation, then jump
  if (ghc && arity !== undefined && arity < args.length && isStrictId(i) && arity > 0) {
    const reg = args.slice(0, arity);
    const over = args.slice(arity);
    const vars = reg.flatMap((a) => genArg(gs, a));
    return [mconcatJStgStat([pushCont(gs, over), jumpToII(gs, i, vars, loadFun)]), "ExprCont"];
  }

  return [jumpToFast(gs, args, loadFun), "ExprCont"];
}

/** GHC.StgToJS.Apply.jumpToFast - try to use a specialized pre-generated
 * application function; if there is none, use h$ap_gen_fast instead. */
function jumpToFast(gs: GenState, args: StgArg[], loadAppInR1: JStgStat): JStgStat {
  // get JS expressions for every argument. Arguments may have more than one
  // expression (e.g. Word64#)
  const vars = args.flatMap((a) => genArg(gs, a));
  const spec = mkApplySpec(ApplyConv.RegsConv, args, vars);
  const apFun = selectApply(spec);
  return mconcatJStgStat([
    assignAllReverseOrder([...regsFromR1.slice(1).map(register)], vars),
    loadAppInR1,
    apFun.generic
      ? // generic apply: pass a tag indicating number of args/slots
        returnS({ tag: "ApplExpr", fn: apFun.fun, args: [specTagExpr(spec)] })
      : // specialized apply: no tag
        returnS({ tag: "ApplExpr", fn: apFun.fun, args: [] }),
  ]);
}

/** GHC.StgToJS.Apply.pushCont. */
export function pushCont(gs: GenState, args: StgArg[]): JStgStat {
  const vars = args.flatMap((a) => genArg(gs, a));
  const spec = mkApplySpec(ApplyConv.StackConv, args, vars);
  const ap = selectApply(spec);
  const items = ap.generic ? [ap.fun, specTagExpr(spec), ...vars] : [ap.fun, ...vars];
  return push(stackState(gs), getSettings(gs), items.reverse());
}

/** GHC.StgToJS.Apply.mkApplySpec. */
function mkApplySpec(conv: ApplyConv, args: StgArg[], vars: JStgExpr[]): ApplySpec {
  return { specConv: conv, specArgs: args.length, specVars: vars.length };
}

/** regular let binding: allocate heap object */
export function genBind(gs: GenState, ctx: ExprCtx, bndr: StgBinding): [JStgStat, ExprCtx] {
  const ctx_ = ctxClearLneFrame(ctx);

  const assign = (b: Binder, r: StgRhs): JStgStat | undefined => {
    if (r.tag === "StgRhsClosure" && r.args.length === 0) {
      const sel = matchSelectorThunk(gs, b, r.body);
      if (sel !== undefined) return sel;
      if (isInlineExpr(r.body)) {
        const d = declVarsForId(gs, b);
        const tgt = varsForId(gs, b);
        const ictx = ctxSetTarget(assocIdExprs(b, tgt), ctx);
        const [j] = genExpr(gs, ictx, r.body);
        return mconcatJStgStat([d, j]);
      }
    }
    if (r.tag === "StgRhsCon") return undefined;
    genEntry(gs, ctx_, b, r);
    return undefined;
  };

  if (bndr.tag === "StgNonRec") {
    const ja = assign(bndr.binder, bndr.rhs);
    const j = ja !== undefined ? ja : allocCls(gs, undefined, [[bndr.binder, bndr.rhs]]);
    return [j, ctx];
  }
  const jas = bndr.pairs.map(([b, r]) => assign(b, r));
  const defined = jas.filter((x): x is JStgStat => x !== undefined);
  const m = jas.length === 0 ? undefined : mconcatJStgStat(defined);
  const rest = bndr.pairs.filter((_, k) => jas[k] === undefined);
  return [allocCls(gs, m, rest), ctx];
}

/** The `assign` clause of genBind that recognises a record selector thunk and
 * emits a call to the RTS's pre-generated `h$c_sel_N` instead of a closure.
 *
 * Returns undefined when the RHS is not of that shape. GHC additionally strips
 * non-code ticks; stg.ts has no StgTick. */
function matchSelectorThunk(gs: GenState, b: Binder, expr: StgExpr): JStgStat | undefined {
  if (expr.tag !== "StgCase") return undefined;
  if (expr.scrutinee.tag !== "StgApp" || expr.scrutinee.args.length !== 0) return undefined;
  if (expr.altType.tag !== "AlgAlt" || expr.alts.length !== 1) return undefined;
  const alt = expr.alts[0];
  if (alt.con.tag !== "DataAlt") return undefined;
  if (alt.body.tag !== "StgApp" || alt.body.args.length !== 0) return undefined;

  const scrutinee = expr.scrutinee.fn;
  const selectee = alt.body.fn;
  const params = alt.binders;
  // scanl' (+) 1 (map typeSize params): the offset of each field in the payload
  const offsets: number[] = [];
  let acc = 1;
  for (const p of params) {
    offsets.push(acc);
    acc += typeSizeId(p);
  }
  const totalSize = params.reduce((s, p) => s + typeSizeId(p), 0);
  const idx = params.findIndex((p) => p.unique === selectee.unique);
  if (idx < 0) return undefined;
  const theOffset = offsets[idx];
  if (theOffset > 16) return undefined; // fixme make this some configurable constant

  const theFv = scrutinee;
  const selTag = theOffset === 2 ? (totalSize === 2 ? "2a" : "2b") : String(theOffset);
  const tgts = identsForId(gs, b);
  const theFvjs = varsForId(gs, theFv);
  if (tgts.length !== 1 || theFvjs.length !== 1) throw new Error("genBind.assign: invalid size");
  return declAssign_(tgts[0], { tag: "ApplExpr", fn: global(`h$c_sel_${selTag}`), args: [theFvjs[0]] });
}

export function genBindLne(gs: GenState, ctx: ExprCtx, bndr: StgBinding): [JStgStat, ExprCtx] {
  const oldFrameSize = ctxLneFrameSize(ctx);
  const isOldLv = (i: Binder): boolean => ctxIsLneBinding(ctx, i) || ctxIsLneLiveVar(ctx, i);
  const live = liveVars(new Map(stgLneLive_(bndr).map((i) => [i.unique, i])));
  const newLvs = [...live.values()].filter((i) => !isOldLv(i));
  const binds: Array<[Binder, StgRhs]> =
    bndr.tag === "StgNonRec" ? [[bndr.binder, bndr.rhs]] : bndr.pairs.map(([b, r]): [Binder, StgRhs] => [b, r]);
  const bound = binds.map(([b]) => b);
  const updBinds = binds.filter(([, r]) => isUpdatableRhs(r));

  // compute live variables and the offsets where they will be stored in the stack
  const vis = optimizeFree(gs, oldFrameSize, [...newLvs, ...updBinds.map(([b]) => b)]).map(
    ([x, y]): [Binder, number] => [x, y],
  );
  // initialize updatable bindings to null_
  const declUpds = mconcatJStgStat(updBinds.map(([b]) => declAssign_(identForId(gs, b), null_)));
  // update expression context to include the updated LNE frame
  const ctx_ = ctxUpdateLneFrame(vis, bound, ctx);
  for (const [b, r] of binds) genEntryLne(gs, ctx_, b, r);
  return [declUpds, ctx_];
}

/** Generate let-no-escape entry
 *
 * Let-no-escape entries live on the stack. There is no heap object associated
 * with them.
 *
 * A let-no-escape entry is called like a normal stack frame, although as an
 * optimization, `Stack`[`Sp`] is not set when making the call. This is done
 * later if the thread needs to be suspended.
 *
 * Updatable let-no-escape binders have one 'private' slot in the stack frame.
 * This slot is initially set to null, changed to h$blackhole when the thunk is
 * being evaluated.
 */
export function genEntryLne(gs: GenState, ctx: ExprCtx, i: Binder, rhs: StgRhs): void {
  const st = stackState(gs);
  if (rhs.tag === "StgRhsCon") {
    resetSlots(st, () => {
      const payloadSize = ctxLneFrameSize(ctx);
      const ei = identForEntryId(gs, i);
      const ii = freshIdent(gs);
      const p = popLneFrame(gs, true, payloadSize, ctx);
      const args_ = rhs.args.flatMap((a) => genArg(gs, a));
      const ac = allocCon(gs, ii, rhs.con, args_);
      emitToplevel(gs, {
        tag: "FuncStat",
        ident: ei,
        args: [],
        body: mconcatJStgStat([decl(ii), p, ac, assign_(register(R1), Var(ii)), returnStack]),
      });
    });
    return;
  }
  resetSlots(st, () => {
    const payloadSize = ctxLneFrameSize(ctx);
    const vars = ctxLneFrameVars(ctx);
    const found = vars.findIndex(([v]) => v.unique === i.unique);
    if (found < 0) throw new Error("genEntryLne: updatable binder not found in let-no-escape frame");
    const myOffset = payloadSize - found;

    const blkHl = mkBhLne(gs, rhs.update, myOffset, payloadSize);

    const locals = popLneFrame(gs, true, payloadSize, ctx);
    const body = genBody(gs, ctx, R1, rhs.args, rhs.body, idPrimReps(i));
    const ei = identForEntryId(gs, i);
    const sr = genStaticRefsRhs(gs, rhs);
    const f = mconcatJStgStat([blkHl, locals, body]);
    emitClosureInfo(gs, {
      var: ei,
      regs: { tag: "CIRegs", skip: 0, types: rhs.args.flatMap(idJSRep) },
      name: `${ei}, ${i.name}`,
      layout: fixedLayout([...ctxLneFrameVars(ctx)].reverse().map(([v]) => stackSlotType(unaryTypeJSRepId(v)))),
      type: { tag: "CIStackFrame" },
      static: sr,
    });
    emitToplevel(gs, { tag: "FuncStat", ident: ei, args: [], body: f });
  });
}

/** The `mk_bh` local of genEntryLne: an updatable LNE binder gets a private
 * slot in the frame that h$bh_lne flips to a blackhole. */
function mkBhLne(gs: GenState, update: UpdateFlag, myOffset: number, payloadSize: number): JStgStat {
  if (update !== UpdateFlag.Updatable) return memptyJStgStat;
  const x = freshIdent(gs);
  return mconcatJStgStat([
    declAssign_(x, {
      tag: "ApplExpr",
      fn: hdBlackHoleLNE,
      args: [Sub(sp, jInt(myOffset)), jInt(payloadSize + 1)],
    }),
    { tag: "IfStat", cond: Var(x), then: returnS(Var(x)), else: memptyJStgStat },
  ]);
}

/** Generate the entry function for a local closure */
export function genEntry(gs: GenState, ctx: ExprCtx, i: Binder, rhs: StgRhs): void {
  if (rhs.tag === "StgRhsCon") return;
  const st = stackState(gs);
  resetSlots(st, () => {
    const live = stgLneLiveExpr(rhs);
    const ll = loadLiveFun(gs, live);
    const llv = verifyRuntimeReps(gs, live);
    const upd = genUpdFrame(gs, rhs.update, i);
    const entryCtx = ctxSetTarget([], ctxClearLneFrame(ctx));
    const body = genBody(gs, entryCtx, R2, rhs.args, rhs.body, idPrimReps(i));
    const et = genEntryType(gs, rhs.args);
    const sr = genStaticRefsRhs(gs, rhs);

    const ei = identForEntryId(gs, i);
    emitClosureInfo(gs, {
      var: ei,
      regs: { tag: "CIRegs", skip: 0, types: [JSRep.PtrV, ...rhs.args.flatMap(idJSRep)] },
      name: `${ei}, ${i.name}`,
      layout: fixedLayout(live.map(unaryTypeJSRepId)),
      type: et,
      static: sr,
    });
    emitToplevel(gs, {
      tag: "FuncStat",
      ident: ei,
      args: [],
      // `setcc` (enterCostCentreThunk / enterCostCentreFun) - see ifProfiling
      body: mconcatJStgStat([ll, llv, upd, ifProfiling(gs, () => memptyJStgStat), body]),
    });
  });
}

/** Generate the entry function types for identifiers. Note that this only
 * returns either 'CIThunk' or 'CIFun'. */
export function genEntryType(gs: GenState, args: Binder[]): CIType {
  if (args.length === 0) return { tag: "CIThunk" };
  const args_ = args.map((a) => genIdArg(gs, a));
  return { tag: "CIFun", arity: args.length, regs: args_.reduce((n, x) => n + x.length, 0) };
}

/** Generate the body of an object.
 *
 * `resultReps` stands in for Expr.hs's `Type` argument (see `resultSize`). */
export function genBody(
  gs: GenState,
  ctx: ExprCtx,
  startReg: number,
  args: Binder[],
  e: StgExpr,
  resultReps: PrimRep[],
): JStgStat {
  // load arguments into local variables
  const args_ = args.flatMap((a) => genIdArgI(gs, a));
  const la = declAssignAll(args_, regsFromR1.slice(startReg).map(register));

  // assert that arguments have valid runtime reps
  const lav = verifyRuntimeReps(gs, args);

  // compute PrimReps and their number of slots required to return the result
  const resVars = resultSize(resultReps);

  // compute typed expressions for each slot and assign registers
  const goVar = (regs: JStgExpr[], rs: Array<[PrimRep, number]>): TypedExpr[] => {
    if (rs.length === 0) return [];
    const [[rep, size], ...rest] = rs;
    return [typedExpr(rep, regs.slice(0, size)), ...goVar(regs.slice(size), rest)];
  };

  const tgt = goVar(regsFromR1.map(register), resVars);
  const ctx_ = ctxSetTarget(tgt, ctx);

  const [je] = genExpr(gs, ctx_, e);
  return mconcatJStgStat([la, lav, je, returnStack]);
}

/** Find the result size after applying the function to the arguments.
 *
 * Expr.hs works this out from a `Type` (see its long comment on why that is
 * hard even with types available); with no types at all, this port is handed
 * the reps and only computes the slot counts. */
export function resultSize(reps: PrimRep[]): Array<[PrimRep, number]> {
  return reps.map((r): [PrimRep, number] => [r, slotCount(primRepSize(r))]);
}

/** Ensure that the set of identifiers has valid 'RuntimeRep's. This function
 * returns a no-op when 'csRuntimeAssert' in 'StgToJSConfig' is False. */
export function verifyRuntimeReps(gs: GenState, xs: Binder[]): JStgStat {
  if (!getSettings(gs).runtimeAssert) return memptyJStgStat;
  const v = (f: string, as: JStgExpr[]): JStgStat => appS(f, as);
  const ver = (j: JStgExpr, r: JSRep): JStgStat => {
    switch (r) {
      case JSRep.PtrV:
        return v("h$verify_rep_heapobj", [j]);
      case JSRep.IntV:
        return v("h$verify_rep_int", [j]);
      case JSRep.DoubleV:
        return v("h$verify_rep_double", [j]);
      case JSRep.ArrV:
        return v("h$verify_rep_arr", [j]);
      default:
        return memptyJStgStat;
    }
  };
  const go = (js: JStgExpr[], vs: JSRep[]): JStgStat => {
    if (vs.length === 0 && js.length === 0) return memptyJStgStat;
    if (vs.length === 0 || js.length === 0) throw new Error("verifyRuntimeReps: inconsistent sizes");
    const [r, ...rs] = vs;
    if (r === JSRep.VoidV) return go(js, rs);
    if (r === JSRep.LongV) return mconcatJStgStat([v("h$verify_rep_long", [js[0], js[1]]), go(js.slice(2), rs)]);
    if (r === JSRep.AddrV) return mconcatJStgStat([v("h$verify_rep_addr", [js[0], js[1]]), go(js.slice(2), rs)]);
    return mconcatJStgStat([ver(js[0], r), go(js.slice(1), rs)]);
  };
  return mconcatJStgStat(xs.map((i) => go(varsForId(gs, i), idJSRep(i))));
}

/** Given a set of 'Id's, bind each 'Id' to the appropriate data fields in N
 * registers. This assumes these data fields have already been populated in the
 * registers. For the empty, singleton, and binary case use register 1, for any
 * more use as many registers as necessary. */
export function loadLiveFun(gs: GenState, l: Binder[]): JStgStat {
  const l_ = l.flatMap((i) => identsForId(gs, i));
  const r1 = register(R1);
  if (l_.length === 0) return memptyJStgStat;
  if (l_.length === 1) return declAssign_(l_[0], closureField1(r1));
  if (l_.length === 2) {
    return mconcatJStgStat([declAssign_(l_[0], closureField1(r1)), declAssign_(l_[1], closureField2(r1))]);
  }
  const [v, ...vs] = l_;
  const d = freshIdent(gs);
  const loadLiveVar = (dE: JStgExpr, n: number, x: Ident): JStgStat =>
    declAssign_(x, { tag: "SelExpr", obj: dE, field: name(dataFieldName(n)) });
  const l__ = mconcatJStgStat(vs.map((x, k) => loadLiveVar(Var(d), k + 1, x)));
  return mconcatJStgStat([declAssign_(v, closureField1(r1)), declAssign_(d, closureField2(r1)), l__]);
}

/** Pop a let-no-escape frame off the stack */
export function popLneFrame(gs: GenState, inEntry: boolean, size: number, ctx: ExprCtx): JStgStat {
  const ctx_ = ctxLneShrinkStack(ctx, size);
  const is = ctxLneFrameVars(ctx_).map(([i, n]): [Ident, StackSlot] => {
    const ids = identsForId(gs, i);
    return [ids[n - 1], { tag: "SlotId", id: i, size: n }];
  });
  const skip = inEntry ? 1 : 0; // pop the frame header
  return popSkipI(stackState(gs), skip, is);
}

/** Generate an update frame for an 'Id'.
 *
 * CONSERVATIVE: the `isOneShotBndr i` clause (which downgrades an updatable
 * thunk to a mere blackhole) needs Core's one-shot annotation, so an Updatable
 * binder always gets the real update frame. */
export function genUpdFrame(gs: GenState, u: UpdateFlag, _i: Binder): JStgStat {
  const maybeBh = (): JStgStat => assertRtsStat(gs, () => bhSingleEntry(getSettings(gs)));
  if (u === UpdateFlag.ReEntrant) return memptyJStgStat;
  if (u === UpdateFlag.Updatable) return updateThunk(stackState(gs), getSettings(gs));
  return maybeBh();
}

/** Blackhole single entry
 *
 * Overwrite a single entry object with a special thunk that behaves like a
 * black hole (throws a JS exception when entered) but pretends to be a thunk.
 * Useful for making sure that the object is not accidentally entered multiple
 * times.
 */
export function bhSingleEntry(_settings: StgToJSConfig): JStgStat {
  const r1 = register(R1);
  return mconcatJStgStat([
    assign_(closureInfo(r1), hdBlackHoleTrap),
    assign_(closureField1(r1), undefined_),
    assign_(closureField2(r1), undefined_),
  ]);
}

export function genStaticRefsRhs(gs: GenState, lv: StgRhs): CIStatic {
  return genStaticRefs(gs, stgRhsLive(lv));
}

/** fixme, update to new way to compute static refs dynamically */
export function genStaticRefs(gs: GenState, lv: LiveVars): CIStatic {
  const sv = liveStatic(lv);
  if (sv.size === 0) return { staticRefs: [] };
  const unfloated: UnfloatedMap = gs.gsUnfloated;
  // GHC also drops definitely-unlifted types; ghcts has no type to test, so
  // the reference is kept - a superset of static refs is always safe.
  const xs = [...sv.values()].filter((x) => !unfloated.has(x.unique));
  const refs: string[] = [];
  for (const x of xs) {
    const ids = identsForId(gs, x);
    if (ids.length > 0) refs.push(ids[0]);
  }
  return { staticRefs: refs };
}

const slotKey = (s: StackSlot): string => (s.tag === "SlotUnknown" ? "?" : `${s.id.unique}|${s.size}`);

/** Reorder the things we need to push to reuse existing stack values as much
 * as possible. The Bool is True if the value is already on the stack at that
 * location. */
export function optimizeFree(gs: GenState, offset: number, ids: Binder[]): Array<[Binder, number, boolean]> {
  const ids_: Array<[Binder, number]> = ids.flatMap((i) =>
    Array.from({ length: typeSizeId(i) }, (_, k): [Binder, number] => [i, k + 1]),
  );
  const l = ids_.length;
  const all = getSlots(stackState(gs));
  // `drop offset . take l . (++ repeat SlotUnknown) <$> getSlots`
  const window: StackSlot[] = Array.from({ length: l }, (_, k) => all[k] ?? slotUnknown).slice(offset);

  // M.fromList keeps the last binding for duplicate keys
  const slm = new Map<string, number>();
  window.forEach((s, k) => slm.set(slotKey(s), k));

  const fixed: Array<[Binder, number, number, boolean]> = [];
  const remaining: Array<[Binder, number]> = [];
  for (const [i, n] of ids_) {
    const j = slm.get(`${i.unique}|${n}`);
    if (j === undefined) remaining.push([i, n]);
    else fixed.push([i, n, j, true]);
  }
  const takenSlots = new Set(fixed.map(([, , x]) => x));
  const freeSlots = Array.from({ length: l }, (_, k) => k).filter((x) => !takenSlots.has(x));
  const remaining_: Array<[Binder, number, number, boolean]> = remaining.map(([i, n], k) => [i, n, freeSlots[k], false]);
  const allSlots = [...fixed, ...remaining_].sort((a, b) => a[2] - b[2]);
  return allSlots.map(([i, n, , b]): [Binder, number, boolean] => [i, n, b]);
}

type ClsEntry = [Ident, JStgExpr, JStgExpr[]];

/** Allocate local closures */
export function allocCls(gs: GenState, dynMiddle: JStgStat | undefined, xs: Array<[Binder, StgRhs]>): JStgStat {
  const stat: JStgStat[] = [];
  const dyn: ClsEntry[] = [];
  for (const [i, rhs] of xs) {
    // GHC's `toCl` has three cases, and the nullary one comes first: a
    // no-argument constructor is `allocCon`'d, which for `Bool` and the other
    // unboxable types yields the static value rather than a fresh - and so
    // always truthy - closure.
    if (rhs.tag === "StgRhsCon" && rhs.args.length === 0) {
      const ii = identForId(gs, i);
      stat.push(mconcatJStgStat([decl(ii), allocCon(gs, ii, rhs.con, [])]));
      continue;
    }
    if (rhs.tag === "StgRhsCon" && rhs.args.length === 1 && isUnboxableCon(rhs.con)) {
      // statics
      const ii = identForId(gs, i);
      const ac = allocCon(gs, ii, rhs.con, genArg(gs, rhs.args[0]));
      stat.push(mconcatJStgStat([decl(ii), ac]));
      continue;
    }
    // dynamics
    if (rhs.tag === "StgRhsCon") {
      dyn.push([identForId(gs, i), varForDataConWorker(gs, rhs.con), rhs.args.flatMap((a) => genArg(gs, a))]);
      continue;
    }
    const live = stgLneLiveExpr(rhs);
    dyn.push([identForId(gs, i), varForEntryId(gs, i), live.flatMap((v) => varsForId(gs, v))]);
  }
  const ac = allocDynAll(gs, false, dynMiddle, dyn);
  return mconcatJStgStat([...stat, ac]);
}

/** Consume Stg case statement and generate a case statement. See also
 * 'genAlts'. */
export function genCase(
  gs: GenState,
  ctx: ExprCtx,
  bnd: Binder,
  e: StgExpr,
  at: import("../stg.js").AltType,
  alts: StgAlt[],
  l: LiveVars,
): [JStgStat, ExprResult] {
  // For:      unpackCStringAppend# "some string"# str
  // Generate: h$appendToHsStringA(str, "some string")
  //
  // The latter has a faster decoding loop. Since #23270 the literal is not an
  // STG atom, so the shape matched is
  //    case "some string"# of b { DEFAULT -> unpackCStringAppend# b str }
  if (
    e.tag === "StgLit" &&
    e.lit.tag === "LitString" &&
    alts.length === 1 &&
    alts[0].con.tag === "DEFAULT" &&
    alts[0].body.tag === "StgApp" &&
    alts[0].body.fn.name === "unpackCStringAppend#" &&
    alts[0].body.args.length === 2 &&
    alts[0].body.args[0].tag === "StgVarArg" &&
    alts[0].body.args[0].id.unique === bnd.unique
  ) {
    const tops = ctxTarget(ctx).flatMap((t) => t.expr);
    if (tops.length === 1) {
      const a = genArg(gs, alts[0].body.args[1]);
      return [assign_(tops[0], app("h$appendToHsStringA", [jString(e.lit.value), ...a])), "ExprInline"];
    }
  }

  if (isInlineExpr(e)) {
    const bndi = identsForId(gs, bnd);
    const ctx_ = ctxSetTop(bnd, ctxSetTarget(assocIdExprs(bnd, bndi.map(Var)), ctx));
    const [ej, r] = genExpr(gs, ctx_, e);
    if (r !== "ExprInline") throw new Error("genCase: expected ExprInline");
    const [aj, ar] = genAlts(gs, ctx, bnd, at, alts);
    return [mconcatJStgStat([...bndi.map(decl), ej, aj]), ar];
  }

  const rj = genRet(gs, ctx, bnd, at, alts, l);
  const ctx_ = ctxSetTop(bnd, ctxSetTarget(assocIdExprs(bnd, regsFromR1.map(register)), ctx));
  const [ej] = genExpr(gs, ctx_, e);
  return [mconcatJStgStat([rj, ej]), "ExprCont"];
}

export function genRet(
  gs: GenState,
  ctx: ExprCtx,
  e: Binder,
  at: import("../stg.js").AltType,
  as: StgAlt[],
  l: LiveVars,
): JStgStat {
  const st = stackState(gs);
  const allRefs: Binder[] = [];
  const seen = new Set<number>();
  for (const a of as) {
    for (const [k, v] of exprRefs(gs.gsUnfloated, a.body)) if (!seen.has(k)) (seen.add(k), allRefs.push(v));
  }
  const lneLive = allRefs.reduce((m, i) => Math.max(m, ctxLneBindingStackSize(ctx, i) ?? 0), 0);
  const ctx_ = ctxLneShrinkStack(ctx, lneLive);
  const lneVars = ctxLneFrameVars(ctx_).map(([v]) => v);
  const isLne = (i: Binder): boolean => ctxIsLneBinding(ctx, i) || ctxIsLneLiveVar(ctx_, i);
  const nonLne = [...l.values()].filter((i) => !isLne(i));

  const altRegs = ((): JSRep[] => {
    switch (at.tag) {
      case "PrimAlt":
        // GHC reads the rep off the alternative's TyCon; stg.ts's PrimAlt has
        // no payload. IntV is the common prim rep and, unlike PtrV, never
        // makes the RTS trace a non-pointer.
        return [JSRep.IntV];
      case "MultiValAlt":
        return idJSRep(e);
      default:
        return [JSRep.PtrV];
    }
  })();

  const r = freshIdent(gs);
  const pushLne = pushLneFrame(gs, lneLive, ctx);
  const free = optimizeFree(gs, 0, nonLne);
  const pushRet = pushRetArgs(gs, free, Var(r));

  const fun = resetSlots(st, () => {
    const decs = declVarsForId(gs, e);
    const load = assignAll(identsForId(gs, e).map(Var), regsFromR1.map(register));
    const loadv = verifyRuntimeReps(gs, [e]);
    const ras = loadRetArgs(gs, free);
    const rasv = verifyRuntimeReps(gs, free.map(([x]) => x));
    const rlne = popLneFrame(gs, false, lneLive, ctx_);
    const rlnev = verifyRuntimeReps(gs, [...lneVars]);
    const [alts_] = genAlts(gs, ctx_, e, at, as);
    return mconcatJStgStat([decs, load, loadv, ras, rasv, rlne, rlnev, alts_, returnStack]);
  });

  const sr = genStaticRefs(gs, l); // srt
  emitClosureInfo(gs, {
    var: r,
    regs: { tag: "CIRegs", skip: 0, types: altRegs },
    name: r,
    layout: fixedLayout([
      ...[...free].reverse().map(([x]) => stackSlotType(unaryTypeJSRepId(x))),
      ...lneVars.map((v) => stackSlotType(unaryTypeJSRepId(v))),
    ]),
    type: { tag: "CIStackFrame" },
    static: sr,
  });
  emitToplevel(gs, { tag: "FuncStat", ident: r, args: [], body: fun });
  return mconcatJStgStat([pushLne, pushRet]);
}

/** Consume an Stg case alternative and generate the corresponding alternative
 * in JS land. If one alternative is a continuation then we must normalize the
 * other alternatives. See 'Branch' and 'normalizeBranches'. */
export function genAlts(
  gs: GenState,
  ctx: ExprCtx,
  e: Binder,
  at: import("../stg.js").AltType,
  alts: StgAlt[],
): [JStgStat, ExprResult] {
  const st = stackState(gs);
  const result = ((): [JStgStat, ExprResult] => {
    switch (at.tag) {
      case "PolyAlt": {
        if (alts.length !== 1) throw new Error("genAlts: multiple polyalt");
        const b = mkAlgBranch(gs, ctx, e, alts[0]);
        return [b.branch_stat, b.branch_result];
      }

      case "PrimAlt": {
        if (alts.length === 1) {
          const ie = varsForId(gs, e);
          const bs = alts[0].binders;
          const dids = mconcatJStgStat(bs.map((b) => declVarsForId(gs, b)));
          const bss = bs.flatMap((b) => varsForId(gs, b));
          const [ej, er] = genExpr(gs, ctx, alts[0].body);
          return [mconcatJStgStat([dids, assignAll(bss, ie), ej]), er];
        }
        const ie = varsForId(gs, e);
        const [r, bss] = normalizeBranches(
          ctx,
          alts.map((a) => isolateSlots(st, () => mkPrimIfBranch(gs, ctx, [primRepToJSRep({ tag: "IntRep" })], a))),
        );
        setSlots(st, []);
        return [mkSw(ie, bss), r];
      }

      case "MultiValAlt": {
        if (alts.length !== 1) throw new Error("genAlts: unexpected MultiValAlt shape");
        const eids = varsForId(gs, e);
        const load = loadUbxTup(gs, eids, alts[0].binders, at.arity);
        const [ej, er] = genExpr(gs, ctx, alts[0].body);
        return [mconcatJStgStat([load, ej]), er];
      }

      case "AlgAlt": {
        if (alts.length === 1 && at.typeName.startsWith("(#")) {
          throw new Error("genAlts: unexpected unboxed tuple");
        }
        if (alts.length === 1) {
          const b = mkAlgBranch(gs, ctx, e, alts[0]);
          return [b.branch_stat, b.branch_result];
        }
        if (alts.length === 2 && alts[0].con.tag === "DataAlt" && isBoolDataCon(alts[0].con.con)) {
          const dc = alts[0].con.con;
          const i = varForId(gs, e);
          const [r, nbs] = normalizeBranches(
            ctx,
            alts.map((a) => isolateSlots(st, () => mkAlgBranch(gs, ctx, e, a))),
          );
          if (nbs.length !== 2) throw new Error("genAlts: invalid branches for Bool");
          const [b1, b2] = nbs;
          const s: JStgStat =
            dc.tag === 2
              ? { tag: "IfStat", cond: i, then: b1.branch_stat, else: b2.branch_stat }
              : { tag: "IfStat", cond: i, then: b2.branch_stat, else: b1.branch_stat };
          setSlots(st, []);
          return [s, r];
        }
        const ei = varForId(gs, e);
        const [r, brs] = normalizeBranches(
          ctx,
          alts.map((a) => isolateSlots(st, () => mkAlgBranch(gs, ctx, e, a))),
        );
        setSlots(st, []);
        return [mkSwitch({ tag: "SelExpr", obj: { tag: "SelExpr", obj: ei, field: name("f") }, field: name("a") }, brs), r];
      }
    }
  })();

  const ver = verifyMatchRep(gs, e, at);
  return [mconcatJStgStat([ver, result[0]]), result[1]];
}

/** If 'StgToJSConfig.csRuntimeAssert' is set, then generate an assertion that
 * asserts the pattern match is valid. */
export function verifyMatchRep(gs: GenState, x: Binder, alt: import("../stg.js").AltType): JStgStat {
  if (!getSettings(gs).runtimeAssert) return memptyJStgStat;
  if (alt.tag !== "AlgAlt") return memptyJStgStat;
  return appS("h$verify_match_alg", [jString(alt.typeName), ...varsForId(gs, x)]);
}

/** A 'Branch' represents a possible branching path of an Stg case statement,
 * i.e., a possible code path from an 'StgAlt'. */
export interface Branch<A> {
  branch_expr: A;
  branch_stat: JStgStat;
  branch_result: ExprResult;
}

/** If one branch ends in a continuation but another is inline, we need to
 * adjust the inline branch to use the continuation convention. */
export function normalizeBranches<A>(ctx: ExprCtx, brs: Array<Branch<A>>): [ExprResult, Array<Branch<A>>] {
  if (brs.every((b) => b.branch_result === "ExprCont")) return ["ExprCont", brs];
  if (branchResult(brs.map((b) => b.branch_result)) === "ExprCont") {
    const mkCont = (b: Branch<A>): Branch<A> =>
      b.branch_result === "ExprInline"
        ? {
            ...b,
            branch_stat: mconcatJStgStat([
              b.branch_stat,
              assignAll(regsFromR1.map(register), ctxTarget(ctx).flatMap((t) => t.expr)),
            ]),
            branch_result: "ExprCont",
          }
        : b;
    return ["ExprCont", brs.map(mkCont)];
  }
  return ["ExprInline", brs];
}

/** Load an unboxed tuple: get all Idents from the input Ids, declare them as
 * JS variables and bind them, in order, to 'es'. */
export function loadUbxTup(gs: GenState, es: JStgExpr[], bs: Binder[], _n: number): JStgStat {
  const bs_ = bs.flatMap((b) => identsForId(gs, b));
  return declAssignAll(bs_, es);
}

export function mkSw(es: JStgExpr[], cases: Array<Branch<JStgExpr[] | undefined>>): JStgStat {
  if (es.length === 1) {
    return mkSwitch(
      es[0],
      cases.map((c) => ({ ...c, branch_expr: c.branch_expr === undefined ? undefined : c.branch_expr[0] })),
    );
  }
  return mkIfElse(es, cases);
}

/** Switch for pattern matching on constructors or prims */
export function mkSwitch(e: JStgExpr, cases: Array<Branch<JStgExpr | undefined>>): JStgStat {
  const n = cases.filter((c) => c.branch_expr !== undefined);
  const d = cases.filter((c) => c.branch_expr === undefined);

  if (n.length === 1 && d.length === 1) {
    return {
      tag: "IfStat",
      cond: { tag: "InfixExpr", op: "StrictEqOp", left: e, right: n[0].branch_expr as JStgExpr },
      then: n[0].branch_stat,
      else: d[0].branch_stat,
    };
  }
  if (n.length === 2 && d.length === 0) {
    return {
      tag: "IfStat",
      cond: { tag: "InfixExpr", op: "StrictEqOp", left: e, right: n[0].branch_expr as JStgExpr },
      then: n[0].branch_stat,
      else: n[1].branch_stat,
    };
  }
  const addBreak = (b: Branch<JStgExpr | undefined>): [JStgExpr, JStgStat] => {
    if (b.branch_expr === undefined) throw new Error("mkSwitch: addBreak");
    return [b.branch_expr, mconcatJStgStat([b.branch_stat, { tag: "BreakStat" }])];
  };
  if (d.length === 0) {
    return { tag: "SwitchStat", scrut: e, cases: n.slice(0, -1).map(addBreak), default: n[n.length - 1].branch_stat };
  }
  if (d.length === 1) {
    return { tag: "SwitchStat", scrut: e, cases: n.map(addBreak), default: d[0].branch_stat };
  }
  throw new Error("mkSwitch: multiple default cases");
}

/** if/else for pattern matching on things that js cannot switch on. The list
 * of branches is expected to have the default alternative first, if it
 * exists. */
export function mkIfElse(e: JStgExpr[], s: Array<Branch<JStgExpr[] | undefined>>): JStgStat {
  const go = (xs: Array<Branch<JStgExpr[] | undefined>>): JStgStat => {
    if (xs.length === 0) throw new Error("mkIfElse: empty expression list");
    if (xs.length === 1) return xs[0].branch_stat; // only one 'nothing' allowed
    const [b, ...rest] = xs;
    if (b.branch_expr === undefined) throw new Error("mkIfElse: multiple DEFAULT cases");
    return { tag: "IfStat", cond: mkEq(e, b.branch_expr), then: b.branch_stat, else: go(rest) };
  };
  return go([...s].reverse());
}

/** Wrapper to construct sequences of (===), e.g.
 *
 *     mkEq [l0,l1,l2] [r0,r1,r2] = (l0 === r0) && (l1 === r1) && (l2 === r2)
 */
export function mkEq(es1: JStgExpr[], es2: JStgExpr[]): JStgExpr {
  if (es1.length !== es2.length) throw new Error("mkEq: incompatible expressions");
  const eqs = es1.map((l, k): JStgExpr => ({ tag: "InfixExpr", op: "StrictEqOp", left: l, right: es2[k] }));
  return eqs.reduce((a, b) => ({ tag: "InfixExpr", op: "LAndOp", left: a, right: b }));
}

export function mkAlgBranch(gs: GenState, top: ExprCtx, d: Binder, alt: StgAlt): Branch<JStgExpr | undefined> {
  if (alt.con.tag === "DataAlt" && isUnboxableCon(alt.con.con) && alt.binders.length === 1) {
    const idd = varForId(gs, d);
    const fldx = identsForId(gs, alt.binders[0]);
    if (fldx.length !== 1) throw new Error("mkAlgBranch: invalid size");
    const [ej, er] = genExpr(gs, top, alt.body);
    return {
      branch_expr: undefined,
      branch_stat: mconcatJStgStat([declAssign_(fldx[0], idd), ej]),
      branch_result: er,
    };
  }
  const cc = caseCond(gs, alt.con);
  const idd = varForId(gs, d);
  const b = loadParams(gs, idd, alt.binders);
  const [ej, er] = genExpr(gs, top, alt.body);
  return { branch_expr: cc, branch_stat: mconcatJStgStat([b, ej]), branch_result: er };
}

/** Generate a primitive If-expression */
export function mkPrimIfBranch(gs: GenState, top: ExprCtx, _vt: JSRep[], alt: StgAlt): Branch<JStgExpr[] | undefined> {
  const ic = ifCond(gs, alt.con);
  const [ej, er] = genExpr(gs, top, alt.body);
  return { branch_expr: ic, branch_stat: ej, branch_result: er };
}

export function ifCond(gs: GenState, con: import("../stg.js").AltCon): JStgExpr[] | undefined {
  switch (con.tag) {
    case "DataAlt":
      return [jInt(con.con.tag)];
    case "LitAlt":
      return genLit(gs, con.lit);
    case "DEFAULT":
      return undefined;
  }
}

export function caseCond(gs: GenState, con: import("../stg.js").AltCon): JStgExpr | undefined {
  switch (con.tag) {
    case "DEFAULT":
      return undefined;
    case "DataAlt":
      return jInt(con.con.tag);
    case "LitAlt": {
      const es = genLit(gs, con.lit);
      if (es.length !== 1) throw new Error("caseCond: expected single-variable literal");
      return es[0];
    }
  }
}

/** Load parameters from constructor */
export function loadParams(gs: GenState, from: JStgExpr, args: Binder[]): JStgStat {
  // `use = repeat True` in GHC - fixme clean up
  const as: Ident[] = args.flatMap((a) => identsForId(gs, a));
  if (as.length === 0) return memptyJStgStat;
  if (as.length === 1) return declAssign_(as[0], sel(from, closureField1_));
  if (as.length === 2) {
    return mconcatJStgStat([declAssign_(as[0], sel(from, closureField1_)), declAssign_(as[1], sel(from, closureField2_))]);
  }
  const [x, ...xs] = as;
  const d = freshIdent(gs);
  const loadConVarsIfUsed = mconcatJStgStat(
    xs.map((c, k) => declAssign_(c, { tag: "SelExpr", obj: Var(d), field: name(dataFieldName(k + 1)) })),
  );
  return mconcatJStgStat([
    declAssign_(x, sel(from, closureField1_)),
    declAssign_(d, sel(from, closureField2_)),
    loadConVarsIfUsed,
  ]);
}

const sel = (o: JStgExpr, f: string): JStgExpr => ({ tag: "SelExpr", obj: o, field: name(f) });

/** Determine if a branch will end in a continuation or not. If not the inline
 * branch must be normalized. See 'normalizeBranches'. NB. not a Monoid. */
export function branchResult(xs: ExprResult[]): ExprResult {
  if (xs.length === 0) throw new Error("branchResult: empty list");
  if (xs.length === 1) return xs[0];
  return xs.includes("ExprCont") ? "ExprCont" : "ExprInline";
}

/** Push return arguments onto the stack. The Bool tracks whether the value is
 * already on the stack or not, used in 'StgToJS.Stack.pushOptimized'. */
export function pushRetArgs(gs: GenState, free: Array<[Binder, number, boolean]>, fun: JStgExpr): JStgStat {
  const rs = free.map(([i, n, b]): [JStgExpr, boolean] => [genIdArg(gs, i)[n - 1], b]);
  return pushOptimized(stackState(gs), getSettings(gs), [...rs, [fun, false]]);
}

/** Load the return arguments then pop the stack frame */
export function loadRetArgs(gs: GenState, free: Array<[Binder, number, boolean]>): JStgStat {
  const ids = free.map(([i, n]) => genIdStackArgI(gs, i)[n - 1]);
  return popSkipI(stackState(gs), 1, ids);
}

/** All identifiers referenced by the expression (does not traverse into nested
 * functions). GHC.JS.Transform's `identsE` is the same walk. */
export const allVars = (e: JStgExpr): Ident[] => identsE(e);

/** Allocate multiple, possibly mutually recursive, closures */
export function allocDynAll(
  gs: GenState,
  haveDecl: boolean,
  middle: JStgStat | undefined,
  cls: ClsEntry[],
): JStgStat {
  const settings = getSettings(gs);
  if (cls.length === 1 && middle === undefined) {
    const [to, entry, free] = cls[0];
    if (!free.some((f) => allVars(f).includes(to))) {
      return allocDynamic(settings, !haveDecl, to, entry, free);
    }
  }

  const middle_ = middle ?? memptyJStgStat;
  const declMaybe = (i: Ident, e: JStgExpr): JStgStat =>
    haveDecl ? assign_(Var(i), e) : declAssign_(i, e);

  const objs = mconcatJStgStat(
    cls.map(([i, f]) =>
      declMaybe(
        i,
        settings.inlineAlloc
          ? {
              tag: "ValExpr",
              value: jhFromList([
                [closureInfo_, f],
                [closureField1_, null_],
                [closureField2_, null_],
                [closureMeta_, zero_],
              ]),
            }
          : { tag: "ApplExpr", fn: hdC, args: [f] },
      ),
    ),
  );

  const fillObj = ([ident, , es]: ClsEntry): JStgStat => {
    const i = Var(ident);
    if (es.length === 0) return memptyJStgStat;
    if (es.length === 1) return assign_(closureField1(i), es[0]);
    if (es.length === 2) {
      return mconcatJStgStat([assign_(closureField1(i), es[0]), assign_(closureField2(i), es[1])]);
    }
    const [ex, ...rest] = es;
    if (settings.inlineAlloc || rest.length > jsClosureCount) {
      return mconcatJStgStat([
        assign_(closureField1(i), ex),
        assign_(closureField2(i), {
          tag: "ValExpr",
          value: jhFromList(rest.map((e, k): [string, JStgExpr] => [dataFieldName(k + 1), e])),
        }),
      ]);
    }
    return mconcatJStgStat([
      assign_(closureField1(i), ex),
      assign_(closureField2(i), { tag: "ApplExpr", fn: allocData(rest.length), args: rest }),
    ]);
  };

  const checkObjs = settings.assertRts
    ? cls.map(([i]): JStgStat => appS("h$checkObj", [Var(i)]))
    : [];

  return mconcatJStgStat([objs, middle_, ...cls.map(fillObj), ...checkObjs]);
}

/** Generate a primop. This function wraps around the real generator
 * 'GHC.StgToJS.genPrim', handling the 'ExprCtx' and all arguments before
 * generating the primop. */
export function genPrimOp(gs: GenState, ctx: ExprCtx, op: string, args: StgArg[]): [JStgStat, ExprResult] {
  const as = args.flatMap((a) => genArg(gs, a));
  const prof = getSettings(gs).prof;
  const bound = getSettings(gs).boundsCheck;
  const jsm = initJSM();
  const res = runJSM(jsm, (js) =>
    withTag(js, "h$PRM", (js2) =>
      // CONSERVATIVE: Expr.hs passes the primop's result `Type`; stg.ts's
      // StgOpApp carries none. prim.ts consults it for exactly one thing -
      // whether a TagToEnumOp returns Bool - so the general (non-Bool) code
      // path is selected.
      genPrim(js2, prof, bound, { isBoolTy: false }, op, ctxTarget(ctx).flatMap((t) => t.expr), as),
    ),
  );
  return res.tag === "PrimInline" ? [res.stat, "ExprInline"] : [res.stat, "ExprCont"];
}
