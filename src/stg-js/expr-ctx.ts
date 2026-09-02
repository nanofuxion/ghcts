/** Ported from GHC/StgToJS/ExprCtx.hs - the context an expression compiles in:
 * where its result goes, and the layout of the enclosing let-no-escape frame.
 *
 * ExprCtx is immutable in GHC and stays immutable here: every `ctxSet*` /
 * `ctxUpdate*` returns a fresh record rather than mutating, because codegen
 * relies on an outer context surviving a recursive call that extended it.
 */
import type { Binder } from "../stg.js";
import type { RealSrcSpan } from "./monad.js";
// GHC.StgToJS.Types' `TypedExpr` lives in ./utils.ts in ghcts, alongside the
// PrimRep stand-in it is parameterised by.
import type { TypedExpr } from "./utils.js";

export type { TypedExpr };

/** Context into which an expression is evaluated */
export interface ExprCtx {
  /** Top-level binding Id */
  readonly ctxTop: Binder;

  /** IDs known evaluated by the enclosing Core/STG let context. */
  readonly ctxEval: ReadonlySet<number>;

  /** Target variables for the evaluated expression */
  readonly ctxTarget: TypedExpr[];

  /** Source location */
  readonly ctxSrcSpan?: RealSrcSpan;

  // -------------------------
  // Handling of let-no-escape

  /** LNE bindings with their expected stack size, keyed on Binder.unique
   * (GHC uses a `UniqFM Id Int`).
   *
   * The number is the size of the stack when the LNE binding was defined. We
   * need to shrink the stack back to this size when we enter one of the
   * associated binder rhs: it expects its free variables at certain offsets in
   * the stack. */
  readonly ctxLneFrameBs: ReadonlyMap<number, number>;

  /** Contents of current LNE frame: variables and their index on the stack */
  readonly ctxLneFrameVars: ReadonlyArray<[Binder, number]>;

  /** Cache the length of `ctxLneFrameVars` */
  readonly ctxLneFrameSize: number;
}

/** Initialize an expression context in the context of the given top-level
 * binding Id */
export function initExprCtx(i: Binder): ExprCtx {
  return {
    ctxTop: i,
    ctxEval: new Set(),
    ctxTarget: [],
    ctxLneFrameBs: new Map(),
    ctxLneFrameVars: [],
    ctxLneFrameSize: 0,
  };
}

/** Set target */
export const ctxSetTarget = (t: TypedExpr[], ctx: ExprCtx): ExprCtx => ({ ...ctx, ctxTarget: t });

/** Set top-level binding Id */
export const ctxSetTop = (i: Binder, ctx: ExprCtx): ExprCtx => ({ ...ctx, ctxTop: i });

export const ctxAddEval = (ids: readonly Binder[], ctx: ExprCtx): ExprCtx => {
  const evals = new Set(ctx.ctxEval);
  for (const i of ids) evals.add(i.unique);
  return { ...ctx, ctxEval: evals };
};

/** Set source location */
export const ctxSetSrcSpan = (span: RealSrcSpan, ctx: ExprCtx): ExprCtx => ({ ...ctx, ctxSrcSpan: span });

/** Read the target of the expression being compiled */
export const ctxTarget = (ctx: ExprCtx): TypedExpr[] => ctx.ctxTarget;

/** Read the source location of the expression being compiled */
export const ctxSrcSpan = (ctx: ExprCtx): RealSrcSpan | undefined => ctx.ctxSrcSpan;

/** Update let-no-escape frame */
export function ctxUpdateLneFrame(
  newSpilledVars: ReadonlyArray<[Binder, number]>,
  newLneIds: readonly Binder[],
  ctx: ExprCtx,
): ExprCtx {
  const newFrameSize = ctx.ctxLneFrameSize + newSpilledVars.length;
  const bs = new Map(ctx.ctxLneFrameBs);
  for (const i of newLneIds) bs.set(i.unique, newFrameSize);
  return {
    ...ctx,
    ctxLneFrameBs: bs,
    ctxLneFrameSize: newFrameSize,
    ctxLneFrameVars: [...ctx.ctxLneFrameVars, ...newSpilledVars],
  };
}

/** Remove information about the current LNE frame */
export const ctxClearLneFrame = (ctx: ExprCtx): ExprCtx => ({
  ...ctx,
  ctxLneFrameBs: new Map(),
  ctxLneFrameVars: [],
  ctxLneFrameSize: 0,
});

export const ctxLneFrameVars = (ctx: ExprCtx): ReadonlyArray<[Binder, number]> => ctx.ctxLneFrameVars;

export const ctxLneFrameSize = (ctx: ExprCtx): number => ctx.ctxLneFrameSize;

/** Predicate: do we know for sure that the given Id is evaluated?
 *
 * GHC answers this from the tag signature InferTags attached to the Id
 * (`idTagSig_maybe`, plus a JoinId veto on `idDetails`). ghcts records the
 * same fact on `Binder.evaluated` after a `case` whose binder is a *fresh*
 * name for the WHNF. `Binder.strict` is `isStrictId` (function closures are
 * not thunks) and must not be read here: that would make `isInlineApp`
 * skip entering a data thunk. */
export function ctxIsEvaluated(i: Binder, ctx?: ExprCtx): boolean {
  if (i.join) return false;
  return i.evaluated === true || ctx?.ctxEval.has(i.unique) === true;
}

/** Return the LNE stack size associated to the given Id. Undefined when the
 * Id doesn't correspond to a LNE binding. */
export const ctxLneBindingStackSize = (ctx: ExprCtx, i: Binder): number | undefined =>
  ctx.ctxLneFrameBs.get(i.unique);

/** Does the given Id correspond to a LNE binding */
export const ctxIsLneBinding = (ctx: ExprCtx, i: Binder): boolean =>
  ctxLneBindingStackSize(ctx, i) !== undefined;

/** Does the given Id correspond to a LNE live var on the stack */
export const ctxIsLneLiveVar = (ctx: ExprCtx, i: Binder): boolean =>
  ctx.ctxLneFrameVars.some(([v]) => v.unique === i.unique);

/** Shrink the LNE stack to the given size */
export function ctxLneShrinkStack(ctx: ExprCtx, n: number): ExprCtx {
  const l = ctx.ctxLneFrameSize;
  if (l < n) throw new Error(`ctxLneShrinkStack: let-no-escape stack too short: ${l} < ${n}`);
  return { ...ctx, ctxLneFrameVars: ctx.ctxLneFrameVars.slice(0, n), ctxLneFrameSize: n };
}
