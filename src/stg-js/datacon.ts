/** Port of GHC.StgToJS.DataCon: code generation of data constructors. */
import type { Ident } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { Var } from "../js/jstg-syntax.js";
import { true_, false_, zero_ } from "../js/make.js";
import type { DataCon } from "../stg.js";
import { newClosure, mkClosure, allocClsA, jsClosureCount } from "./closure.js";
import type { ExprCtx } from "./expr-ctx.js";
import { ctxTarget } from "./expr-ctx.js";
import type { GenState } from "./monad.js";
import { getSettings } from "./monad.js";
import { varForDataConWorker } from "./ids.js";
import type { StgToJSConfig } from "./types.js";
import { assignToExprCtx, isBoolDataCon, isUnboxableCon, isUnboxedTupleDataCon } from "./utils.js";

/** Generate a data constructor. Special handling for unboxed tuples. */
export function genCon(gs: GenState, ctx: ExprCtx, con: DataCon, args: JStgExpr[]): JStgStat {
  if (isUnboxedTupleDataCon(con)) return assignToExprCtx(ctx, args);

  const target = ctxTarget(ctx).flatMap((t) => t.expr);
  if (target.length === 1 && target[0].tag === "ValExpr" && target[0].value.tag === "JVar") {
    return allocCon(gs, target[0].value.ident, con, args);
  }
  throw new Error(`genCon: unhandled DataCon ${con.name}`);
}

/** Allocate a data constructor. Allocate in this context means bind the data
 * constructor to 'to'.
 *
 * GHC threads a CostCentreStack through for profiling; ghcts models no cost
 * centres, so the profiling branch (`ccsVarJ`) is dropped and the closure is
 * allocated without a cc field. */
export function allocCon(gs: GenState, to: Ident, con: DataCon, xs: JStgExpr[]): JStgStat {
  if (isBoolDataCon(con) || isUnboxableCon(con)) {
    return { tag: "AssignStat", lhs: Var(to), op: "AssignOp", rhs: allocUnboxedCon(con, xs) };
  }
  const e = varForDataConWorker(gs, con);
  return allocDynamic(getSettings(gs), false, to, e, xs);
}

/** Allocate an unboxed data constructor. If we have a bool we calculate the
 * right value. If not then we expect a singleton list and unbox by converting
 * 'C x' to 'x'. NB. This function may throw. */
export function allocUnboxedCon(con: DataCon, xs: JStgExpr[]): JStgExpr {
  if (xs.length === 0) {
    if (isBoolDataCon(con) && con.tag === 1) return false_;
    if (isBoolDataCon(con) && con.tag === 2) return true_;
  }
  if (xs.length === 1 && isUnboxableCon(con)) return xs[0];
  throw new Error(`allocUnboxedCon: not an unboxed constructor: ${con.name}`);
}

/** Allocate an entry function. See 'GHC.StgToJS' for the object layout. */
export function allocDynamicE(inlineAlloc: boolean, entry: JStgExpr, free: JStgExpr[], cc?: JStgExpr): JStgExpr {
  if (inlineAlloc || free.length > jsClosureCount) {
    return newClosure(mkClosure(entry, free, zero_, cc));
  }
  const allocFun = allocClsA(free.length);
  return { tag: "ApplExpr", fn: allocFun, args: [entry, ...free, ...(cc === undefined ? [] : [cc])] };
}

/** Allocate a dynamic object. */
export function allocDynamic(
  s: StgToJSConfig,
  needDecl: boolean,
  to: Ident,
  entry: JStgExpr,
  free: JStgExpr[],
  cc?: JStgExpr,
): JStgStat {
  const value = allocDynamicE(s.inlineAlloc, entry, free, cc);
  return needDecl ? { tag: "DeclStat", ident: to, value } : { tag: "AssignStat", lhs: Var(to), op: "AssignOp", rhs: value };
}
