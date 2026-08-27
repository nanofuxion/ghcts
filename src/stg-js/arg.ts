/** Port of GHC.StgToJS.Arg: code generation of application arguments.
 *
 * Note [ Unboxable Literals Optimization ]
 * ~~~~~~~~~~~~~~~~~~
 *
 * Boxable types in the JS backend are represented as heap objects. Some types,
 * such as Int8, do not benefit from being wrapped in an object in the JS
 * runtime. This optimization detects such types and changes the code generator
 * to generate a more efficient representation, saving one level of
 * indirection. Instead of a wrapper object with a field for the value's
 * payload:
 *
 *   var anInt8 = { d1 = <Int8# payload>
 *                , f  : info table / entry function which scrutinizes it
 *                };
 *
 * we instead generate:
 *
 *   var anInt8 = <Int8# payload>;
 *
 * This fires when: the type has a single data constructor; that constructor
 * holds a single monomorphic field; and the value is distinguishable from a
 * THUNK using JavaScript's `typeof`.
 *
 * How is this sound? Normally it would violate call-by-need, but the JS
 * backend consumes STG, so we can statically tell whether the value in
 * question will be a THUNK, and the runtime can tell with `typeof`: an Int8
 * contains an Int8#, whose JS type is 'number', while a THUNK of type Int8 is
 * an 'object' that may have to be entered. A type with a 'ThreadId#' field is
 * not subject to this because it must be a JS 'object'. Int64# likewise: it
 * does not fit in one JavaScript variable and so needs an 'object'.
 */
import type { Ident } from "../js/ident.js";
import type { JStgExpr } from "../js/jstg-syntax.js";
import { global } from "../js/jstg-syntax.js";
import { true_, false_ } from "../js/make.js";
import type { Binder, DataCon, StgArg, StgExpr } from "../stg.js";
import { allocDynamicE, allocUnboxedCon } from "./datacon.js";
import type { StaticArg, StaticLit, StaticUnboxed, StaticVal } from "./literal.js";
import { genLit, genStaticLit, staticLitToJExpr } from "./literal.js";
import type { GenState, StackSlot } from "./monad.js";
import { emitStatic, getSettings } from "./monad.js";
import { identForId, identForIdN, identForDataConWorker, varForId, varForIdN, varForDataConWorker } from "./ids.js";
import { idIsMultiVar, idIsVoid, idSlotCount, isBoolDataCon, isUnboxableCon } from "./utils.js";

/** GHC compares against the wired-in `trueDataConId`/`falseDataConId`; ghcts
 * binders have no wired-in identity, so the name is the only handle. */
const isTrueDataConId = (i: Binder): boolean => i.name === "True";
const isFalseDataConId = (i: Binder): boolean => i.name === "False";
const isConsDataCon = (dc: DataCon): boolean => dc.name === ":";

/** Generate JS code for static arguments. */
export function genStaticArg(gs: GenState, a: StgArg): StaticArg[] {
  if (a.tag === "StgLitArg") return genStaticLit(a.lit).map(staticLitArg);
  const i = a.id;
  const expr = gs.gsUnfloated.get(i.unique);
  if (expr !== undefined) return unfloatedStatic(gs, expr);
  if (idIsVoid(i)) return [];
  if (isTrueDataConId(i)) return [staticLitArg({ tag: "BoolLit", value: true })];
  if (isFalseDataConId(i)) return [staticLitArg({ tag: "BoolLit", value: false })];
  if (idIsMultiVar(i)) {
    return range(idSlotCount(i)).map((n): StaticArg => ({ tag: "StaticObjArg", name: identForIdN(gs, i, n) }));
  }
  return [{ tag: "StaticObjArg", name: identForId(gs, i) }];
}

function unfloatedStatic(gs: GenState, x: StgExpr): StaticArg[] {
  if (x.tag === "StgLit") return genStaticLit(x.lit).map(staticLitArg);
  if (x.tag === "StgConApp") {
    const dc = x.con;
    if (isBoolDataCon(dc) || isUnboxableCon(dc)) {
      return [allocUnboxedConStatic(dc, x.args.flatMap((a) => genStaticArg(gs, a)))];
    }
    if (x.args.length === 0) return [{ tag: "StaticObjArg", name: identForDataConWorker(gs, dc) }];
    const as = x.args.flatMap((a) => genStaticArg(gs, a));
    return [{ tag: "StaticConArg", name: identForDataConWorker(gs, dc), args: as }];
  }
  throw new Error(`genArg: unexpected unfloated expression: ${x.tag}`);
}

/** Generate JS code for an StgArg. */
export function genArg(gs: GenState, a: StgArg): JStgExpr[] {
  if (a.tag === "StgLitArg") return genLit(gs, a.lit);
  const i = a.id;
  const expr = gs.gsUnfloated.get(i.unique);
  if (expr !== undefined) return unfloated(gs, expr);
  if (idIsVoid(i)) return [];
  if (isTrueDataConId(i)) return [true_];
  if (isFalseDataConId(i)) return [false_];
  if (idIsMultiVar(i)) return range(idSlotCount(i)).map((n) => varForIdN(gs, i, n));
  return [varForId(gs, i)];
}

function unfloated(gs: GenState, x: StgExpr): JStgExpr[] {
  if (x.tag === "StgLit") return genLit(gs, x.lit);
  if (x.tag === "StgConApp") {
    const dc = x.con;
    if (isBoolDataCon(dc) || isUnboxableCon(dc)) {
      return [allocUnboxedCon(dc, x.args.flatMap((a) => genArg(gs, a)))];
    }
    // GHC uses `varForId (dataConWorkId dc)`; ghcts has no worker Id, so the
    // worker symbol is generated straight from the DataCon.
    if (x.args.length === 0) return [varForDataConWorker(gs, dc)];
    const as = x.args.flatMap((a) => genArg(gs, a));
    return [allocDynamicE(getSettings(gs).inlineAlloc, varForDataConWorker(gs, dc), as)];
  }
  throw new Error(`genArg: unexpected unfloated expression: ${x.tag}`);
}

/** Generate a Var as JStgExpr. */
export function genIdArg(gs: GenState, i: Binder): JStgExpr[] {
  return genArg(gs, { tag: "StgVarArg", id: i });
}

/** Generate an Id as an Ident. */
export function genIdArgI(gs: GenState, i: Binder): Ident[] {
  if (idIsVoid(i)) return [];
  if (idIsMultiVar(i)) return range(idSlotCount(i)).map((n) => identForIdN(gs, i, n));
  return [identForId(gs, i)];
}

/** Generate IDs for stack arguments. See 'StgToJS.Expr.loadRetArgs'. */
export function genIdStackArgI(gs: GenState, i: Binder): Array<[Ident, StackSlot]> {
  return genIdArgI(gs, i).map((ident, k): [Ident, StackSlot] => [ident, { tag: "SlotId", id: i, size: k + 1 }]);
}

/** Allocate Static Constructors.
 *
 * GHC also resolves a CostCentreStack label here; ghcts models no cost
 * centres, so statics are emitted without one. */
export function allocConStatic(gs: GenState, to: Ident, con: DataCon, args: StgArg[]): void {
  const xs = args.flatMap((a) => genStaticArg(gs, a));
  // see Note [ Unboxable Literals Optimization ] for the purpose of these checks
  if (xs.length === 0) {
    if (isBoolDataCon(con) && con.tag === 1) return emitStatic(gs, to, unboxed({ tag: "StaticUnboxedBool", value: false }));
    if (isBoolDataCon(con) && con.tag === 2) return emitStatic(gs, to, unboxed({ tag: "StaticUnboxedBool", value: true }));
    return emitStatic(gs, to, { tag: "StaticData", name: identForDataConWorker(gs, con), args: [] });
  }
  if (xs.length === 1 && isUnboxableCon(con)) {
    const x = xs[0];
    if (x.tag !== "StaticLitArg") throw new Error("allocConStatic: invalid unboxed literal");
    switch (x.lit.tag) {
      case "IntLit":
        return emitStatic(gs, to, unboxed({ tag: "StaticUnboxedInt", value: x.lit.value }));
      case "BoolLit":
        return emitStatic(gs, to, unboxed({ tag: "StaticUnboxedBool", value: x.lit.value }));
      case "DoubleLit":
        return emitStatic(gs, to, unboxed({ tag: "StaticUnboxedDouble", value: x.lit.value }));
      default:
        throw new Error("allocConStatic: invalid unboxed literal");
    }
  }
  if (isConsDataCon(con)) {
    if (args.length < 2) throw new Error("allocConStatic: invalid args for consDataCon");
    return emitStatic(gs, to, allocateStaticList(gs, [args[0]], args[1]));
  }
  return emitStatic(gs, to, { tag: "StaticData", name: identForDataConWorker(gs, con), args: xs });
}

/** Allocate unboxed constructors. */
export function allocUnboxedConStatic(con: DataCon, xs: StaticArg[]): StaticArg {
  if (xs.length === 0) {
    if (isBoolDataCon(con) && con.tag === 1) return staticLitArg({ tag: "BoolLit", value: false });
    if (isBoolDataCon(con) && con.tag === 2) return staticLitArg({ tag: "BoolLit", value: true });
  }
  if (xs.length === 1 && xs[0].tag === "StaticLitArg" && (xs[0].lit.tag === "IntLit" || xs[0].lit.tag === "DoubleLit")) {
    return xs[0];
  }
  throw new Error(`allocUnboxedConStatic: not an unboxed constructor: ${con.name}`);
}

/** Allocate Static list. */
export function allocateStaticList(gs: GenState, xs: StgArg[], a: StgArg): StaticVal {
  if (a.tag !== "StgVarArg") throw new Error("allocateStaticList: unexpected literal in list");
  const i = a.id;
  if (i.name === "[]") return listAlloc(gs, xs); // isDataConId_maybe i == Just nilDataCon
  const e = gs.gsUnfloated.get(i.unique);
  if (e !== undefined && e.tag === "StgConApp" && isConsDataCon(e.con) && e.args.length === 2) {
    return allocateStaticList(gs, [e.args[0], ...xs], e.args[1]);
  }
  return listAlloc(gs, xs, a);
}

function listAlloc(gs: GenState, xs: StgArg[], r?: StgArg): StaticVal {
  const as = [...xs].reverse().flatMap((x) => genStaticArg(gs, x));
  if (r === undefined) return { tag: "StaticList", args: as };
  const r_ = genStaticArg(gs, r);
  if (r_.length === 1 && r_[0].tag === "StaticObjArg") return { tag: "StaticList", args: as, tail: r_[0].name };
  throw new Error("allocateStaticList: invalid argument (tail)");
}

/** Generate JS code corresponding to a static arg. */
export function jsStaticArg(a: StaticArg): JStgExpr {
  switch (a.tag) {
    case "StaticLitArg":
      return staticLitToJExpr(a.lit);
    case "StaticObjArg":
      return global(a.name);
    case "StaticConArg":
      return allocDynamicE(false, global(a.name), a.args.map(jsStaticArg));
  }
}

/** Generate JS code corresponding to a list of static args. */
export function jsStaticArgs(as: StaticArg[]): JStgExpr {
  return { tag: "ValExpr", value: { tag: "JList", values: as.map(jsStaticArg) } };
}

const staticLitArg = (lit: StaticLit): StaticArg => ({ tag: "StaticLitArg", lit });
const unboxed = (value: StaticUnboxed): StaticVal => ({ tag: "StaticUnboxed", value });
const range = (n: number): number[] => Array.from({ length: n }, (_, k) => k + 1);
