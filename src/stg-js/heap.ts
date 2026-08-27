/** Ported from GHC/StgToJS/Heap.hs.
 *
 * Accessors for the JS heap-object layout: a closure is a plain JS object with
 * fields `f` (infotable), `d1`/`d2` (payload), `m` (meta) and `cc` (cost
 * centre), and the infotable carries `t` (closure type) and `a` (con tag /
 * function arity - deliberately the same field, they never coexist).
 *
 * Haskell's primed names (`isThunk'`, `conTag'`, ... - the variants that take
 * an infotable instead of a closure) are spelled with a trailing underscore
 * here, since `'` is not a TS identifier character. The unprimed field-name
 * constants keep their own trailing underscore from the Haskell source.
 */
import type { JStgExpr } from "../js/jstg-syntax.js";
import { String_ } from "../js/jstg-syntax.js";
import { jString, sel_, strictEq_, typeOf, if_ } from "../js/make.js";
import { ClosureType, closureTypeToJExpr } from "./types.js";

/** Closure infotable field name */
export const closureInfo_ = "f";

/** Closure first payload field name */
export const closureField1_ = "d1";

/** Closure second payload field name */
export const closureField2_ = "d2";

/** Closure meta field name */
export const closureMeta_ = "m";

/** Closure cost-center field name */
export const closureCC_ = "cc";

/** Infotable type field name */
const infoClosureType_ = "t";

/** Infotable tag field name */
const infoConTag_ = "a";

/** Infotable arity field name */
const infoFunArity_ = "a";

export const jTyObject: JStgExpr = jString("object");

/** Closure type from infotable */
export const infoClosureType = (f: JStgExpr): JStgExpr => sel_(f, infoClosureType_);

/** Function arity from infotable */
export const infoFunArity = (f: JStgExpr): JStgExpr => sel_(f, infoFunArity_);

export const closureType = (c: JStgExpr): JStgExpr => infoClosureType(closureInfo(c));

export const isObject = (c: JStgExpr): JStgExpr => strictEq_(typeOf(c), String_("object"));

export const isThunk = (c: JStgExpr): JStgExpr => strictEq_(closureType(c), closureTypeToJExpr(ClosureType.Thunk));

export const isThunk_ = (f: JStgExpr): JStgExpr => strictEq_(infoClosureType(f), closureTypeToJExpr(ClosureType.Thunk));

export const isBlackhole = (c: JStgExpr): JStgExpr => strictEq_(closureType(c), closureTypeToJExpr(ClosureType.Blackhole));

export const isFun = (c: JStgExpr): JStgExpr => strictEq_(closureType(c), closureTypeToJExpr(ClosureType.Fun));

export const isFun_ = (f: JStgExpr): JStgExpr => strictEq_(infoClosureType(f), closureTypeToJExpr(ClosureType.Fun));

export const isPap = (c: JStgExpr): JStgExpr => strictEq_(closureType(c), closureTypeToJExpr(ClosureType.Pap));

export const isPap_ = (f: JStgExpr): JStgExpr => strictEq_(infoClosureType(f), closureTypeToJExpr(ClosureType.Pap));

export const isCon = (c: JStgExpr): JStgExpr => strictEq_(closureType(c), closureTypeToJExpr(ClosureType.Con));

export const isCon_ = (f: JStgExpr): JStgExpr => strictEq_(infoClosureType(f), closureTypeToJExpr(ClosureType.Con));

export const conTag = (c: JStgExpr): JStgExpr => conTag_(closureInfo(c));

export const conTag_ = (f: JStgExpr): JStgExpr => sel_(f, infoConTag_);

/** Get closure infotable */
export const closureInfo = (p: JStgExpr): JStgExpr => sel_(p, closureInfo_);

/** Get closure metadata */
export const closureMeta = (p: JStgExpr): JStgExpr => sel_(p, closureMeta_);

/** Get closure cost-center */
export const closureCC = (p: JStgExpr): JStgExpr => sel_(p, closureCC_);

/** Get closure extra field 1 */
export const closureField1 = (p: JStgExpr): JStgExpr => sel_(p, closureField1_);

/** Get closure extra field 2 */
export const closureField2 = (p: JStgExpr): JStgExpr => sel_(p, closureField2_);

/** Number of arguments (arity & 0xff = arguments, arity >> 8 = number of registers) */
export const funArity = (c: JStgExpr): JStgExpr => infoFunArity(closureInfo(c));

/** arity of a partial application */
export const papArity = (cp: JStgExpr): JStgExpr => closureField1(closureField2(cp));

/** Arity tag (tag >> 8 = registers, tag & 0xff = arguments) of a heap object
 * `c`. Pass `f` when a reference to the infotable is already in hand - it
 * saves looking up `c.f` twice. */
export function funOrPapArity(c: JStgExpr, f: JStgExpr | undefined): JStgExpr {
  return f === undefined
    ? if_(isFun(c), funArity(c), papArity(c))
    : if_(isFun_(f), infoFunArity(f), papArity(c));
}
