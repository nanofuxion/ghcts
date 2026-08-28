/** Port of GHC.StgToJS.Utils.
 *
 * A grab bag: expression assignment/coercion, the PrimRep <-> JSRep mapping,
 * reference and live-variable analysis over STG. The parts of Utils.hs that
 * consult Core `Type`s are not portable - ghcts's Binder and DataCon (see
 * stg.ts) carry no type - so those either take the representation as an
 * explicit argument or are omitted; each such spot is commented.
 */
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { mconcatJStgStat, memptyJStgStat } from "../js/jstg-syntax.js";
import { assign_, assignAllEqual } from "../js/make.js";
import { hdStablePtrBuf } from "./symbols.js";
import type { CILayout } from "./types.js";
import { JSRep, ciLayoutFixed, varSize } from "./types.js";
// Utils.hs exports varSize/isVoid; ghcts already has them in types.ts.
export { varSize, isVoid } from "./types.js";
import type { Binder, DataCon, StgArg, StgBinding, StgExpr, StgRhs, StgAlt } from "../stg.js";
import { UpdateFlag } from "../stg.js";
import type { ExprCtx } from "./expr-ctx.js";
import { ctxTarget } from "./expr-ctx.js";

/** GHC.Types.RepType.PrimRep, restricted to the non-vector reps the JS
 * backend supports. BoxedRep's payload is the levity (Unlifted/Lifted/unknown),
 * which assignCoerce below discriminates on. */
export type PrimRep =
  | { tag: "BoxedRep"; levity?: "Lifted" | "Unlifted" }
  | { tag: "IntRep" } | { tag: "Int8Rep" } | { tag: "Int16Rep" } | { tag: "Int32Rep" } | { tag: "Int64Rep" }
  | { tag: "WordRep" } | { tag: "Word8Rep" } | { tag: "Word16Rep" } | { tag: "Word32Rep" } | { tag: "Word64Rep" }
  | { tag: "AddrRep" }
  | { tag: "FloatRep" }
  | { tag: "DoubleRep" };

/** PrimOrVoidRep. */
export type PrimOrVoidRep = { tag: "VoidRep" } | { tag: "NVRep"; rep: PrimRep };

/** Typed expression - GHC.StgToJS.Types.TypedExpr. */
export interface TypedExpr {
  typ: PrimRep;
  expr: JStgExpr[];
}

export const typedExpr = (typ: PrimRep, expr: JStgExpr[]): TypedExpr => ({ typ, expr });

export function assignToTypedExprs(tes: TypedExpr[], es: JStgExpr[]): JStgStat {
  return assignAllEqual(tes.flatMap((t) => t.expr), es);
}

export function assignTypedExprs(tes: TypedExpr[], es: TypedExpr[]): JStgStat {
  // extract the JExprs, effectively unarising a RuntimeRep thing to multiple
  // VarType-repped things (e.g., AddrRep takes two VarType-regs)
  return assignAllEqual(tes.flatMap((t) => t.expr), es.flatMap((t) => t.expr));
}

export function assignToExprCtx(ctx: ExprCtx, es: JStgExpr[]): JStgStat {
  return assignToTypedExprs(ctxTarget(ctx), es);
}

/** Assign first expr only (if it exists), performing coercions between some
 * PrimReps (e.g. StablePtr# and Addr#). */
export function assignCoerce1(xs: TypedExpr[], ys: TypedExpr[]): JStgStat {
  if (xs.length === 1 && ys.length === 1) return assignCoerce(xs[0], ys[0]);
  // An empty list on the left denotes "assign nothing to n empty slots on the
  // right". Usually this shouldn't come up, but rare cases where the earlier
  // code can't correctly guess the size of type classes allocate slots that
  // aren't needed.
  if (xs.length === 0) return memptyJStgStat;
  throw new Error("assignCoerce1: lengths do not match");
}

const isUnliftedBoxed = (t: TypedExpr): boolean => t.typ.tag === "BoxedRep" && t.typ.levity === "Unlifted";

/** Assign p2 to p1 with optional coercion. */
export function assignCoerce(p1: TypedExpr, p2: TypedExpr): JStgStat {
  // Coercion between StablePtr# and Addr#
  if (p1.typ.tag === "AddrRep" && p1.expr.length === 2 && isUnliftedBoxed(p2) && p2.expr.length === 1) {
    return mconcatJStgStat([assign_(p1.expr[0], hdStablePtrBuf), assign_(p1.expr[1], p2.expr[0])]);
  }
  if (isUnliftedBoxed(p1) && p1.expr.length === 1 && p2.typ.tag === "AddrRep" && p2.expr.length === 2) {
    return assign_(p1.expr[0], p2.expr[1]);
  }
  return assignTypedExprs([p1], [p2]);
}

// ---------------------------------------------------------------------------
//                              Core Utils
// ---------------------------------------------------------------------------

/** Types whose single constructor holds a single field represented as a JS
 * Number, and are therefore unboxable - see Note [ Unboxable Literals
 * Optimization ] in arg.ts.
 *
 * GHC decides this from the constructor's field types (`dataConRepArgTys`);
 * ghcts's DataCon carries no field types, so the wired-in boxed primitives -
 * exactly the types for which `isUnboxable` holds in GHC - are listed here.
 * Int64/Word64 are absent on purpose: they are LongV, two JS variables. */
const unboxableTyCons: ReadonlySet<string> = new Set([
  "Int", "Int8", "Int16", "Int32",
  "Word", "Word8", "Word16", "Word32",
  "Char", "Float", "Double",
]);

/** can we unbox C x to x, only if x is represented as a Number */
export function isUnboxableCon(dc: DataCon): boolean {
  return dc.arity === 1 && dc.tag === 1 && unboxableTyCons.has(dc.typeName);
}

/** one-constructor types with one primitive field represented as a JS Number
 * can be unboxed */
export function isUnboxable(r: JSRep): boolean {
  return r === JSRep.DoubleV || r === JSRep.IntV; // IntV includes Char#
}

export function isBoolDataCon(dc: DataCon): boolean {
  return dc.typeName === "Bool";
}

/** Unboxed tuples are spelled `(# ,, #)`, as in GHC. */
export function isUnboxedTupleDataCon(dc: DataCon): boolean {
  return dc.name.startsWith("(#");
}

/** Number of slots occupied by a PrimRep. */
export enum SlotCount {
  NoSlot = 0,
  OneSlot = 1,
  TwoSlots = 2,
}

/** Return SlotCount as an Int. */
export const slotCount = (s: SlotCount): number => s;

export function jsRepSlots(r: JSRep): SlotCount {
  switch (r) {
    case JSRep.VoidV:
      return SlotCount.NoSlot;
    case JSRep.LongV: // hi, low
    case JSRep.AddrV: // obj/array, offset
      return SlotCount.TwoSlots;
    default:
      return SlotCount.OneSlot;
  }
}

export function isMultiVar(r: JSRep): boolean {
  return jsRepSlots(r) === SlotCount.TwoSlots;
}

export function primRepToJSRep(r: PrimRep): JSRep {
  switch (r.tag) {
    case "BoxedRep":
      return JSRep.PtrV;
    case "IntRep":
    case "Int8Rep":
    case "Int16Rep":
    case "Int32Rep":
    case "WordRep":
    case "Word8Rep":
    case "Word16Rep":
    case "Word32Rep":
      return JSRep.IntV;
    case "Int64Rep":
    case "Word64Rep":
      return JSRep.LongV;
    case "AddrRep":
      return JSRep.AddrV;
    case "FloatRep":
    case "DoubleRep":
      return JSRep.DoubleV;
  }
}

export function primOrVoidRepToJSRep(r: PrimOrVoidRep): JSRep {
  return r.tag === "VoidRep" ? JSRep.VoidV : primRepToJSRep(r.rep);
}

export function primRepSize(p: PrimRep): SlotCount {
  return jsRepSlots(primRepToJSRep(p));
}

/** standard fixed layout: payload types. Payload starts at .d1 for heap
 * objects, entry closest to Sp for stack frames. */
export function fixedLayout(vts: JSRep[]): CILayout {
  return ciLayoutFixed(vts.reduce((n, v) => n + varSize(v), 0), vts);
}

/** 2-var values might have been moved around separately, use DoubleV as
 * substitute; ObjV is 1 var, so this is no problem for implicit metadata.
 *
 * GHC derives `otype` from the Id's type; ghcts has to be handed it. */
export function stackSlotType(otype: JSRep): JSRep {
  return jsRepSlots(otype) === SlotCount.OneSlot ? otype : JSRep.DoubleV;
}

/** How many JS slots a binder occupies. stg.ts records this on the binder
 * itself (`arity`) because there is no type to compute it from; unannotated
 * binders are single-slot pointers, the overwhelmingly common case. */
export function idSlotCount(i: Binder): number {
  return i.arity ?? 1;
}
export const idIsVoid = (i: Binder): boolean => idSlotCount(i) === 0;
export const idIsMultiVar = (i: Binder): boolean => idSlotCount(i) === 2;

/** Associate the given values to each PrimRep in the given order, taking into
 * account the number of slots per PrimRep. */
export function assocPrimReps(rs: PrimRep[], vs: JStgExpr[]): Array<[PrimRep, JStgExpr[]]> {
  const out: Array<[PrimRep, JStgExpr[]]> = [];
  let i = 0;
  for (const r of rs) {
    const n = primRepSize(r);
    if (i + n > vs.length) throw new Error("assocPrimReps: not enough values");
    out.push([r, vs.slice(i, i + n)]);
    i += n;
  }
  return out;
}

/** Associate the given JStgExprs to the given PrimReps as TypedExprs. GHC's
 * `assocIdExprs` reads the reps off the Id's type; ghcts passes them in. */
export function assocExprs(rs: PrimRep[], es: JStgExpr[]): TypedExpr[] {
  return assocPrimReps(rs, es).map(([r, xs]) => typedExpr(r, xs));
}

export function mkArityTag(arity: number, registers: number): number {
  return arity | (registers << 8);
}

// ---------------------------------------------------------------------------
//                               Stg Utils
// ---------------------------------------------------------------------------

/** GHC's `Set Id`/`UniqFM Id` become Maps keyed on Binder.unique. Insertion
 * order is preserved, which keeps generated output deterministic the way
 * GHC's ordered Sets do. */
export type IdSet = Map<number, Binder>;
/** Id -> StgExpr map for unfloated arguments. */
export type UnfloatedMap = Map<number, StgExpr>;

/** A `DVarSet` is a `UniqDFM`, which carries an upper bound on the tags it has
 * handed out (`udfm_i`). `plusUDFM` compares the two bounds and inserts the
 * smaller set into the larger, so the larger side keeps its order and only the
 * other side's new keys are appended - which is why a free-variable list is
 * neither in occurrence order nor reversed. The bound lives in a side table so
 * that `IdSet` stays a plain Map for every other consumer; a Map built
 * anywhere else reads as a set whose bound is its size, which is what
 * `mkUniqDSet` would have produced. */
const bounds = new WeakMap<IdSet, number>();
const boundOf = (s: IdSet): number => bounds.get(s) ?? s.size;
const withBound = (s: IdSet, n: number): IdSet => {
  bounds.set(s, n);
  return s;
};

const singleton = (i: Binder): IdSet => withBound(new Map([[i.unique, i]]), 1);

/** `plusUDFM`. */
const union2 = (l: IdSet, r: IdSet): IdSet => {
  const [base, add] = boundOf(l) > boundOf(r) ? [l, r] : [r, l];
  const out = new Map(base);
  // A duplicate key keeps the tag it already had, but still costs a tag.
  for (const [k, v] of add) if (!out.has(k)) out.set(k, v);
  return withBound(out, boundOf(base) + add.size);
};

/** `unionManyUniqDSets`: foldl', with the empty set only for an empty list. */
const unions = (ss: IdSet[]): IdSet => (ss.length === 0 ? withBound(new Map(), 0) : ss.reduce(union2));

/** `delDVarSetList`. Deleting does not return the tag. */
const without = (s: IdSet, bs: Binder[]): IdSet => {
  const out = new Map(s);
  for (const b of bs) out.delete(b.unique);
  return withBound(out, boundOf(s));
};

/** collect Ids that this binding refers to (does not include the bindees
 * themselves). First argument is the unfloated-argument map. */
export function bindingRefs(u: UnfloatedMap, b: StgBinding): IdSet {
  return b.tag === "StgNonRec" ? rhsRefs(u, b.rhs) : unions(b.pairs.map(([, r]) => rhsRefs(u, r)));
}

export function rhsRefs(u: UnfloatedMap, rhs: StgRhs): IdSet {
  // GHC additionally pulls in `dataConImplicitTyThings`; ghcts's DataCon has
  // no implicit TyThings to collect.
  return rhs.tag === "StgRhsClosure" ? exprRefs(u, rhs.body) : unions(rhs.args.map((a) => argRefs(u, a)));
}

export function exprRefs(u: UnfloatedMap, e: StgExpr): IdSet {
  switch (e.tag) {
    case "StgApp":
      return unions([singleton(e.fn), ...e.args.map((a) => argRefs(u, a))]);
    case "StgConApp":
      return unions(e.args.map((a) => argRefs(u, a)));
    case "StgOpApp":
      return unions(e.args.map((a) => argRefs(u, a)));
    case "StgLit":
      return new Map();
    case "StgCase":
      return unions([exprRefs(u, e.scrutinee), ...e.alts.map((a) => altRefs(u, a))]);
    case "StgLet":
    case "StgLetNoEscape":
      return unions([bindingRefs(u, e.binding), exprRefs(u, e.body)]);
  }
}

export function altRefs(u: UnfloatedMap, alt: StgAlt): IdSet {
  return exprRefs(u, alt.body);
}

export function argRefs(u: UnfloatedMap, a: StgArg): IdSet {
  if (a.tag !== "StgVarArg") return new Map();
  const e = u.get(a.id.unique);
  return e === undefined ? singleton(a.id) : exprRefs(u, e);
}

/** True when the binding is a `StaticPtr` constructor application, which the
 * linker must export. GHC compares against `staticPtrDataConKey`. */
export function hasExport(bnd: StgBinding): boolean {
  const isExportedBind = (rhs: StgRhs): boolean => rhs.tag === "StgRhsCon" && rhs.con.name === "StaticPtr";
  return bnd.tag === "StgNonRec" ? isExportedBind(bnd.rhs) : bnd.pairs.some(([, r]) => isExportedBind(r));
}

export function collectTopIds(bnd: StgBinding): Binder[] {
  return bnd.tag === "StgNonRec" ? [bnd.binder] : bnd.pairs.map(([b]) => b);
}

export function collectIds(unfloated: UnfloatedMap, b: StgBinding): Binder[] {
  // GHC also rejects anything defined in GHC.Prim (no JS source file exists
  // for it); ghcts's Binder has no defining module to test.
  return [...bindingRefs(unfloated, b).values()].filter((i) => !i.name.startsWith("(#"));
}

// ---------------------------------------------------------------------------
//                               Live vars
// ---------------------------------------------------------------------------

export type LiveVars = IdSet;

/** GHC splits on `isGlobalId`; stg.ts's stand-in is the `exported` flag. */
export function liveStatic(l: LiveVars): LiveVars {
  return withBound(new Map([...l].filter(([, v]) => v.exported === true)), boundOf(l));
}

export function liveVars(l: LiveVars): LiveVars {
  return withBound(new Map([...l].filter(([, v]) => v.exported !== true)), boundOf(l));
}

export function stgBindLive(b: StgBinding): Array<[Binder, LiveVars]> {
  return b.tag === "StgNonRec" ? [[b.binder, stgRhsLive(b.rhs)]] : b.pairs.map(([i, r]): [Binder, LiveVars] => [i, stgRhsLive(r)]);
}

export function stgBindRhsLive(b: StgBinding): LiveVars {
  const bs = stgBindLive(b);
  return without(unions(bs.map(([, l]) => l)), bs.map(([i]) => i));
}

export function stgRhsLive(rhs: StgRhs): LiveVars {
  return rhs.tag === "StgRhsClosure"
    ? without(stgExprLive(true, rhs.body), rhs.args)
    : unions(rhs.args.map(stgArgLive));
}

export function stgArgLive(a: StgArg): LiveVars {
  return a.tag === "StgVarArg" ? singleton(a.id) : new Map();
}

export function stgExprLive(includeLHS: boolean, e: StgExpr): LiveVars {
  switch (e.tag) {
    case "StgApp":
      return unions([singleton(e.fn), ...e.args.map(stgArgLive)]);
    case "StgLit":
      return new Map();
    case "StgConApp":
    case "StgOpApp":
      return unions(e.args.map(stgArgLive));
    case "StgCase": {
      const al = without(unions(e.alts.map(stgAltLive)), [e.binder]);
      return includeLHS ? unions([stgExprLive(true, e.scrutinee), al]) : al;
    }
    case "StgLet":
    case "StgLetNoEscape":
      return without(unions([stgBindRhsLive(e.binding), stgExprLive(true, e.body)]), bindees(e.binding));
  }
}

export function stgAltLive(alt: StgAlt): LiveVars {
  return without(stgExprLive(true, alt.body), alt.binders);
}

export function bindees(b: StgBinding): Binder[] {
  return b.tag === "StgNonRec" ? [b.binder] : b.pairs.map(([i]) => i);
}

export function isUpdatableRhs(rhs: StgRhs): boolean {
  return rhs.tag === "StgRhsClosure" && rhs.update === UpdateFlag.Updatable;
}

export function stgLneLive_(b: StgBinding): Binder[] {
  const bound = new Set(bindees(b).map((i) => i.unique));
  return stgLneLive(b).filter((i) => !bound.has(i.unique));
}

export function stgLneLive(b: StgBinding): Binder[] {
  if (b.tag === "StgNonRec") return stgLneLiveExpr(b.rhs);
  const seen = new Map<number, Binder>();
  for (const [, rhs] of b.pairs) for (const i of stgLneLiveExpr(rhs)) if (!seen.has(i.unique)) seen.set(i.unique, i);
  return [...seen.values()];
}

export function stgLneLiveExpr(rhs: StgRhs): Binder[] {
  return [...liveVars(stgRhsLive(rhs)).values()];
}
