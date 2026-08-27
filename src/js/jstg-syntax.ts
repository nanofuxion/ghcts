/** Port of GHC.JS.JStg.Syntax: the deeply embedded, "staged" JS eDSL that the
 * JS backend's runtime system is written in. Nothing fancy - a straightforward
 * deeply embedded DSL, mirrored one constructor at a time. */
import type { Ident } from "./ident.js";
import { name } from "./ident.js";

export type JsLabel = string;

export type JStgStat =
  | { tag: "DeclStat"; ident: Ident; value?: JStgExpr }
  | { tag: "ReturnStat"; value: JStgExpr }
  | { tag: "IfStat"; cond: JStgExpr; then: JStgStat; else: JStgStat }
  | { tag: "WhileStat"; isDo: boolean; cond: JStgExpr; body: JStgStat }
  | { tag: "ForStat"; init: JStgStat; cond: JStgExpr; step: JStgStat; body: JStgStat }
  | { tag: "ForInStat"; isEach: boolean; ident: Ident; obj: JStgExpr; body: JStgStat }
  | { tag: "SwitchStat"; scrut: JStgExpr; cases: Array<[JStgExpr, JStgStat]>; default: JStgStat }
  | { tag: "TryStat"; body: JStgStat; ident: Ident; catch: JStgStat; finally: JStgStat }
  | { tag: "BlockStat"; stats: JStgStat[] }
  | { tag: "ApplStat"; fn: JStgExpr; args: JStgExpr[] }
  | { tag: "UOpStat"; op: UOp; value: JStgExpr }
  | { tag: "AssignStat"; lhs: JStgExpr; op: AOp; rhs: JStgExpr }
  | { tag: "LabelStat"; label: JsLabel; body: JStgStat }
  | { tag: "BreakStat"; label?: JsLabel }
  | { tag: "ContinueStat"; label?: JsLabel }
  | { tag: "FuncStat"; ident: Ident; args: Ident[]; body: JStgStat }
  /** TS-only addition: mirrors Syntax.ts's ThrowStat - GHC's JStg/Syntax.hs
   * has no throw-statement constructor either. */
  | { tag: "ThrowStat"; value: JStgExpr }
  /** TS-only escape hatch with no Haskell counterpart: splices pre-rendered
   * JS source directly into the tree. Real GHC.JS has no such constructor -
   * every node is built through the EDSL. ghcts still needs this while parts
   * of the compiler emit source text instead of AST nodes (see compiler.ts). */
  | { tag: "RawStat"; source: string };

/** GHC.JS.JStg.Syntax's Monoid instance: mempty = BlockStat []. */
export const memptyJStgStat: JStgStat = { tag: "BlockStat", stats: [] };

const isEmptyBlock = (s: JStgStat): boolean => s.tag === "BlockStat" && s.stats.length === 0;

/** GHC.JS.JStg.Syntax's Semigroup instance: appendJStgStat. */
export function appendJStgStat(mx: JStgStat, my: JStgStat): JStgStat {
  if (isEmptyBlock(mx)) return my;
  if (isEmptyBlock(my)) return mx;
  if (mx.tag === "BlockStat" && my.tag === "BlockStat") return { tag: "BlockStat", stats: [...mx.stats, ...my.stats] };
  if (mx.tag === "BlockStat") return { tag: "BlockStat", stats: [...mx.stats, my] };
  if (my.tag === "BlockStat") return { tag: "BlockStat", stats: [mx, ...my.stats] };
  return { tag: "BlockStat", stats: [mx, my] };
}

/** mconcat over JStgStat: folds with appendJStgStat / memptyJStgStat. */
export const mconcatJStgStat = (stats: JStgStat[]): JStgStat => stats.reduce(appendJStgStat, memptyJStgStat);

export type JStgExpr =
  | { tag: "ValExpr"; value: JVal }
  | { tag: "SelExpr"; obj: JStgExpr; field: Ident }
  | { tag: "IdxExpr"; obj: JStgExpr; index: JStgExpr }
  | { tag: "InfixExpr"; op: Op; left: JStgExpr; right: JStgExpr }
  | { tag: "UOpExpr"; op: UOp; value: JStgExpr }
  | { tag: "IfExpr"; cond: JStgExpr; then: JStgExpr; else: JStgExpr }
  | { tag: "ApplExpr"; fn: JStgExpr; args: JStgExpr[] }
  /** TS-only escape hatch, see RawStat above. */
  | { tag: "RawExpr"; source: string };

/** A double that is guaranteed comparable/orderable the way GHC's SaneDouble
 * is (Eq/Ord defined so that NaN == NaN); represented as a plain number since
 * TS has no distinct Double/SaneDouble types. */
export type SaneDouble = number;

export type JVal =
  | { tag: "JVar"; ident: Ident }
  | { tag: "JList"; values: JStgExpr[] }
  | { tag: "JDouble"; value: SaneDouble }
  | { tag: "JInt"; value: bigint }
  | { tag: "JStr"; value: string }
  | { tag: "JRegEx"; value: string }
  | { tag: "JBool"; value: boolean }
  | { tag: "JHash"; entries: Array<[string, JStgExpr]> }
  | { tag: "JFunc"; args: Ident[]; body: JStgStat };

export type Op =
  | "EqOp" | "StrictEqOp" | "NeqOp" | "StrictNeqOp"
  | "GtOp" | "GeOp" | "LtOp" | "LeOp"
  | "AddOp" | "SubOp" | "MulOp" | "DivOp" | "ModOp"
  | "LeftShiftOp" | "RightShiftOp" | "ZRightShiftOp"
  | "BAndOp" | "BOrOp" | "BXorOp" | "LAndOp" | "LOrOp"
  | "InstanceofOp" | "InOp";

export type UOp =
  | "NotOp" | "BNotOp" | "NegOp" | "PlusOp" | "NewOp" | "TypeofOp" | "DeleteOp"
  | "YieldOp" | "VoidOp" | "PreIncOp" | "PostIncOp" | "PreDecOp" | "PostDecOp";

export type AOp = "AssignOp" | "AddAssignOp" | "SubAssignOp";

// --------------------------------------------------------------------------
// Pattern synonyms over JS operators, ported as plain constructor functions
// since TypeScript has no pattern-synonym feature. Names match the Haskell
// pattern synonyms exactly.
// --------------------------------------------------------------------------

export const New = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "NewOp", value: x });
export const PreInc = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "PreIncOp", value: x });
export const PostInc = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "PostIncOp", value: x });
export const PreDec = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "PreDecOp", value: x });
export const PostDec = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "PostDecOp", value: x });
export const Not = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "NotOp", value: x });
export const Negate = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "NegOp", value: x });
export const BNot = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "BNotOp", value: x });

export const Add = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "AddOp", left: x, right: y });
export const Sub = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "SubOp", left: x, right: y });
export const Mul = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "MulOp", left: x, right: y });
export const Div = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "DivOp", left: x, right: y });
export const Mod = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "ModOp", left: x, right: y });
export const BOr = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "BOrOp", left: x, right: y });
export const BAnd = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "BAndOp", left: x, right: y });
export const BXor = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "BXorOp", left: x, right: y });
export const LOr = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "LOrOp", left: x, right: y });
export const LAnd = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "LAndOp", left: x, right: y });

export const Int = (x: bigint | number): JStgExpr => ({ tag: "ValExpr", value: { tag: "JInt", value: BigInt(x) } });
export const String_ = (x: string): JStgExpr => ({ tag: "ValExpr", value: { tag: "JStr", value: x } });
export const Var = (x: Ident): JStgExpr => ({ tag: "ValExpr", value: { tag: "JVar", ident: x } });
export const Func = (args: Ident[], body: JStgStat): JStgExpr => ({ tag: "ValExpr", value: { tag: "JFunc", args, body } });

/** construct a JS reference, intended to refer to a global name */
export const global = (fastString: string): JStgExpr => Var(name(fastString));

/** construct a JS reference, intended to refer to a local name */
export const local = (fastString: string): JStgExpr => Var(name(fastString));
