/** Port of GHC.JS.Syntax: the "final" JS AST, produced by translating the
 * staged GHC.JS.JStg.Syntax tree (see transform.ts / jStgStatToJS). Same
 * concrete shape as JStgStat/JStgExpr/JVal - GHC keeps these as separate
 * nominal types purely so a stray staged node can't leak into optimized code;
 * we mirror that separation with distinct type names over the same shapes. */
import type { Ident } from "./ident.js";
import { name } from "./ident.js";
import type { Op, UOp, AOp, SaneDouble, JsLabel } from "./jstg-syntax.js";

export type JLabel = JsLabel;

export type JStat =
  | { tag: "DeclStat"; ident: Ident; value?: JExpr }
  | { tag: "ReturnStat"; value: JExpr }
  | { tag: "IfStat"; cond: JExpr; then: JStat; else: JStat }
  | { tag: "WhileStat"; isDo: boolean; cond: JExpr; body: JStat }
  | { tag: "ForStat"; init: JStat; cond: JExpr; step: JStat; body: JStat }
  | { tag: "ForInStat"; isEach: boolean; ident: Ident; obj: JExpr; body: JStat }
  | { tag: "SwitchStat"; scrut: JExpr; cases: Array<[JExpr, JStat]>; default: JStat }
  | { tag: "TryStat"; body: JStat; ident: Ident; catch: JStat; finally: JStat }
  | { tag: "BlockStat"; stats: JStat[] }
  | { tag: "ApplStat"; fn: JExpr; args: JExpr[] }
  | { tag: "UOpStat"; op: UOp; value: JExpr }
  | { tag: "AssignStat"; lhs: JExpr; op: AOp; rhs: JExpr }
  | { tag: "LabelStat"; label: JLabel; body: JStat }
  | { tag: "BreakStat"; label?: JLabel }
  | { tag: "ContinueStat"; label?: JLabel }
  | { tag: "FuncStat"; ident: Ident; args: Ident[]; body: JStat }
  /** TS-only addition: GHC's own Syntax.hs has no throw-statement
   * constructor at all (the RTS never needs one), so this isn't a subset of
   * a Haskell node - it's a deliberate, documented extension for ghcts's
   * runtime-error paths (non-exhaustive patterns, pattern-match failures). */
  | { tag: "ThrowStat"; value: JExpr }
  /** TS-only escape hatch, see jstg-syntax.ts's RawStat. */
  | { tag: "RawStat"; source: string };

export const memptyJStat: JStat = { tag: "BlockStat", stats: [] };

const isEmptyBlock = (s: JStat): boolean => s.tag === "BlockStat" && s.stats.length === 0;

/** GHC.JS.Syntax's Semigroup instance: appendJStat. */
export function appendJStat(mx: JStat, my: JStat): JStat {
  if (isEmptyBlock(mx)) return my;
  if (isEmptyBlock(my)) return mx;
  if (mx.tag === "BlockStat" && my.tag === "BlockStat") return { tag: "BlockStat", stats: [...mx.stats, ...my.stats] };
  if (mx.tag === "BlockStat") return { tag: "BlockStat", stats: [...mx.stats, my] };
  if (my.tag === "BlockStat") return { tag: "BlockStat", stats: [mx, ...my.stats] };
  return { tag: "BlockStat", stats: [mx, my] };
}

export const mconcatJStat = (stats: JStat[]): JStat => stats.reduce(appendJStat, memptyJStat);

export type JExpr =
  | { tag: "ValExpr"; value: JVal }
  | { tag: "SelExpr"; obj: JExpr; field: Ident }
  | { tag: "IdxExpr"; obj: JExpr; index: JExpr }
  | { tag: "InfixExpr"; op: Op; left: JExpr; right: JExpr }
  | { tag: "UOpExpr"; op: UOp; value: JExpr }
  | { tag: "IfExpr"; cond: JExpr; then: JExpr; else: JExpr }
  | { tag: "ApplExpr"; fn: JExpr; args: JExpr[] }
  /** TS-only escape hatch, see jstg-syntax.ts's RawExpr. */
  | { tag: "RawExpr"; source: string };

export type JVal =
  | { tag: "JVar"; ident: Ident }
  | { tag: "JList"; values: JExpr[] }
  | { tag: "JDouble"; value: SaneDouble }
  | { tag: "JInt"; value: bigint }
  | { tag: "JStr"; value: string }
  | { tag: "JRegEx"; value: string }
  | { tag: "JBool"; value: boolean }
  | { tag: "JHash"; entries: Array<[string, JExpr]> }
  | { tag: "JFunc"; args: Ident[]; body: JStat };

export { type Op, type UOp, type AOp } from "./jstg-syntax.js";

export const New = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "NewOp", value: x });
export const PreInc = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "PreIncOp", value: x });
export const PostInc = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "PostIncOp", value: x });
export const PreDec = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "PreDecOp", value: x });
export const PostDec = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "PostDecOp", value: x });
export const Not = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "NotOp", value: x });
export const Negate = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "NegOp", value: x });
export const BNot = (x: JExpr): JExpr => ({ tag: "UOpExpr", op: "BNotOp", value: x });

export const Add = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "AddOp", left: x, right: y });
export const Sub = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "SubOp", left: x, right: y });
export const Mul = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "MulOp", left: x, right: y });
export const Div = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "DivOp", left: x, right: y });
export const Mod = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "ModOp", left: x, right: y });
export const BOr = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "BOrOp", left: x, right: y });
export const BAnd = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "BAndOp", left: x, right: y });
export const BXor = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "BXorOp", left: x, right: y });
export const LOr = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "LOrOp", left: x, right: y });
export const LAnd = (x: JExpr, y: JExpr): JExpr => ({ tag: "InfixExpr", op: "LAndOp", left: x, right: y });

export const Int = (x: bigint | number): JExpr => ({ tag: "ValExpr", value: { tag: "JInt", value: BigInt(x) } });
export const String_ = (x: string): JExpr => ({ tag: "ValExpr", value: { tag: "JStr", value: x } });
export const Var = (x: Ident): JExpr => ({ tag: "ValExpr", value: { tag: "JVar", ident: x } });

/** construct a JS variable reference */
export const var_ = (fastString: string): JExpr => Var(name(fastString));

/** The JS literal 'true' */
export const true_: JExpr = { tag: "ValExpr", value: { tag: "JBool", value: true } };

/** The JS literal 'false' */
export const false_: JExpr = { tag: "ValExpr", value: { tag: "JBool", value: false } };
