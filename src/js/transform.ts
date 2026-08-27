/** Port of GHC.JS.Transform: collects identifiers out of the staged AST, and
 * translates the staged (JStg) AST into the final (JS) AST once building is
 * done. */
import type { Ident } from "./ident.js";
import type { JStgStat, JStgExpr, JVal as JStgVal, Op as StgOp, UOp as StgUOp, AOp as StgAOp } from "./jstg-syntax.js";
import type { JStat, JExpr, JVal, Op, UOp, AOp } from "./syntax.js";

export function identsS(s: JStgStat): Ident[] {
  switch (s.tag) {
    case "DeclStat": return [s.ident, ...(s.value ? identsE(s.value) : [])];
    case "ReturnStat": return identsE(s.value);
    case "IfStat": return [...identsE(s.cond), ...identsS(s.then), ...identsS(s.else)];
    case "WhileStat": return [...identsE(s.cond), ...identsS(s.body)];
    case "ForStat": return [...identsS(s.init), ...identsE(s.cond), ...identsS(s.step), ...identsS(s.body)];
    case "ForInStat": return [s.ident, ...identsE(s.obj), ...identsS(s.body)];
    case "SwitchStat": return [
      ...identsE(s.scrut),
      ...s.cases.flatMap(([e, st]) => [...identsE(e), ...identsS(st)]),
      ...identsS(s.default),
    ];
    case "TryStat": return [...identsS(s.body), s.ident, ...identsS(s.catch), ...identsS(s.finally)];
    case "BlockStat": return s.stats.flatMap(identsS);
    case "ApplStat": return [...identsE(s.fn), ...s.args.flatMap(identsE)];
    case "UOpStat": return identsE(s.value);
    case "AssignStat": return [...identsE(s.lhs), ...identsE(s.rhs)];
    case "LabelStat": return identsS(s.body);
    case "BreakStat": return [];
    case "ContinueStat": return [];
    case "FuncStat": return [s.ident, ...s.args, ...identsS(s.body)];
    case "ThrowStat": return identsE(s.value);
    case "RawStat": return [];
  }
}

export function identsE(e: JStgExpr): Ident[] {
  switch (e.tag) {
    case "ValExpr": return identsV(e.value);
    case "SelExpr": return identsE(e.obj); // do not rename properties
    case "IdxExpr": return [...identsE(e.obj), ...identsE(e.index)];
    case "InfixExpr": return [...identsE(e.left), ...identsE(e.right)];
    case "UOpExpr": return identsE(e.value);
    case "IfExpr": return [...identsE(e.cond), ...identsE(e.then), ...identsE(e.else)];
    case "ApplExpr": return [...identsE(e.fn), ...e.args.flatMap(identsE)];
    case "RawExpr": return [];
  }
}

export function identsV(v: JStgVal): Ident[] {
  switch (v.tag) {
    case "JVar": return [v.ident];
    case "JList": return v.values.flatMap(identsE);
    case "JDouble": case "JInt": case "JStr": case "JRegEx": case "JBool": return [];
    case "JHash": return v.entries.flatMap(([, e]) => identsE(e));
    case "JFunc": return [...v.args, ...identsS(v.body)];
  }
}

//------------------------------------------------------------------------------
//                            Translation
//------------------------------------------------------------------------------

export function jStgStatToJS(s: JStgStat): JStat {
  switch (s.tag) {
    case "DeclStat": return { tag: "DeclStat", ident: s.ident, value: s.value && jStgExprToJS(s.value) };
    case "ReturnStat": return { tag: "ReturnStat", value: jStgExprToJS(s.value) };
    case "IfStat": return { tag: "IfStat", cond: jStgExprToJS(s.cond), then: jStgStatToJS(s.then), else: jStgStatToJS(s.else) };
    case "WhileStat": return { tag: "WhileStat", isDo: s.isDo, cond: jStgExprToJS(s.cond), body: jStgStatToJS(s.body) };
    case "ForStat": return { tag: "ForStat", init: jStgStatToJS(s.init), cond: jStgExprToJS(s.cond), step: jStgStatToJS(s.step), body: jStgStatToJS(s.body) };
    case "ForInStat": return { tag: "ForInStat", isEach: s.isEach, ident: s.ident, obj: jStgExprToJS(s.obj), body: jStgStatToJS(s.body) };
    case "SwitchStat": return {
      tag: "SwitchStat",
      scrut: jStgExprToJS(s.scrut),
      cases: s.cases.map(([e, st]): [JExpr, JStat] => [jStgExprToJS(e), jStgStatToJS(st)]),
      default: jStgStatToJS(s.default),
    };
    case "TryStat": return { tag: "TryStat", body: jStgStatToJS(s.body), ident: s.ident, catch: jStgStatToJS(s.catch), finally: jStgStatToJS(s.finally) };
    case "BlockStat": return { tag: "BlockStat", stats: s.stats.map(jStgStatToJS) };
    case "ApplStat": return { tag: "ApplStat", fn: jStgExprToJS(s.fn), args: s.args.map(jStgExprToJS) };
    case "UOpStat": return { tag: "UOpStat", op: jStgUOpToJS(s.op), value: jStgExprToJS(s.value) };
    case "AssignStat": return { tag: "AssignStat", lhs: jStgExprToJS(s.lhs), op: jStgAOpToJS(s.op), rhs: jStgExprToJS(s.rhs) };
    case "LabelStat": return { tag: "LabelStat", label: s.label, body: jStgStatToJS(s.body) };
    case "BreakStat": return { tag: "BreakStat", label: s.label };
    case "ContinueStat": return { tag: "ContinueStat", label: s.label };
    case "FuncStat": return { tag: "FuncStat", ident: s.ident, args: s.args, body: jStgStatToJS(s.body) };
    case "ThrowStat": return { tag: "ThrowStat", value: jStgExprToJS(s.value) };
    case "RawStat": return { tag: "RawStat", source: s.source };
  }
}

export function jStgExprToJS(e: JStgExpr): JExpr {
  switch (e.tag) {
    case "ValExpr": return { tag: "ValExpr", value: jStgValToJS(e.value) };
    case "SelExpr": return { tag: "SelExpr", obj: jStgExprToJS(e.obj), field: e.field };
    case "IdxExpr": return { tag: "IdxExpr", obj: jStgExprToJS(e.obj), index: jStgExprToJS(e.index) };
    case "InfixExpr": return { tag: "InfixExpr", op: jStgOpToJS(e.op), left: jStgExprToJS(e.left), right: jStgExprToJS(e.right) };
    case "UOpExpr": return { tag: "UOpExpr", op: jStgUOpToJS(e.op), value: jStgExprToJS(e.value) };
    case "IfExpr": return { tag: "IfExpr", cond: jStgExprToJS(e.cond), then: jStgExprToJS(e.then), else: jStgExprToJS(e.else) };
    case "ApplExpr": return { tag: "ApplExpr", fn: jStgExprToJS(e.fn), args: e.args.map(jStgExprToJS) };
    case "RawExpr": return { tag: "RawExpr", source: e.source };
  }
}

export function jStgValToJS(v: JStgVal): JVal {
  switch (v.tag) {
    case "JVar": return { tag: "JVar", ident: v.ident };
    case "JList": return { tag: "JList", values: v.values.map(jStgExprToJS) };
    case "JDouble": return { tag: "JDouble", value: v.value };
    case "JInt": return { tag: "JInt", value: v.value };
    case "JStr": return { tag: "JStr", value: v.value };
    case "JRegEx": return { tag: "JRegEx", value: v.value };
    case "JBool": return { tag: "JBool", value: v.value };
    case "JHash": return {
      tag: "JHash",
      // lexically sorted, matching jStgValToJS's satHash/compareHash - avoids
      // the non-determinism that an unsorted map traversal would introduce
      entries: [...v.entries].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)).map(([k, e]): [string, JExpr] => [k, jStgExprToJS(e)]),
    };
    case "JFunc": return { tag: "JFunc", args: v.args, body: jStgStatToJS(v.body) };
  }
}

export function jStgOpToJS(op: StgOp): Op {
  return op;
}

export function jStgUOpToJS(op: StgUOp): UOp {
  return op;
}

export function jStgAOpToJS(op: StgAOp): AOp {
  return op;
}
