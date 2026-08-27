/** Port of GHC.JS.Optimizer: a shallow, continuation-passing-style peephole
 * optimizer over GHC.JS.Syntax. Each optimization pattern-matches on the head
 * of a statement stream; on a match it rewrites and calls `loop` (so the
 * result is optimized again, along with the rest of the chain); on no match
 * it calls `next` to hand the stream to the next optimization. The final
 * "optimization" is tailLoop, which walks to the next block and restarts the
 * pipeline - see Note [Unsafe JavaScript optimizations] below, ported
 * verbatim from the Haskell source. */
import type { JStat, JExpr, JVal } from "./syntax.js";
import * as Simple from "./opt-simple.js";

/*
Note [Unsafe JavaScript optimizations]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There are a number of optimizations that the JavaScript Backend performs that
are not sound with respect to arbitrary JavaScript. We still perform these
optimizations because we are not optimizing arbitrary JavaScript and under the
assumption that the JavaScript backend will not generate code that violates
the soundness of the optimizer. For example, deadCodeElim removes all
statements after a `return`, which is unsound in general (hoisted nested
function declarations could still be reachable) but never unsound for code
this backend actually generates.
*/

export function jsOptimize(s: JStat): JStat {
  return jsOptimizeStat(Simple.simpleOpt(s));
}

function jsOptimizeStat(s0: JStat): JStat {
  switch (s0.tag) {
    case "BlockStat": return { ...s0, stats: jsOptimize_(s0.stats) };
    case "ForStat": return { ...s0, init: jsOptimizeStat(s0.init), cond: jExprOptimize(s0.cond), step: jsOptimizeStat(s0.step), body: jsOptimizeStat(s0.body) };
    case "ForInStat": return { ...s0, body: jsOptimizeStat(s0.body) };
    case "WhileStat": return { ...s0, cond: jExprOptimize(s0.cond), body: jsOptimizeStat(s0.body) };
    case "SwitchStat": return { ...s0, cases: s0.cases.map(([c, cs]): [JExpr, JStat] => [c, jsOptimizeStat(cs)]), default: jsOptimizeStat(s0.default) };
    case "FuncStat": return { ...s0, body: jsOptimizeStat(s0.body) };
    case "IfStat": return { ...s0, cond: jExprOptimize(s0.cond), then: jsOptimizeStat(s0.then), else: jsOptimizeStat(s0.else) };
    case "TryStat": return { ...s0, body: jsOptimizeStat(s0.body), catch: jsOptimizeStat(s0.catch), finally: jsOptimizeStat(s0.finally) };
    case "LabelStat": return { ...s0, body: jsOptimizeStat(s0.body) };
    case "AssignStat": return { ...s0, lhs: jExprOptimize(s0.lhs), rhs: jExprOptimize(s0.rhs) };
    case "DeclStat": return s0.value === undefined ? s0 : { ...s0, value: jExprOptimize(s0.value) };
    case "ReturnStat": return { ...s0, value: jExprOptimize(s0.value) };
    case "UOpStat": return { ...s0, value: jExprOptimize(s0.value) };
    case "ApplStat": return { ...s0, fn: jExprOptimize(s0.fn), args: s0.args.map(jExprOptimize) };
    case "ThrowStat": return { ...s0, value: jExprOptimize(s0.value) };
    case "BreakStat": case "ContinueStat": case "RawStat": return s0;
  }
}

type BlockTrans = (stats: JStat[]) => JStat[];
type BlockOpt = (loop: BlockTrans, next: BlockTrans) => BlockTrans;

const memptyOpt: BlockOpt = (_loop, next) => next;
const combine = (a: BlockOpt, b: BlockOpt): BlockOpt => (loop, next) => a(loop, b(loop, next));
const combineAll = (opts: BlockOpt[]): BlockOpt => opts.reduceRight((acc, o) => combine(o, acc), memptyOpt);

function runBlockOpt(opt: BlockOpt, xs: JStat[]): JStat[] {
  const recur: BlockTrans = (ys) => opt(recur, (zs) => zs)(ys);
  return recur(xs);
}

function jsOptimize_(stats: JStat[]): JStat[] {
  const opts = combineAll([declareAssign, combineOps, deadCodeElim, tailLoop]);
  return runBlockOpt(opts, flattenBlocks(stats));
}

/** recur over a JExpr and optimize the JVals */
function jExprOptimize(e: JExpr): JExpr {
  switch (e.tag) {
    case "ValExpr": return { ...e, value: jValOptimize(e.value) };
    case "SelExpr": return { ...e, obj: jExprOptimize(e.obj) };
    case "IdxExpr": return { ...e, obj: jExprOptimize(e.obj), index: jExprOptimize(e.index) };
    case "UOpExpr": return { ...e, value: jExprOptimize(e.value) };
    case "IfExpr": return { ...e, then: jExprOptimize(e.then), else: jExprOptimize(e.else) };
    case "ApplExpr": return { ...e, fn: jExprOptimize(e.fn), args: e.args.map(jExprOptimize) };
    case "InfixExpr": return { ...e, left: jExprOptimize(e.left), right: jExprOptimize(e.right) };
    case "RawExpr": return e;
  }
}

/** drive optimizations to anonymous functions and over expressions */
function jValOptimize(v: JVal): JVal {
  switch (v.tag) {
    case "JFunc": return { ...v, body: jsOptimizeStat(v.body) };
    case "JList": return { ...v, values: v.values.map(jExprOptimize) };
    case "JHash": return { ...v, entries: v.entries.map(([k, e]): [string, JExpr] => [k, jExprOptimize(e)]) };
    case "JVar": case "JDouble": case "JInt": case "JStr": case "JRegEx": case "JBool": return v;
  }
}

/** Perform all the optimizations on the tail of a block. */
const tailLoop: BlockOpt = (loop, next) => (xs) => {
  if (xs.length === 0) return next([]);
  const [x, ...rest] = xs;
  return next([jsOptimizeStat(x), ...loop(rest)]);
};

/**
   Catch modify and assign operators:
      case 1: i = i + 1; ==> ++i;
      case 2: i = i - 1; ==> --i;
      case 3: i = i + n; ==> i += n;
      case 4: i = i - n; ==> i -= n;
 */
const combineOps: BlockOpt = (loop, next) => (xs) => {
  const [op1, op2, ...rest2] = xs;
  const tail1 = xs.slice(1);

  // var x = expr; return x; ==> return expr;
  if (op1?.tag === "DeclStat" && op1.value !== undefined && op2?.tag === "ReturnStat") {
    const declValue = op1.value, declIdent = op1.ident, ret = op2;
    if (ret.value.tag === "ValExpr" && ret.value.value.tag === "JVar" && ret.value.value.ident === declIdent) {
      return loop([{ tag: "ReturnStat", value: declValue }, ...rest2]);
    }
  }

  // x = expr; return x; ==> return expr;
  if (op1?.tag === "AssignStat" && op1.op === "AssignOp" && op1.lhs.tag === "ValExpr" && op1.lhs.value.tag === "JVar" && op2?.tag === "ReturnStat") {
    const assignIdent = op1.lhs.value.ident, assignRhs = op1.rhs, ret = op2;
    if (ret.value.tag === "ValExpr" && ret.value.value.tag === "JVar" && ret.value.value.ident === assignIdent) {
      return loop([{ tag: "ReturnStat", value: assignRhs }, ...rest2]);
    }
  }

  // h$sp -= 2; h$sp += 5; ==> h$sp += 3;
  if (op1 && op2) {
    const s1 = isStackAdjust(op1), s2 = isStackAdjust(op2);
    if (s1 !== undefined && s2 !== undefined) return loop([...mkStackAdjust(s1 + s2), ...rest2]);
  }

  // x = x + 1; ==> ++x;  x = x - 1; ==> --x;  x = x + n; ==> x += n;  x = x - n; ==> x -= n;
  if (op1?.tag === "AssignStat" && op1.op === "AssignOp" && op1.lhs.tag === "ValExpr" && op1.lhs.value.tag === "JVar" && op1.rhs.tag === "InfixExpr") {
    const ident = op1.lhs, i = op1.lhs.value.ident, rhs = op1.rhs;
    const isVar = (e: JExpr, name: string): boolean => e.tag === "ValExpr" && e.value.tag === "JVar" && e.value.ident === name;
    const isOne = (e: JExpr): boolean => e.tag === "ValExpr" && e.value.tag === "JInt" && e.value.value === 1n;
    if (isVar(rhs.left, i)) {
      if (rhs.op === "AddOp" && isOne(rhs.right)) return loop([{ tag: "UOpStat", op: "PreIncOp", value: ident }, ...tail1]);
      if (rhs.op === "SubOp" && isOne(rhs.right)) return loop([{ tag: "UOpStat", op: "PreDecOp", value: ident }, ...tail1]);
      if (rhs.op === "AddOp") return loop([{ tag: "AssignStat", lhs: ident, op: "AddAssignOp", rhs: rhs.right }, ...tail1]);
      if (rhs.op === "SubOp") return loop([{ tag: "AssignStat", lhs: ident, op: "SubAssignOp", rhs: rhs.right }, ...tail1]);
    } else if (isVar(rhs.right, i)) {
      // commutative cases
      if (rhs.op === "AddOp" && isOne(rhs.left)) return loop([{ tag: "UOpStat", op: "PreIncOp", value: ident }, ...tail1]);
      if (rhs.op === "AddOp") return loop([{ tag: "AssignStat", lhs: ident, op: "AddAssignOp", rhs: rhs.left }, ...tail1]);
    }
  }

  return next(xs);
};

/** Catch 'var i; i = q;' ==> 'var i = q;' */
const declareAssign: BlockOpt = (loop, next) => (xs) => {
  const [a, b, ...rest] = xs;
  if (a?.tag === "DeclStat" && a.value === undefined && b?.tag === "AssignStat" && b.op === "AssignOp" && b.lhs.tag === "ValExpr" && b.lhs.value.tag === "JVar" && b.lhs.value.ident === a.ident) {
    return loop([{ tag: "DeclStat", ident: a.ident, value: b.rhs }, ...rest]);
  }
  return next(xs);
};

/** Eliminate all code after a return statement - see Note [Unsafe JavaScript
 * optimizations]. Doesn't need to loop. */
const deadCodeElim: BlockOpt = (_loop, next) => (xs) => (xs[0]?.tag === "ReturnStat" ? next([xs[0]]) : next(xs));

/** remove nested blocks */
function flattenBlocks(stats: JStat[]): JStat[] {
  const out: JStat[] = [];
  for (const s of stats) {
    if (s.tag === "BlockStat") out.push(...flattenBlocks(s.stats));
    else out.push(s);
  }
  return out;
}

const sp: JExpr = { tag: "ValExpr", value: { tag: "JVar", ident: "h$sp" } };
const isSp = (e: JExpr): boolean => e.tag === "ValExpr" && e.value.tag === "JVar" && e.value.ident === "h$sp";

function isStackAdjust(s: JStat): bigint | undefined {
  if (s.tag === "UOpStat" && isSp(s.value)) {
    if (s.op === "PreIncOp" || s.op === "PostIncOp") return 1n;
    if (s.op === "PreDecOp" || s.op === "PostDecOp") return -1n;
  }
  if (s.tag === "AssignStat" && isSp(s.lhs) && s.rhs.tag === "ValExpr" && s.rhs.value.tag === "JInt") {
    if (s.op === "AddAssignOp") return s.rhs.value.value;
    if (s.op === "SubAssignOp") return -s.rhs.value.value;
  }
  if (s.tag === "AssignStat" && isSp(s.lhs) && s.op === "AssignOp" && s.rhs.tag === "InfixExpr" && isSp(s.rhs.left) && s.rhs.right.tag === "ValExpr" && s.rhs.right.value.tag === "JInt") {
    if (s.rhs.op === "AddOp") return s.rhs.right.value.value;
    if (s.rhs.op === "SubOp") return -s.rhs.right.value.value;
  }
  if (s.tag === "AssignStat" && isSp(s.lhs) && s.op === "AssignOp" && s.rhs.tag === "InfixExpr" && s.rhs.op === "AddOp" && s.rhs.left.tag === "ValExpr" && s.rhs.left.value.tag === "JInt" && isSp(s.rhs.right)) {
    return s.rhs.left.value.value;
  }
  return undefined;
}

function mkStackAdjust(n: bigint): JStat[] {
  if (n === 0n) return [];
  if (n === 1n) return [{ tag: "UOpStat", op: "PostIncOp", value: sp }];
  if (n === -1n) return [{ tag: "UOpStat", op: "PostDecOp", value: sp }];
  return n < 0n
    ? [{ tag: "AssignStat", lhs: sp, op: "AssignOp", rhs: { tag: "InfixExpr", op: "SubOp", left: sp, right: { tag: "ValExpr", value: { tag: "JInt", value: -n } } } }]
    : [{ tag: "AssignStat", lhs: sp, op: "AssignOp", rhs: { tag: "InfixExpr", op: "AddOp", left: sp, right: { tag: "ValExpr", value: { tag: "JInt", value: n } } } }];
}
