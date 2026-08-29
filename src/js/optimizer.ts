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

/** A rewrite that fires on the front of the stream: consume `consumed`
 * elements, replace them with `replacement` (put back at the front, so a
 * follow-on rewrite gets another look at it - matching GHC's `loop`). */
interface FrontRewrite {
  consumed: number;
  replacement: JStat[];
}

/** `runBlockOpt`/`tailLoop`'s CPS recursion (`opt(recur, id)(xs)`,
 * `next([jsOptimizeStat(x), ...loop(rest)])`) is GHC's own algorithm over a
 * lazy, structurally-shared `[JStat]`; the identical recursion over a strict
 * TypeScript array copies the tail at every level of `[x, ...rest]` and
 * `[...loop(rest)]`, which is O(n^2) memory and O(n) stack depth for a
 * whole-program statement list (the linker's largest blocks run into the
 * hundreds of thousands of statements). This drives the same three rewrite
 * rules (`declareAssign`, `combineOps`, `deadCodeElim`) with an explicit
 * loop instead: an index into the immutable input plus a small `pending`
 * buffer standing in for "the front of the stream still to be examined" -
 * a rewrite never produces more than the couple of elements the patterns
 * below match on, so `pending` never grows with the input. Same rewrites,
 * same order, same result; O(n) time and memory, no recursion. */
function runBlockOptIter(xs: JStat[]): JStat[] {
  const out: JStat[] = [];
  const n = xs.length;
  let i = 0;
  let pending: JStat[] = [];
  const at = (k: number): JStat | undefined => (k < pending.length ? pending[k] : xs[i + (k - pending.length)]);
  const consume = (k: number): void => {
    if (k <= pending.length) pending = pending.slice(k);
    else {
      i += k - pending.length;
      pending = [];
    }
  };
  for (;;) {
    const op1 = at(0);
    if (op1 === undefined) break;
    const op2 = at(1);

    if (op1.tag === "ReturnStat") {
      // deadCodeElim: drop everything after a return (see Note [Unsafe
      // JavaScript optimizations]) - the rest of `pending` and of `xs`.
      out.push(jsOptimizeStat(op1));
      return out;
    }

    const rewrite = tryDeclareAssign(op1, op2) ?? tryCombineOps(op1, op2);
    if (rewrite !== undefined) {
      consume(rewrite.consumed);
      pending = [...rewrite.replacement, ...pending];
      continue;
    }

    out.push(jsOptimizeStat(op1));
    consume(1);
  }
  return out;
}

function jsOptimize_(stats: JStat[]): JStat[] {
  return runBlockOptIter(flattenBlocks(stats));
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

/**
   Catch modify and assign operators:
      case 1: i = i + 1; ==> ++i;
      case 2: i = i - 1; ==> --i;
      case 3: i = i + n; ==> i += n;
      case 4: i = i - n; ==> i -= n;
 */
function tryCombineOps(op1: JStat | undefined, op2: JStat | undefined): FrontRewrite | undefined {
  // var x = expr; return x; ==> return expr;
  if (op1?.tag === "DeclStat" && op1.value !== undefined && op2?.tag === "ReturnStat") {
    const declValue = op1.value, declIdent = op1.ident, ret = op2;
    if (ret.value.tag === "ValExpr" && ret.value.value.tag === "JVar" && ret.value.value.ident === declIdent) {
      return { consumed: 2, replacement: [{ tag: "ReturnStat", value: declValue }] };
    }
  }

  // x = expr; return x; ==> return expr;
  if (op1?.tag === "AssignStat" && op1.op === "AssignOp" && op1.lhs.tag === "ValExpr" && op1.lhs.value.tag === "JVar" && op2?.tag === "ReturnStat") {
    const assignIdent = op1.lhs.value.ident, assignRhs = op1.rhs, ret = op2;
    if (ret.value.tag === "ValExpr" && ret.value.value.tag === "JVar" && ret.value.value.ident === assignIdent) {
      return { consumed: 2, replacement: [{ tag: "ReturnStat", value: assignRhs }] };
    }
  }

  // h$sp -= 2; h$sp += 5; ==> h$sp += 3;
  if (op1 && op2) {
    const s1 = isStackAdjust(op1), s2 = isStackAdjust(op2);
    if (s1 !== undefined && s2 !== undefined) return { consumed: 2, replacement: mkStackAdjust(s1 + s2) };
  }

  // x = x + 1; ==> ++x;  x = x - 1; ==> --x;  x = x + n; ==> x += n;  x = x - n; ==> x -= n;
  if (op1?.tag === "AssignStat" && op1.op === "AssignOp" && op1.lhs.tag === "ValExpr" && op1.lhs.value.tag === "JVar" && op1.rhs.tag === "InfixExpr") {
    const ident = op1.lhs, i = op1.lhs.value.ident, rhs = op1.rhs;
    const isVar = (e: JExpr, name: string): boolean => e.tag === "ValExpr" && e.value.tag === "JVar" && e.value.ident === name;
    const isOne = (e: JExpr): boolean => e.tag === "ValExpr" && e.value.tag === "JInt" && e.value.value === 1n;
    if (isVar(rhs.left, i)) {
      if (rhs.op === "AddOp" && isOne(rhs.right)) return { consumed: 1, replacement: [{ tag: "UOpStat", op: "PreIncOp", value: ident }] };
      if (rhs.op === "SubOp" && isOne(rhs.right)) return { consumed: 1, replacement: [{ tag: "UOpStat", op: "PreDecOp", value: ident }] };
      if (rhs.op === "AddOp") return { consumed: 1, replacement: [{ tag: "AssignStat", lhs: ident, op: "AddAssignOp", rhs: rhs.right }] };
      if (rhs.op === "SubOp") return { consumed: 1, replacement: [{ tag: "AssignStat", lhs: ident, op: "SubAssignOp", rhs: rhs.right }] };
    } else if (isVar(rhs.right, i)) {
      // commutative cases
      if (rhs.op === "AddOp" && isOne(rhs.left)) return { consumed: 1, replacement: [{ tag: "UOpStat", op: "PreIncOp", value: ident }] };
      if (rhs.op === "AddOp") return { consumed: 1, replacement: [{ tag: "AssignStat", lhs: ident, op: "AddAssignOp", rhs: rhs.left }] };
    }
  }

  return undefined;
}

/** Catch 'var i; i = q;' ==> 'var i = q;' */
function tryDeclareAssign(a: JStat | undefined, b: JStat | undefined): FrontRewrite | undefined {
  if (a?.tag === "DeclStat" && a.value === undefined && b?.tag === "AssignStat" && b.op === "AssignOp" && b.lhs.tag === "ValExpr" && b.lhs.value.tag === "JVar" && b.lhs.value.ident === a.ident) {
    return { consumed: 2, replacement: [{ tag: "DeclStat", ident: a.ident, value: b.rhs }] };
  }
  return undefined;
}

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
