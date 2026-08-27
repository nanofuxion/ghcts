/** Port of GHC.JS.Opt.Expr: a simple expression optimizer performing constant
 * folding and some boolean-expression optimizations. Intended to run after
 * GHC.JS.Opt.Simple (opt-simple.ts), which eliminates redundant assignments
 * and produces expressions this can fold more effectively. */
import type { JStat, JExpr, JVal, Op } from "./syntax.js";

export function optExprs(s: JStat): JStat {
  const go = (s: JStat): JStat => {
    switch (s.tag) {
      case "DeclStat": return { ...s, value: s.value && opt(s.value) };
      case "AssignStat": return { ...s, lhs: opt(s.lhs), rhs: opt(s.rhs) };
      case "ReturnStat": return { ...s, value: opt(s.value) };
      case "BlockStat": return { ...s, stats: s.stats.map(go) };
      case "IfStat": return { ...s, cond: optCond(s.cond), then: go(s.then), else: go(s.else) };
      case "WhileStat": return { ...s, cond: optCond(s.cond), body: go(s.body) };
      case "ForStat": return { ...s, init: go(s.init), cond: optCond(s.cond), step: go(s.step), body: go(s.body) };
      case "ForInStat": return { ...s, obj: opt(s.obj), body: go(s.body) };
      case "SwitchStat": return { ...s, scrut: opt(s.scrut), cases: s.cases.map(([c, cs]): [JExpr, JStat] => [c, go(cs)]), default: go(s.default) };
      case "TryStat": return { ...s, body: go(s.body), catch: go(s.catch), finally: go(s.finally) };
      case "ApplStat": return { ...s, fn: opt(s.fn), args: s.args.map(opt) };
      case "UOpStat": return { ...s, value: opt(s.value) };
      case "LabelStat": return { ...s, body: go(s.body) };
      case "BreakStat": case "ContinueStat": case "RawStat": return s;
      case "FuncStat": return { ...s, body: go(s.body) };
      case "ThrowStat": return { ...s, value: opt(s.value) };
    }
  };
  return go(s);
}

/** remove double negation if we're using the expression in a loop/if condition */
export function optCond(e: JExpr): JExpr {
  let f = opt(e);
  while (f.tag === "UOpExpr" && f.op === "NotOp" && f.value.tag === "UOpExpr" && f.value.op === "NotOp") {
    f = f.value.value;
  }
  return f;
}

export function opt(e: JExpr): JExpr {
  switch (e.tag) {
    case "ValExpr": return e;
    case "SelExpr": return { ...e, obj: opt(e.obj) };
    case "IdxExpr": return { ...e, obj: opt(e.obj), index: opt(e.index) };
    case "InfixExpr": {
      // ((c_e ? 1 : 0) === 1)   ==> !!c_e
      // ((c_e ? 1 : 0) === 0)   ==> !c_e
      if (e.op === "StrictEqOp" && e.left.tag === "IfExpr") {
        const c_e = e.left.cond;
        const t_e = opt(e.left.then), f_e = opt(e.left.else), rhs = opt(e.right);
        if (t_e.tag === "ValExpr" && rhs.tag === "ValExpr" && eqVal(t_e.value, rhs.value)) {
          return { tag: "UOpExpr", op: "NotOp", value: { tag: "UOpExpr", op: "NotOp", value: c_e } };
        }
        if (f_e.tag === "ValExpr" && rhs.tag === "ValExpr" && eqVal(f_e.value, rhs.value)) {
          return { tag: "UOpExpr", op: "NotOp", value: opt(c_e) };
        }
        return { tag: "InfixExpr", op: "StrictEqOp", left: { tag: "IfExpr", cond: c_e, then: t_e, else: f_e }, right: rhs };
      }
      // (1 === (c_e ? 1 : 0))   ==> !!c_e
      // (0 === (c_e ? 1 : 0))   ==> !c_e
      if (e.op === "StrictEqOp" && e.right.tag === "IfExpr") {
        const lhs = opt(e.left);
        const c_e = opt(e.right.cond), t_e = opt(e.right.then), f_e = opt(e.right.else);
        if (t_e.tag === "ValExpr" && lhs.tag === "ValExpr" && eqVal(t_e.value, lhs.value)) {
          return { tag: "UOpExpr", op: "NotOp", value: { tag: "UOpExpr", op: "NotOp", value: c_e } };
        }
        if (f_e.tag === "ValExpr" && lhs.tag === "ValExpr" && eqVal(f_e.value, lhs.value)) {
          return { tag: "UOpExpr", op: "NotOp", value: c_e };
        }
        return { tag: "InfixExpr", op: "StrictEqOp", left: lhs, right: { tag: "IfExpr", cond: c_e, then: t_e, else: f_e } };
      }
      const e1 = opt(e.left), e2 = opt(e.right);
      if (e1.tag === "ValExpr" && e1.value.tag === "JInt" && e2.tag === "ValExpr" && e2.value.tag === "JInt") {
        const v = optInt(e.op, e1.value.value, e2.value.value);
        if (v !== undefined) return { tag: "ValExpr", value: v };
      }
      if (e1.tag === "ValExpr" && e1.value.tag === "JBool" && e2.tag === "ValExpr" && e2.value.tag === "JBool") {
        const v = optBool(e.op, e1.value.value, e2.value.value);
        if (v !== undefined) return { tag: "ValExpr", value: v };
      }
      return { ...e, left: e1, right: e2 };
    }
    case "UOpExpr": return { ...e, value: opt(e.value) };
    case "IfExpr": return { ...e, cond: optCond(e.cond), then: opt(e.then), else: opt(e.else) };
    case "ApplExpr": return { ...e, fn: opt(e.fn), args: e.args.map(opt) };
    case "RawExpr": return e;
  }
}

/** Optimizations for operations on two known boolean values */
function optBool(op: Op, x: boolean, y: boolean): JVal | undefined {
  switch (op) {
    case "LAndOp": return { tag: "JBool", value: x && y };
    case "LOrOp": return { tag: "JBool", value: x || y };
    case "EqOp": case "StrictEqOp": return { tag: "JBool", value: x === y };
    case "NeqOp": case "StrictNeqOp": return { tag: "JBool", value: x !== y };
    default: return undefined;
  }
}

const MASK32 = 0xffffffffn;

/** JavaScript bitwise operations truncate numbers to 32 bit signed integers;
 * do the same when constant folding with this kind of operator. */
function truncOp(op: (a: number, b: number) => number, n: bigint, m: bigint): JVal {
  const a = Number(BigInt.asIntN(32, n)), b = Number(BigInt.asIntN(32, m));
  return { tag: "JInt", value: BigInt(op(a, b) | 0) };
}

function shiftOp(op: (a: number, b: number) => number, n: bigint, m: bigint): JVal {
  const a = Number(BigInt.asIntN(32, n)), b = Number(m & 0x1fn);
  return { tag: "JInt", value: BigInt(op(a, b) | 0) };
}

/** Optimizations for operations on two known integer values */
function optInt(op: Op, n: bigint, m: bigint): JVal | undefined {
  switch (op) {
    case "ZRightShiftOp": {
      const a = Number(n & MASK32), b = Number(m & 0x1fn);
      return { tag: "JInt", value: BigInt((a >>> b) >>> 0) };
    }
    case "BOrOp": return truncOp((a, b) => a | b, n, m);
    case "BAndOp": return truncOp((a, b) => a & b, n, m);
    case "BXorOp": return truncOp((a, b) => a ^ b, n, m);
    case "RightShiftOp": return shiftOp((a, b) => a >> b, n, m);
    case "LeftShiftOp": return shiftOp((a, b) => a << b, n, m);
    case "AddOp": return smallIntOp((a, b) => a + b, n, m);
    case "SubOp": return smallIntOp((a, b) => a - b, n, m);
    case "MulOp": return smallIntOp((a, b) => a * b, n, m);
    default: {
      const cmp = getCmpOp(op);
      if (cmp && isSmall52(n) && isSmall52(m)) return { tag: "JBool", value: cmp(n, m) };
      return undefined;
    }
  }
}

function smallIntOp(op: (a: bigint, b: bigint) => bigint, n: bigint, m: bigint): JVal | undefined {
  const r = op(n, m);
  return isSmall52(n) && isSmall52(m) && isSmall52(r) ? { tag: "JInt", value: r } : undefined;
}

function getCmpOp(op: Op): ((a: bigint, b: bigint) => boolean) | undefined {
  switch (op) {
    case "EqOp": case "StrictEqOp": return (a, b) => a === b;
    case "NeqOp": case "StrictNeqOp": return (a, b) => a !== b;
    case "GtOp": return (a, b) => a > b;
    case "GeOp": return (a, b) => a >= b;
    case "LtOp": return (a, b) => a < b;
    case "LeOp": return (a, b) => a <= b;
    default: return undefined;
  }
}

/** JavaScript numbers are IEEE 754 double precision floats, which have a
 * 52-bit mantissa; true if the integer is definitely representable without
 * loss of precision as a JavaScript number. */
function isSmall52(n: bigint): boolean {
  return n >= -0x10000000000000n && n <= 0xfffffffffffffn;
}

/** True if the values are definitely equal in JavaScript (e1 === e2 is not
 * always true even for syntactically-equal expressions: NaN, fresh arrays,
 * fresh function calls). */
function eqVal(a: JVal, b: JVal): boolean {
  if (a.tag === "JInt" && b.tag === "JInt") return a.value === b.value;
  if (a.tag === "JStr" && b.tag === "JStr") return a.value === b.value;
  if (a.tag === "JBool" && b.tag === "JBool") return a.value === b.value;
  if (a.tag === "JDouble" && b.tag === "JDouble") return !Number.isNaN(a.value) && !Number.isNaN(b.value) && a.value === b.value;
  return false;
}
