/** Port of GHC.JS.Make: helper functions that make the GHC.JS.JStg.Syntax
 * EDSL ergonomic to build. Two kinds of helpers, exactly as the Haskell
 * module describes: introduction functions that inject Haskell/TS values
 * into the EDSL (jString, jVar, jFor, ...), and combinators that build new
 * EDSL terms out of existing ones (|=, if_, math_cos, ...).
 *
 * Haskell's ToJExpr/ToStat/JVarMagic/JSArgument type classes are resolved at
 * compile time by the type checker, including ten separate JSArgument tuple
 * instances so `jFunction`/`jVar` etc. can be polymorphic over arity.
 * TypeScript has no type-directed dispatch, so:
 *   - toJExpr/toStat below are ordinary runtime functions over the handful of
 *     shapes GHC actually instantiates them at (see their doc comments);
 *   - the ten JSArgument tuple instances collapse into one implementation
 *     parameterized by an explicit arity number and an array of fresh
 *     JStgExpr's, since TS arrays are already "any arity" - jFunction,
 *     jFunctionSized, jVar/jVars, jLam and jTryCatchFinally all take the
 *     arity (or tuple size) as an explicit number instead of an inferred one.
 */
import type { Ident } from "./ident.js";
import { name } from "./ident.js";
import type { JStgStat, JStgExpr, JVal, Op, UOp } from "./jstg-syntax.js";
import { global } from "./jstg-syntax.js";
import { mconcatJStgStat, memptyJStgStat } from "./jstg-syntax.js";
import type { JSM } from "./jstg-monad.js";
import { identsE } from "./transform.js";

// --------------------------------------------------------------------------
//                         Introduction functions
// --------------------------------------------------------------------------

/** GHC.JS.Make.ToJExpr, collapsed to a single runtime function since TS has
 * no type-directed instance resolution. Handles the shapes GHC actually
 * marshals through toJExpr: JStgExpr/JVal (identity), arrays (JList),
 * booleans (as the `true`/`false` globals, matching the Bool instance
 * exactly), and Idents (as JVar). Numbers and strings are deliberately NOT
 * overloaded here (unlike Int/Integer/Double/Char/FastString's instances) -
 * the type-level distinction between an int, a double, a char and a string
 * has no runtime signal in TS, so callers should reach for jInt/jDouble/
 * jString/name directly instead of relying on toJExpr to guess. */
export function toJExpr(x: JStgExpr | JVal | boolean | Ident | Array<JStgExpr | JVal | boolean | Ident>): JStgExpr {
  if (Array.isArray(x)) return { tag: "ValExpr", value: { tag: "JList", values: x.map(toJExpr) } };
  if (typeof x === "boolean") return x ? global("true") : global("false");
  if (typeof x === "string") return { tag: "ValExpr", value: { tag: "JVar", ident: x } };
  if ("tag" in x && (x.tag === "ValExpr" || x.tag === "SelExpr" || x.tag === "IdxExpr" || x.tag === "InfixExpr" || x.tag === "UOpExpr" || x.tag === "IfExpr" || x.tag === "ApplExpr" || x.tag === "RawExpr")) return x;
  return { tag: "ValExpr", value: x };
}

export const jInt = (n: bigint | number): JStgExpr => ({ tag: "ValExpr", value: { tag: "JInt", value: BigInt(n) } });
export const jDouble = (n: number): JStgExpr => ({ tag: "ValExpr", value: { tag: "JDouble", value: n } });

/** Convert a string to a Javascript String - GHC.JS.Make.jString. */
export const jString = (s: string): JStgExpr => ({ tag: "ValExpr", value: { tag: "JStr", value: s } });

/** GHC.JS.Make.ToStat, collapsed the same way as ToJExpr. */
export function toStat(x: JStgStat | JStgExpr | JStgStat[] | JStgExpr[]): JStgStat {
  if (Array.isArray(x)) {
    if (x.length > 0 && "tag" in x[0] && isStatTag(x[0].tag)) return { tag: "BlockStat", stats: (x as JStgStat[]) };
    return { tag: "BlockStat", stats: (x as JStgExpr[]).map(expr2stat) };
  }
  return isStatTag(x.tag) ? (x as JStgStat) : expr2stat(x as JStgExpr);
}
const STAT_TAGS = new Set(["DeclStat", "ReturnStat", "IfStat", "WhileStat", "ForStat", "ForInStat", "SwitchStat", "TryStat", "BlockStat", "ApplStat", "UOpStat", "AssignStat", "LabelStat", "BreakStat", "ContinueStat", "FuncStat", "RawStat"]);
const isStatTag = (tag: string): boolean => STAT_TAGS.has(tag);

/** Convert a JS expression to a JS statement where applicable - only affects
 * application, if-expressions and unary expressions. */
export function expr2stat(e: JStgExpr): JStgStat {
  if (e.tag === "ApplExpr") return { tag: "ApplStat", fn: e.fn, args: e.args };
  if (e.tag === "IfExpr") return { tag: "IfStat", cond: e.cond, then: expr2stat(e.then), else: expr2stat(e.else) };
  if (e.tag === "UOpExpr") return { tag: "UOpStat", op: e.op, value: e.value };
  return nullStat;
}

/** construct a js declaration with the given identifier */
export const decl = (i: Ident): JStgStat => ({ tag: "DeclStat", ident: i });

/** Create a new anonymous function - GHC.JS.Make.jLam. */
export function jLam(js: JSM, arity: number, body: (args: JStgExpr[]) => JStgStat): JStgExpr {
  const argIdents = Array.from({ length: arity }, () => js.newIdent());
  const args = argIdents.map((i): JStgExpr => ({ tag: "ValExpr", value: { tag: "JVar", ident: i } }));
  return { tag: "ValExpr", value: { tag: "JFunc", args: argIdents, body: body(args) } };
}

/** Special case of jLam where the function needs no fresh arguments. */
export const jLam2 = (body: JStgStat): JStgExpr => ({ tag: "ValExpr", value: { tag: "JFunc", args: [], body } });

/** Introduce one new variable into scope for the duration of the enclosed
 * statement - GHC.JS.Make.jVar. */
export function jVar(js: JSM, body: (v: JStgExpr) => JStgStat): JStgStat {
  return jVars(js, 1, ([v]) => body(v));
}

/** Introduce `arity` new variables into scope for the duration of the
 * enclosed statement - GHC.JS.Make.jVars, generalized over an explicit arity
 * instead of Haskell's JSArgument tuple-size dispatch. */
export function jVars(js: JSM, arity: number, body: (vs: JStgExpr[]) => JStgStat): JStgStat {
  const idents = Array.from({ length: arity }, () => js.newIdent());
  const vs = idents.map((i): JStgExpr => ({ tag: "ValExpr", value: { tag: "JVar", ident: i } }));
  return mconcatJStgStat([...idents.map(decl), body(vs)]);
}

/** Construct a top-level function subject to JS hoisting - GHC.JS.Make.
 * jFunction (jFunctionSized collapses to the same implementation in TS,
 * since both just need an explicit arity here). */
export function jFunction(js: JSM, ident: Ident, arity: number, body: (args: JStgExpr[]) => JStgStat): JStgStat {
  const argIdents = Array.from({ length: arity }, () => js.newIdent());
  const args = argIdents.map((i): JStgExpr => ({ tag: "ValExpr", value: { tag: "JVar", ident: i } }));
  return { tag: "FuncStat", ident, args: argIdents, body: body(args) };
}
export const jFunctionSized = jFunction;

/** Construct a top-level function that binds no parameters. */
export const jFunction_ = (ident: Ident, body: JStgStat): JStgStat => ({ tag: "FuncStat", ident, args: [], body });

/** GHC.JS.Make.jBlock :: Monoid a => [JSM a] -> JSM a. TS has no monadic
 * sequencing to mirror (there is nothing to run), so callers just build the
 * list of statements directly and pass it here to fold with mconcat. */
export const jBlock = (stats: JStgStat[]): JStgStat => mconcatJStgStat(stats);

/** Create a 'for in' statement - GHC.JS.Make.jForIn. */
export function jForIn(js: JSM, e: JStgExpr, f: (v: JStgExpr) => JStgStat): JStgStat {
  const i = js.newIdent();
  return mconcatJStgStat([decl(i), { tag: "ForInStat", isEach: false, ident: i, obj: e, body: f({ tag: "ValExpr", value: { tag: "JVar", ident: i } }) }]);
}

/** As with jForIn but creating a "for each in" statement. */
export function jForEachIn(js: JSM, e: JStgExpr, f: (v: JStgExpr) => JStgStat): JStgStat {
  const i = js.newIdent();
  return mconcatJStgStat([decl(i), { tag: "ForInStat", isEach: true, ident: i, obj: e, body: f({ tag: "ValExpr", value: { tag: "JVar", ident: i } }) }]);
}

/** Create a 'for' statement given init/predicate/step/body over a fresh
 * counter - GHC.JS.Make.jFor. */
export function jFor(
  js: JSM,
  init: (i: JStgExpr) => JStgStat,
  pred: (i: JStgExpr) => JStgExpr,
  step: (i: JStgExpr) => JStgStat,
  body: (i: JStgExpr) => JStgStat,
): JStgStat {
  const id = js.newIdent();
  const i: JStgExpr = { tag: "ValExpr", value: { tag: "JVar", ident: id } };
  return mconcatJStgStat([decl(id), { tag: "ForStat", init: init(i), cond: pred(i), step: step(i), body: body(i) }]);
}

/** GHC.JS.Make.jTryCatchFinally. */
export function jTryCatchFinally(js: JSM, c: (i: Ident) => JStgStat, f: (i: Ident) => JStgStat, f2: (i: Ident) => JStgStat): JStgStat {
  const i = js.newIdent();
  return { tag: "TryStat", body: c(i), ident: i, catch: f(i), finally: f2(i) };
}

/** The empty JS HashMap - GHC.JS.Make.jhEmpty et al. Represented as an
 * ordered array of entries rather than Haskell's Data.Map, since JHash itself
 * is an association list (see jstg-syntax.ts). */
export const jhEmpty = (): Array<[string, JStgExpr]> => [];
export const jhSingle = (k: string, v: JStgExpr): Array<[string, JStgExpr]> => jhAdd(k, v, jhEmpty());
export function jhAdd(k: string, v: JStgExpr, m: Array<[string, JStgExpr]>): Array<[string, JStgExpr]> {
  return [...m.filter(([k2]) => k2 !== k), [k, v]];
}
export const jhFromList = (entries: Array<[string, JStgExpr]>): JVal => ({ tag: "JHash", entries });

/** The empty JS statement. */
export const nullStat: JStgStat = memptyJStgStat;

// --------------------------------------------------------------------------
//                              Combinators
// --------------------------------------------------------------------------

const infix = (op: Op) => (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op, left: x, right: y });

/** JS infix equality operators: .==. .===. .!=. .!==. */
export const eq_ = infix("EqOp");
export const strictEq_ = infix("StrictEqOp");
export const neq_ = infix("NeqOp");
export const strictNeq_ = infix("StrictNeqOp");

/** JS infix ord operators: .>. .>=. .<. .<=. */
export const gt_ = infix("GtOp");
export const ge_ = infix("GeOp");
export const lt_ = infix("LtOp");
export const le_ = infix("LeOp");

/** JS infix bit operators: .|. .||. .&&. */
export const bor_ = infix("BOrOp");
export const lor_ = infix("LOrOp");
export const land_ = infix("LAndOp");

/** JS infix bit shift operators: .<<. .>>. .>>>. */
export const shl_ = infix("LeftShiftOp");
export const shr_ = infix("RightShiftOp");
export const ushr_ = infix("ZRightShiftOp");

/** Given a JStgExpr, return its type - GHC.JS.Make.typeOf. */
export const typeOf = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "TypeofOp", value: x });

/** JS if-expression: if_ e1 e2 e3 ==> e1 ? e2 : e3 */
export const if_ = (cond: JStgExpr, then: JStgExpr, els: JStgExpr): JStgExpr => ({ tag: "IfExpr", cond, then, else: els });

/** If-expression which returns statements: ifS e s1 s2 ==> if(e){s1}else{s2} */
export const ifS = (cond: JStgExpr, then: JStgStat, els: JStgStat): JStgStat => ({ tag: "IfStat", cond, then, else: els });

/** Version of a JS if-expression which admits computed branches. */
export const jIf = (cond: JStgExpr, a: JStgStat, b: JStgStat): JStgStat => ({ tag: "IfStat", cond, then: a, else: b });

/** A when-statement as sugar via ifS: jwhenS cond block ==> if(cond){block}else{} */
export const jwhenS = (cond: JStgExpr, block: JStgStat): JStgStat => ({ tag: "IfStat", cond, then: block, else: memptyJStgStat });

/** If-expression which returns blocks: ifBlockS e s1 s2 ==> if(e){s1}else{s2} */
export const ifBlockS = (cond: JStgExpr, s1: JStgStat[], s2: JStgStat[]): JStgStat => ({ tag: "IfStat", cond, then: mconcatJStgStat(s1), else: mconcatJStgStat(s2) });

/** if-expression that returns 1 if condition holds, 0 otherwise: e ? 1 : 0 */
export const if10 = (e: JStgExpr): JStgExpr => ({ tag: "IfExpr", cond: e, then: one_, else: zero_ });

/** if-expression that returns 0 if condition holds, 1 otherwise: e ? 0 : 1 */
export const if01 = (e: JStgExpr): JStgExpr => ({ tag: "IfExpr", cond: e, then: zero_, else: one_ });

/** an application expression, see related appS: app f xs ==> f(xs) */
export const app = (f: string, xs: JStgExpr[]): JStgExpr => ({ tag: "ApplExpr", fn: global(f), args: xs });

/** A statement application, see the expression form app. */
export const appS = (f: string, xs: JStgExpr[]): JStgStat => ({ tag: "ApplStat", fn: global(f), args: xs });

/** Return a JStgExpr. */
export const returnS = (e: JStgExpr): JStgStat => ({ tag: "ReturnStat", value: e });

/** "for" loop with increment at end of body - GHC.JS.Make.loop. */
export function loop_(js: JSM, initial: JStgExpr, test: (i: JStgExpr) => JStgExpr, body: (i: JStgExpr) => JStgStat): JStgStat {
  return jVar(js, (i) => mconcatJStgStat([assign_(i, initial), { tag: "WhileStat", isDo: false, cond: test(i), body: body(i) }]));
}

/** "for" loop, block-statement flavor - GHC.JS.Make.loopBlockS. */
export function loopBlockS(js: JSM, initial: JStgExpr, test: (i: JStgExpr) => JStgExpr, body: (i: JStgExpr) => JStgStat[]): JStgStat {
  return jVar(js, (i) => mconcatJStgStat([assign_(i, initial), { tag: "WhileStat", isDo: false, cond: test(i), body: mconcatJStgStat(body(i)) }]));
}

/** Prefix/postfix increment/decrement a JStgExpr. */
export const preIncrS = (x: JStgExpr): JStgStat => ({ tag: "UOpStat", op: "PreIncOp", value: x });
export const postIncrS = (x: JStgExpr): JStgStat => ({ tag: "UOpStat", op: "PostIncOp", value: x });
export const preDecrS = (x: JStgExpr): JStgStat => ({ tag: "UOpStat", op: "PreDecOp", value: x });
export const postDecrS = (x: JStgExpr): JStgStat => ({ tag: "UOpStat", op: "PostDecOp", value: x });

/** Byte indexing with a 64/32/16/8-bit offset. */
export const off64 = (o: JStgExpr, i: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "AddOp", left: o, right: shl_(i, three_) });
export const off32 = (o: JStgExpr, i: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "AddOp", left: o, right: shl_(i, two_) });
export const off16 = (o: JStgExpr, i: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "AddOp", left: o, right: shl_(i, one_) });
export const off8 = (o: JStgExpr, i: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "AddOp", left: o, right: i });

/** a bit mask to retrieve the lower 8/16 bits. */
export const mask8 = (x: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "BAndOp", left: x, right: jInt(0xff) });
export const mask16 = (x: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "BAndOp", left: x, right: jInt(0xffff) });

/** Sign-extend/narrow an 8/16-bit value. */
export const signExtend8 = (x: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "SubOp", left: { tag: "InfixExpr", op: "BAndOp", left: x, right: jInt(0x7f) }, right: { tag: "InfixExpr", op: "BAndOp", left: x, right: jInt(0x80) } });
export const signExtend16 = (x: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "SubOp", left: { tag: "InfixExpr", op: "BAndOp", left: x, right: jInt(0x7fff) }, right: { tag: "InfixExpr", op: "BAndOp", left: x, right: jInt(0x8000) } });

/** Select a property from an object: obj .^ prop ==> obj.prop */
export const sel_ = (obj: JStgExpr, prop: string): JStgExpr => ({ tag: "SelExpr", obj, field: name(prop) });

/** Assign a variable to an expression: foo |= expr ==> foo = expr; */
export const assign_ = (l: JStgExpr, r: JStgExpr): JStgStat => ({ tag: "AssignStat", lhs: l, op: "AssignOp", rhs: r });

/** Declare a variable and assign it: i ||= expr ==> var i = expr; */
export const declAssign_ = (i: Ident, e: JStgExpr): JStgStat => ({ tag: "DeclStat", ident: i, value: e });

/** return the expression at idx of obj: obj .! idx ==> obj[idx] */
export const idx_ = (obj: JStgExpr, i: JStgExpr): JStgExpr => ({ tag: "IdxExpr", obj, index: i });

export function assignAllEqual(xs: JStgExpr[], ys: JStgExpr[]): JStgStat {
  if (xs.length !== ys.length) throw new Error("assignAllEqual: lists of different lengths");
  return mconcatJStgStat(xs.map((x, n) => assign_(x, ys[n])));
}
export function assignAll(xs: JStgExpr[], ys: JStgExpr[]): JStgStat {
  const n = Math.min(xs.length, ys.length);
  return mconcatJStgStat(Array.from({ length: n }, (_, k) => assign_(xs[k], ys[k])));
}
export function assignAllReverseOrder(xs: JStgExpr[], ys: JStgExpr[]): JStgStat {
  const n = Math.min(xs.length, ys.length);
  return mconcatJStgStat(Array.from({ length: n }, (_, k) => assign_(xs[k], ys[k])).reverse());
}
export function declAssignAll(xs: Ident[], ys: JStgExpr[]): JStgStat {
  const n = Math.min(xs.length, ys.length);
  return mconcatJStgStat(Array.from({ length: n }, (_, k) => declAssign_(xs[k], ys[k])));
}

// --------------------------------------------------------------------------
//                                Literals
// --------------------------------------------------------------------------

export const null_: JStgExpr = global("null");
export const undefined_: JStgExpr = global("undefined");
export const zero_: JStgExpr = jInt(0);
export const one_: JStgExpr = jInt(1);
export const two_: JStgExpr = jInt(2);
export const three_: JStgExpr = jInt(3);
export const true_: JStgExpr = { tag: "ValExpr", value: { tag: "JBool", value: true } };
export const false_: JStgExpr = { tag: "ValExpr", value: { tag: "JBool", value: false } };

export const returnStack: JStgStat = { tag: "ReturnStat", value: { tag: "ApplExpr", fn: global("h$rs"), args: [] } };

// --------------------------------------------------------------------------
//                             Math functions
// --------------------------------------------------------------------------

const math: JStgExpr = global("Math");
const math_ = (op: string) => (args: JStgExpr[]): JStgExpr => ({ tag: "ApplExpr", fn: sel_(math, op), args });

export const math_log = math_("log");
export const math_sin = math_("sin");
export const math_cos = math_("cos");
export const math_tan = math_("tan");
export const math_exp = math_("exp");
export const math_acos = math_("acos");
export const math_asin = math_("asin");
export const math_atan = math_("atan");
export const math_abs = math_("abs");
export const math_pow = math_("pow");
export const math_sign = math_("sign");
export const math_sqrt = math_("sqrt");
export const math_asinh = math_("asinh");
export const math_acosh = math_("acosh");
export const math_atanh = math_("atanh");
export const math_sinh = math_("sinh");
export const math_cosh = math_("cosh");
export const math_tanh = math_("tanh");
export const math_expm1 = math_("expm1");
export const math_log1p = math_("log1p");
export const math_fround = math_("fround");
export const math_min = math_("min");
export const math_max = math_("max");

/** GHC.JS.Make's Num/Fractional instances for JStgExpr. */
export const jAdd = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "AddOp", left: x, right: y });
export const jSub = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "SubOp", left: x, right: y });
export const jMul = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "MulOp", left: x, right: y });
export const jDiv = (x: JStgExpr, y: JStgExpr): JStgExpr => ({ tag: "InfixExpr", op: "DivOp", left: x, right: y });
export const jAbs = (x: JStgExpr): JStgExpr => math_abs([x]);
export const jNegate = (x: JStgExpr): JStgExpr => ({ tag: "UOpExpr", op: "NegOp", value: x });
export const jSignum = (x: JStgExpr): JStgExpr => math_sign([x]);

// re-exported for convenience since Make.hs's JSArgument.argList is just
// identsE over the already-built fresh JStgExpr's
export { identsE };
