/** Port of GHC.StgToJS.Literal.
 *
 * Literals represented with 2 values:
 *  * Addr# (Null and Strings): array and offset
 *  * 64-bit values: high 32-bit, low 32-bit
 *  * labels: call to h$mkFunctionPtr and 0, or function name and 0
 */
import type { JStgExpr } from "../js/jstg-syntax.js";
import { Int, Var, global } from "../js/jstg-syntax.js";
import { jInt, jDouble, jString, null_, toJExpr, ushr_, app, zero_ } from "../js/make.js";
import type { Literal } from "../stg.js";
import { hdStrStr, hdRawStr } from "./symbols.js";
import type { GenState } from "./monad.js";
import { emitStatic } from "./monad.js";
import { freshIdent } from "./ids.js";

/** GHC.StgToJS.Symbols.mkRawSymbol. */
export function mkRawSymbol(exported: boolean, s: string): string {
  return (exported ? "h$" : "h$$") + s;
}

/** A static literal value - GHC.StgToJS.Types.StaticLit. Types.hs's
 * Core-facing half was left unported (see types.ts's header); the static
 * vocabulary lives here and in arg.ts, with its producers. */
export type StaticLit =
  | { tag: "BoolLit"; value: boolean }
  | { tag: "IntLit"; value: bigint }
  | { tag: "NullLit" }
  | { tag: "DoubleLit"; value: number }
  | { tag: "StringLit"; value: string }
  | { tag: "BinLit"; value: Uint8Array }
  /** is function pointer, label (also used for string / binary init) */
  | { tag: "LabelLit"; isFun: boolean; label: string };

/** Static Arguments: things that are statically allocated, i.e. they exist at
 * program startup - static heap objects, literals, or things GHC floated to a
 * top level binding. */
export type StaticArg =
  /** reference to a heap object */
  | { tag: "StaticObjArg"; name: string }
  | { tag: "StaticLitArg"; lit: StaticLit }
  /** unfloated constructor */
  | { tag: "StaticConArg"; name: string; args: StaticArg[] };

/** unboxed constructor (Bool, Int, Double etc) */
export type StaticUnboxed =
  | { tag: "StaticUnboxedBool"; value: boolean }
  | { tag: "StaticUnboxedInt"; value: bigint }
  | { tag: "StaticUnboxedDouble"; value: number }
  | { tag: "StaticUnboxedString"; value: string }
  | { tag: "StaticUnboxedStringOffset"; value: string };

export type StaticVal =
  /** heap object for function */
  | { tag: "StaticFun"; name: string; args: StaticArg[] }
  /** heap object for CAF; absent field means the thunk is initialized in an
   * alternative way, like string thunks through h$str */
  | { tag: "StaticThunk"; init?: { name: string; args: StaticArg[] } }
  | { tag: "StaticUnboxed"; value: StaticUnboxed }
  /** regular datacon app */
  | { tag: "StaticData"; name: string; args: StaticArg[] }
  /** list initializer (with optional tail) */
  | { tag: "StaticList"; args: StaticArg[]; tail?: string };

/** `instance ToJExpr StaticLit`. */
export function staticLitToJExpr(l: StaticLit): JStgExpr {
  switch (l.tag) {
    case "BoolLit":
      // `toJExpr (b :: Bool)` is the `true`/`false` *global*, not a JBool.
      return toJExpr(l.value);
    case "IntLit":
      return jInt(l.value);
    case "NullLit":
      return null_;
    case "DoubleLit":
      return jDouble(l.value);
    case "StringLit":
      return app(hdStrStr, [jString(l.value)]);
    case "BinLit":
      return app(hdRawStr, [{ tag: "ValExpr", value: { tag: "JList", values: Array.from(l.value, (b) => jInt(b)) } }]);
    case "LabelLit":
      return global(l.label);
  }
}

/** Generate JS expressions for a Literal. */
export function genLit(gs: GenState, l: Literal): JStgExpr[] {
  switch (l.tag) {
    case "LitChar":
      return [jInt(ord(l.value))];
    case "LitString": {
      const strLit = freshIdent(gs);
      const strOff = freshIdent(gs);
      emitStatic(gs, strLit, { tag: "StaticUnboxed", value: { tag: "StaticUnboxedString", value: l.value } });
      emitStatic(gs, strOff, { tag: "StaticUnboxed", value: { tag: "StaticUnboxedStringOffset", value: l.value } });
      return [Var(strLit), Var(strOff)];
    }
    case "LitNullAddr":
      return [null_, Int(0)];
    case "LitNumInt":
    case "LitNumInt8":
    case "LitNumInt16":
    case "LitNumInt32":
      return [jInt(l.value)];
    case "LitNumInt64":
      return [jInt(l.value >> 32n), toU32Expr(l.value)];
    case "LitNumWord":
    case "LitNumWord8":
    case "LitNumWord16":
    case "LitNumWord32":
      return [toU32Expr(l.value)];
    case "LitNumWord64":
      return [toU32Expr(l.value >> 32n), toU32Expr(l.value)];
    case "LitFloat":
      return [jDouble(r2f(l.value))];
    case "LitDouble":
      return [jDouble(l.value)];
    case "LitLabel":
      // GHC branches on the literal's FunctionOrData flag, emitting
      // h$mkFunctionPtr for IsFunction. stg.ts's LitLabel carries no such
      // flag, so only the data form is reachable here.
      return [global(mkRawSymbol(true, l.name)), Int(0)];
  }
}

/** generate a literal for the static init tables */
export function genStaticLit(l: Literal): StaticLit[] {
  switch (l.tag) {
    case "LitChar":
      return [intLit(BigInt(ord(l.value)))];
    case "LitString":
      return [{ tag: "StringLit", value: l.value }, intLit(0n)];
    case "LitNullAddr":
      return [{ tag: "NullLit" }, intLit(0n)];
    case "LitNumInt":
    case "LitNumInt8":
    case "LitNumInt16":
    case "LitNumInt32":
      return [intLit(l.value)];
    case "LitNumInt64":
      return [intLit(l.value >> 32n), toU32Lit(l.value)];
    case "LitNumWord":
    case "LitNumWord8":
    case "LitNumWord16":
    case "LitNumWord32":
      return [toU32Lit(l.value)];
    case "LitNumWord64":
      return [toU32Lit(l.value >> 32n), toU32Lit(l.value)];
    case "LitFloat":
      return [{ tag: "DoubleLit", value: r2f(l.value) }];
    case "LitDouble":
      return [{ tag: "DoubleLit", value: l.value }];
    case "LitLabel":
      // see genLit's LitLabel: no FunctionOrData flag to pass on.
      return [{ tag: "LabelLit", isFun: false, label: mkRawSymbol(true, l.name) }, intLit(0n)];
  }
}

const intLit = (value: bigint): StaticLit => ({ tag: "IntLit", value });

/** make an unsigned 32 bit number from this unsigned one, lower 32 bits */
function toU32Expr(i: bigint): JStgExpr {
  return ushr_(Int(i & 0xffffffffn), zero_);
}

/** make an unsigned 32 bit number from this unsigned one, lower 32 bits */
function toU32Lit(i: bigint): StaticLit {
  return intLit(i & 0xffffffffn);
}

/** r2f = float2Double . realToFrac: round to single precision, then widen. */
const r2f = (r: number): number => Math.fround(r);

function ord(c: string): number {
  const cp = c.codePointAt(0);
  if (cp === undefined) throw new Error("genLit: empty LitChar");
  return cp;
}
