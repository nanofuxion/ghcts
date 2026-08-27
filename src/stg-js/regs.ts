/** Ported from GHC/StgToJS/Regs.hs (GHC 9.12.2).
 *
 * The JS backend's "registers": R1..R128, the stack pointer/array, and the
 * return registers used to smuggle extra results out of foreign calls.
 *
 * Two Haskell-isms have no TS counterpart and are handled as follows:
 *   - `data StgReg = R1 | ... | R128 deriving (Enum, Bounded, Ix)` becomes a
 *     bare `number` holding `fromEnum r` (so R1 = 0), which makes derived Ord
 *     and Ix fall out of plain arithmetic and array indexing.
 *   - `instance ToJExpr` cannot be expressed, so each instance becomes a named
 *     function: `register` (StgReg), `foreignRegister` (StgRet), and
 *     `specialToJExpr` (Special).
 */
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr } from "../js/jstg-syntax.js";
import { global } from "../js/jstg-syntax.js";
import { jInt, jSub, idx_ } from "../js/make.js";
import { hdRegs, hdStack, hdStackPtr } from "./symbols.js";
import { StgRet } from "./types.js";

export { StgRet };

/** General purpose "registers". Payload is `fromEnum r`, so R1 is 0.
 *
 * The JS backend arbitrarily supports 128 registers. */
export type StgReg = number;

/** `maxBound :: StgReg`, i.e. `fromEnum R128`. */
const maxBoundReg: StgReg = 127;

export const R1: StgReg = 0;
export const R2: StgReg = 1;
export const R3: StgReg = 2;
export const R4: StgReg = 3;

/** Stack registers */
export enum Special {
  Stack = 0,
  Sp = 1,
}

/** GHC.StgToJS.Symbols.hdStr - the "h$" prefix, computed rather than a literal
 * in Symbols.hs and so not among symbols.ts's generated exports. */
const hdStr = "h$";

export function specialToJExpr(s: Special): JStgExpr {
  return s === Special.Stack ? hdStack : hdStackPtr;
}

// ---------------------------------------------------
// helpers
// ---------------------------------------------------

export const sp: JStgExpr = specialToJExpr(Special.Sp);

export const stack: JStgExpr = specialToJExpr(Special.Stack);

/** `jsRegToInt = (+1) . fromEnum` - the 1-indexed register number. */
export const jsRegToInt = (r: StgReg): number => r + 1;

/** `intToJSReg r = toEnum (r - 1)` */
export const intToJSReg = (r: number): StgReg => r - 1;

/** Register expression from its 1-indexed number */
export const jsReg = (r: number): JStgExpr => register(intToJSReg(r));

export const maxReg: number = jsRegToInt(maxBoundReg);

export const minReg: number = jsRegToInt(0);

/** List of registers, starting from R1 */
export const regsFromR1: StgReg[] = Array.from({ length: maxBoundReg + 1 }, (_, i) => i);

/** List of registers, starting from R2 */
export const regsFromR2: StgReg[] = regsFromR1.slice(1);

/** List of registers, starting from R1 as JStgExpr.
 *
 * Kept as a generator (rather than 9.12.2's list) so existing callers that
 * `take` a prefix keep working. */
export function* jsRegsFromR1(): Generator<JStgExpr> {
  for (const r of regsFromR1) yield register(r);
}

/** List of registers, starting from R2 as JExpr */
export function* jsRegsFromR2(): Generator<JStgExpr> {
  const it = jsRegsFromR1();
  it.next();
  yield* it;
}

// ---------------------------------------------------
// caches
// ---------------------------------------------------

/** `lowRegs = map reg_to_ident [R1 .. R31]` - note these are Idents, named
 * h$r1 .. h$r31 (`map toLower . show`). */
export const lowRegs: Ident[] = regsFromR1.slice(0, 31).map((r) => name(`${hdStr}r${jsRegToInt(r)}`));

export const retRegs: Ident[] = Object.keys(StgRet)
  .filter((k) => isNaN(Number(k)))
  .map((n) => name(hdStr + n.toLowerCase()));

/** cache JExpr representing StgReg.
 *
 * R1..R31 are the globals h$r1..h$r31; R32..R128 are `h$regs[fromEnum r - 32]`.
 * `fromEnum R32` is 31, so R32 renders as `h$regs[-1]` and the array is used
 * from index -1 upwards. That off-by-one is upstream's, and GHC's own rts.js
 * agrees: `case(32):return h$regs[(-1)];`. */
const registers: JStgExpr[] = [
  ...lowRegs.map((i) => global(i)),
  ...regsFromR1.slice(31).map((r) => idx_(hdRegs, jInt(r - 32))),
];

/** cache JExpr representing StgRet */
const rets: JStgExpr[] = retRegs.map((i) => global(i));

/** Given a register, return the JS syntax object representing that register */
export function register(i: StgReg): JStgExpr {
  return registers[i]!;
}

/** Given a register, return the JS syntax object representing that register */
export const foreignRegister = (i: StgRet): JStgExpr => rets[i]!;

// ---------------------------------------------------
// compatibility shims for apply.ts
//
// None of these exist in 9.12.2 (its Apply.hs goes through h$getReg/h$setReg
// instead). They keep the 10.1-era apply.ts compiling until it is realigned.
// ---------------------------------------------------

/** @deprecated 10.1 only; `jsRegToInt` in 9.12.2. */
export const regNumber = jsRegToInt;

/** @deprecated 10.1 only. Last register with its own global: R31. */
export const maxLowReg: StgReg = 30;

/** @deprecated 10.1 only. `h$regs[n - 32]` for a dynamic register number. */
export const highReg_expr = (r: JStgExpr): JStgExpr => idx_(hdRegs, jSub(r, jInt(32)));
