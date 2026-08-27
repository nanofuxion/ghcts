/** Ported from GHC/StgToJS/Regs.hs.
 *
 * The JS backend's "registers": R1..Rn, the stack pointer/array, and the
 * return registers used to smuggle extra results out of foreign calls.
 *
 * Two Haskell-isms have no TS counterpart and are handled as follows:
 *   - `newtype StgReg = StgReg Int` is a bare `number` here, holding the same
 *     0-indexed payload, so Haskell's derived Ord (`i <= maxCachedReg` in
 *     `register`) and Ix (array indexing) both fall out of plain arithmetic.
 *     The `R1`..`R4` pattern synonyms become constants of that type.
 *   - `instance ToJExpr` cannot be expressed, so each instance becomes a named
 *     function: `register` (StgReg), `foreignRegister` (StgRet), and
 *     `specialToJExpr` (Special).
 *
 * `regsFromR1` and friends are infinite lists in Haskell, consumed lazily by
 * callers that `take` as many registers as an application needs. TS arrays are
 * strict, so these are generator functions instead - same laziness, same
 * "too many registers" panic once the supply is exhausted.
 */
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr } from "../js/jstg-syntax.js";
import { global } from "../js/jstg-syntax.js";
import { jInt, jSub, idx_ } from "../js/make.js";
import { hdRegs, hdStack, hdStackPtr } from "./symbols.js";
import { StgRet } from "./types.js";

export { StgRet };

/** General purpose "registers". 0-indexed payload, exactly as GHC's newtype. */
export type StgReg = number;

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

/** 1-indexed register number (R1 has index 1) */
export const regNumber = (r: StgReg): number => r + 1;

/** StgReg from 1-indexed number */
function regFromNumber(r: number): StgReg {
  if (r < 1) throw new Error("StgToJS.Regs: assertion failed: r >= 1");
  return r - 1;
}

export const regsFromTo = (x: StgReg, y: StgReg): StgReg[] =>
  Array.from({ length: Math.max(0, y - x + 1) }, (_, k) => x + k);

/** Register expression from its 1-indexed index */
export const jsReg = (r: number): JStgExpr => register(regFromNumber(r));

export const minReg: StgReg = R1;

/** GHC uses `maxBound :: Int`; JS numbers top out earlier, and either bound is
 * far beyond any reachable register count. */
export const maxReg: StgReg = regFromNumber(Number.MAX_SAFE_INTEGER);

export const lowRegsCount = 31;

export const maxLowReg: StgReg = regFromNumber(lowRegsCount);

/** First register stored in h$regs array instead of having its own top-level
 * variable */
export const minHighReg: StgReg = maxLowReg + 1;

/** List of registers, starting from R1 */
export function* regsFromR1(): Generator<StgReg> {
  for (let r = R1; ; r++) {
    if (r > maxReg) throw new Error("StgToJS: code requires too many registers");
    yield r;
  }
}

/** List of registers, starting from R2 */
export function* regsFromR2(): Generator<StgReg> {
  const it = regsFromR1();
  it.next();
  yield* it;
}

/** List of registers, starting from R1 as JStgExpr */
export function* jsRegsFromR1(): Generator<JStgExpr> {
  for (const r of regsFromR1()) yield register(r);
}

/** List of registers, starting from R2 as JExpr */
export function* jsRegsFromR2(): Generator<JStgExpr> {
  const it = jsRegsFromR1();
  it.next();
  yield* it;
}

/** List of registers, starting from given reg as JExpr */
export function* jsRegsFrom(n: StgReg): Generator<JStgExpr> {
  const it = jsRegsFromR1();
  for (let i = 0; i < n; i++) it.next();
  yield* it;
}

/** High register */
export function highReg(r: number): JStgExpr {
  if (r < regNumber(minHighReg)) throw new Error("StgToJS.Regs: assertion failed: r >= regNumber minHighReg");
  return idx_(hdRegs, jInt(r - regNumber(minHighReg)));
}

/** High register indexing with a JS expression */
export const highReg_expr = (r: JStgExpr): JStgExpr => idx_(hdRegs, jSub(r, jInt(regNumber(minHighReg))));

// ---------------------------------------------------
// caches
// ---------------------------------------------------

export const lowRegs: StgReg[] = regsFromTo(minReg, maxLowReg);

/** low regs are named h$r1, h$r2, etc. */
export const lowRegsIdents: Ident[] = lowRegs.map((r) => name(`${hdStr}r${regNumber(r)}`));

export const retRegs: Ident[] = Object.keys(StgRet)
  .filter((k) => isNaN(Number(k)))
  .map((n) => name(hdStr + n.toLowerCase()));

/** cache JExpr representing StgRet */
const rets: JStgExpr[] = retRegs.map((i) => global(i));

/** Given a register, return the JS syntax object representing that register */
export const foreignRegister = (i: StgRet): JStgExpr => rets[i];

/** Given a register, return the JS syntax object representing that register */
export function register(i: StgReg): JStgExpr {
  // Expressions of common registers are cached; higher ones are made on the fly.
  return i <= maxCachedReg ? register_cache[i] : make_high_reg(i);
}

const maxCachedReg: StgReg = regFromNumber(128);

/** Make h$regs[XXX] expression for the register */
const make_high_reg = (r: StgReg): JStgExpr => highReg(regNumber(r));

/** cache JExpr representing StgReg */
const register_cache: JStgExpr[] = [
  ...lowRegsIdents.map((i) => global(i)),
  ...regsFromTo(minHighReg, maxCachedReg).map(make_high_reg),
];
