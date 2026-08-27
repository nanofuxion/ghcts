/** Ported 1:1 from GHC/StgToJS/Rts/Types.hs.
 *
 * Small helpers the RTS generator uses to talk about closures and stack
 * frames. `traceRts` and `assertRts` emit nothing unless the corresponding
 * config flag is on, which is why GHC's default output carries no tracing.
 */
import { memptyJStgStat, mconcatJStgStat, type JStgExpr, type JStgStat } from "../js/jstg-syntax.js";
import type { JSM } from "../js/jstg-monad.js";
import {
  app,
  appS,
  assign_,
  idx_,
  ifS,
  jAdd,
  jIf,
  jInt,
  jSub,
  jVar,
  jwhenS,
  lt_,
  mask8,
  sel_,
  shr_,
  strictEq_,
} from "../js/make.js";
import { hdApGen, hdClosureTypeNameStr, hdLogStr } from "./symbols.js";
import { sp, stack } from "./regs.js";
import type { StgToJSConfig } from "./types.js";

/** GHC writes `appS "throw"` - a JS keyword, not an h$ RTS symbol, so this
 * one name is deliberately not sourced from symbols.ts. */
const throwStr = "throw";

/** Inject a trace statement on `ex` into the compiled program. */
export function traceRts(s: StgToJSConfig, ex: JStgExpr): JStgStat {
  return s.traceRts ? appS(hdLogStr, [ex]) : memptyJStgStat;
}

/** Assert that `ex` holds, throwing `m` in JS land otherwise. */
export function assertRts(s: StgToJSConfig, ex: JStgExpr, m: JStgExpr): JStgStat {
  return s.assertRts
    ? jwhenS({ tag: "UOpExpr", op: "NotOp", value: ex }, appS(throwStr, [m]))
    : memptyJStgStat;
}

/** Name of the closure `c`. */
export const clName = (c: JStgExpr): JStgExpr => sel_(c, "n");

/** Type name of the closure `c`. */
export const clTypeName = (c: JStgExpr): JStgExpr => app(hdClosureTypeNameStr, [sel_(c, "t")]);

/** Assign the size of a stack frame - header included - into `tgt`.
 *
 * A frame header's `arity` packs two numbers: `arity & 0xff` is the argument
 * count and `arity >> 8` is the register count. `h$ap_gen` is special-cased
 * because its size is not in its own `size` field but in the word beneath the
 * header; a negative `size` tag means the same thing. */
export function stackFrameSize(js: JSM, tgt: JStgExpr, f: JStgExpr): JStgStat {
  const underHeader = idx_(stack, jSub(sp, jInt(1)));
  return jIf(
    strictEq_(f, hdApGen),
    assign_(tgt, jAdd(shr_(underHeader, jInt(8)), jInt(2))),
    jVar(js, (tag) =>
      mconcatJStgStat([
        assign_(tag, sel_(f, "size")),
        ifS(lt_(tag, jInt(0)), assign_(tgt, underHeader), assign_(tgt, jAdd(mask8(tag), jInt(1)))),
      ]),
    ),
  );
}
