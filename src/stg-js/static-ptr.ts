/** Ported from GHC/StgToJS/StaticPtr.hs (GHC 9.12.2). */
import type { JStgStat } from "../js/jstg-syntax.js";
import { mconcatJStgStat } from "../js/jstg-syntax.js";
import { jLam2, sel_ } from "../js/make.js";
import type { Binder } from "../stg.js";
import { varForId } from "./ids.js";
import { genLit } from "./literal.js";
import type { GenState } from "./monad.js";
import { hdHsSptInsert, hdInitStatic } from "./symbols.js";

/** `GHC.Linker.Types.SptEntry`: the static-pointer's Id plus its 128-bit
 * fingerprint, as two Word64 halves. */
export interface SptEntry {
  id: Binder;
  fingerprint: [bigint, bigint];
}

export function initStaticPtrs(gs: GenState, ptrs: SptEntry[]): JStgStat {
  return mconcatJStgStat(ptrs.map((p) => initStatic(gs, p)));
}

function initStatic(gs: GenState, e: SptEntry): JStgStat {
  const i = varForId(gs, e.id);
  // `mkLitWord64` per half; genLit unarises each Word64 into a (hi,lo) pair,
  // so h$hs_spt_insert receives four numbers plus the pointer.
  const fpa = e.fingerprint.flatMap((w) => genLit(gs, { tag: "LitNumWord64", value: w }));
  const sptInsert: JStgStat = { tag: "ApplStat", fn: hdHsSptInsert, args: [...fpa, i] };
  return { tag: "ApplStat", fn: sel_(hdInitStatic, "push"), args: [jLam2(sptInsert)] };
}
