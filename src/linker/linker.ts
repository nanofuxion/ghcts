/** Ported from GHC/StgToJS/Linker/Linker.hs (GHC 9.12.2) - the assembly step.
 *
 * What is *not* ported, and why: everything upstream of assembly. GHC reads
 * `.o` files (`readObjectBlocks`), unpacks `.a` archives (`ArchiveCache`,
 * `readArObject`), and walks a dependency graph over the blocks in them
 * (`getDeps`, `requiredBlocks`, `LinkPlan`) to decide which blocks to emit.
 * ghcts's `stgToJS` hands back `LinkableUnit`s in memory, already the set to
 * emit, so all of that has no counterpart. Also skipped: emcc/clibs.js, the
 * closure-compiler externs, `writeHtml`, `writeRunner`, the linker stats
 * (`renderLinkerStats`) and the `out.frefs.*` foreign-reference dumps.
 *
 * What is ported: `linkModules` (the commoned-up metadata), `renderModules`
 * (module code, then metadata, then exports), `runMainJS`, and `combineFiles`.
 */
import { jsOptimize } from "../js/optimizer.js";
import { renderStat } from "../js/ppr.js";
import type { JStat } from "../js/syntax.js";
import { mconcatJStgStat } from "../js/jstg-syntax.js";
import { jStgStatToJS } from "../js/transform.js";
import { closureInfoStat } from "../stg-js/closure.js";
import type { LinkableUnit } from "../stg-js/codegen.js";
import type { Module, StaticInfo } from "../stg-js/monad.js";
import { staticDeclStat, staticInitStat } from "../stg-js/codegen.js";
import { renderRts } from "../stg-js/rts.js";
import { renderStaticRts } from "../stg-js/rts-static.js";
import type { StgToJSConfig } from "../stg-js/types.js";

/** One module's compiled output, as `stgToJS` returns it. `ModuleCode` in
 * Linker.hs, minus `mc_frefs` (ghcts's ObjBlock drops `oiFImports`). */
export interface ModuleCode {
  module: Module;
  units: LinkableUnit[];
}

export interface LinkedJs {
  rts: string;
  lib: string;
  out: string;
  runmain: string;
  all: string;
}

/** `runMainJS (UseEmccRts False)`. */
export const runMainJS = "h$main(h$mainZCZCMainzimain);\n";

/** `hPutJS`: an empty block writes nothing at all; anything else is rendered
 * and terminated with a newline so the file ends on one. */
function hPutJS(s: JStat): string {
  if (s.tag === "BlockStat" && s.stats.length === 0) return "";
  return renderStat(s) + "\n";
}

/** `nubStaticInfo` - only keep the first StaticInfo with a given name. There is
 * no reason for the initializing value to differ for the same global name. */
function nubStaticInfo(xs: StaticInfo[]): StaticInfo[] {
  const seen = new Set<string>();
  return xs.filter((x) => (seen.has(x.siVar) ? false : (seen.add(x.siVar), true)));
}

/** `renderModules . linkModules`: each module's code, then the commoned-up
 * metadata (static declarations, static initialisers, closure info tables),
 * then the raw module exports.
 *
 * `debug = False` in `linkModules`, so closure infos carry no debug data. */
export function renderModules(config: StgToJSConfig, mods: ModuleCode[]): string {
  const debug = false;
  const statics = nubStaticInfo(mods.flatMap((m) => m.units.flatMap((u) => u.luObjBlock.oiStatic)));
  const infos = mods.flatMap((m) => m.units.flatMap((u) => u.luObjBlock.oiClInfo));

  const code = mods
    .map((m) => hPutJS(jsOptimize(jStgStatToJS(mconcatJStgStat(m.units.map((u) => u.luObjBlock.oiStat))))))
    .join("");

  const meta = mconcatJStgStat([
    ...statics.map(staticDeclStat),
    ...statics.map(staticInitStat),
    ...infos.map((ci) => closureInfoStat(debug, ci)),
  ]);

  // GHC's `mc_exports` is the concatenation of the blocks' `oiRaw`, which only
  // ever carries JS emitted by `foreign export javascript`. ghcts's ObjBlock
  // has no oiRaw, so the exports section is always empty.
  return code + hPutJS(jsOptimize(jStgStatToJS(meta)));
}

/** `link`, reduced to the four artefacts and their concatenation
 * (`combineFiles`: rts.js, lib.js, out.js, [clibs.js], runmain.js). */
export function link(config: StgToJSConfig, mods: ModuleCode[]): LinkedJs {
  const rts = renderRts(config);
  const lib = renderStaticRts(config);
  const out = renderModules(config, mods);
  const runmain = runMainJS;
  return { rts, lib, out, runmain, all: rts + lib + out + runmain };
}
