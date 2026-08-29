/** Ported from GHC/StgToJS/Linker/Linker.hs (GHC 9.12.2) - the assembly step.
 *
 * What is *not* ported, and why: everything upstream of assembly. GHC reads
 * `.o` files (`readObjectBlocks`), unpacks `.a` archives (`ArchiveCache`,
 * `readArObject`) - ghcts's `stgToJS` hands back `LinkableUnit`s in memory
 * already, so that part has no counterpart. Also skipped: emcc/clibs.js, the
 * closure-compiler externs, `writeHtml`, `writeRunner`, the linker stats
 * (`renderLinkerStats`) and the `out.frefs.*` foreign-reference dumps.
 *
 * What is ported: `getDeps`/`requiredBlocks` (as `reachableUnits` below -
 * GHC's version walks a dependency graph GHC computed and cached per object
 * file at compile time; ghcts recomputes each unit's free identifiers from
 * its own already-generated code instead of caching them separately, since
 * nothing else needs that data), `linkModules` (the commoned-up metadata),
 * `renderModules` (module code, then metadata, then exports), `runMainJS`,
 * and `combineFiles`.
 */
import { jsOptimize } from "../js/optimizer.js";
import { renderStat } from "../js/ppr.js";
import type { JStat } from "../js/syntax.js";
import { mconcatJStgStat } from "../js/jstg-syntax.js";
import type { JStgStat } from "../js/jstg-syntax.js";
import { identsS } from "../js/transform.js";
import { jStgStatToJS } from "../js/transform.js";
import { closureInfoStat } from "../stg-js/closure.js";
import type { LinkableUnit } from "../stg-js/codegen.js";
import type { Module, StaticInfo } from "../stg-js/monad.js";
import { staticDeclStat, staticInitStat } from "../stg-js/codegen.js";
import { renderRts } from "../stg-js/rts.js";
import { renderStaticRts } from "../stg-js/rts-static.js";
import type { StgToJSConfig } from "../stg-js/types.js";

/** GHC's own entry symbol for `Main.main`, per `runMainJS` below - the sole
 * root `getDeps` starts from for an executable (`root_funs` = `[mainFun]` in
 * `GHC.StgToJS.Linker.Linker.link`; ghcts links exactly one executable, so
 * this is always the whole root set). */
const MAIN_SYMBOL = "h$mainZCZCMainzimain";

/** `getDeps`/`requiredBlocks`: which of `mods`' units are actually reachable
 * from `main`, so the ones that aren't never reach `renderModules`.
 *
 * GHC's version walks `BlockInfo`s it computed and cached per object file
 * during compilation (`bi_block_deps`/`blockFunDeps`, from `Deps.hs`). ghcts
 * has the same data available, just not cached separately: `luDepSymbols`
 * (`src/stg-js/codegen.ts`) is `collectIds`' STG-level free-identifier set
 * for the unit, already resolved to symbol strings by `identForId` at the
 * point each unit was generated - exactly GHC's own dependency source, not a
 * re-derivation from the rendered JS. That rendered-JS re-derivation was
 * tried first and is kept as a defense-in-depth supplement below (via
 * GHC.JS.Transform's `identsS`, walking the *same* `staticDeclStat` /
 * `staticInitStat` / `closureInfoStat` renderModules itself uses): it caught
 * everything `luDepSymbols` was already relied on to source. `luDepSymbols`
 * doesn't have the gaps a rendered-AST re-derivation risks, because it's
 * sourced from the STG term directly, before codegen has a chance to lose
 * anything.
 *
 * `oiSymbols` (populated from `collectTopIds`) is *not* a complete list of
 * everything a unit's own code declares, though: `genToplevelDecl` also
 * calls `genToplevelConEntry`, which emits an extra `_con_e` constructor
 * entry point for a data constructor's own worker binding - a symbol
 * `oiSymbols` never learns about, since it only records the identifiers
 * `topDeps`/`collectTopIds` names. Before this pass that was invisible
 * because every unit was always included regardless; used as a reachability
 * index, a `bySymbol` built from `oiSymbols` alone doesn't know an
 * `_con_e` symbol has a home, so any *other* unit referencing it (a real
 * device run caught `Tip_con_e is not defined` after `Data.Map`'s `Tip`
 * constructor's unit was wrongly dropped, exactly this way) can never mark
 * that unit reachable. `declaredNames` recovers the complete set the same
 * way `unitDeps` recovers dependencies below: by walking the unit's own
 * already-generated code instead of trusting a field that was never meant to
 * be exhaustive on its own.
 *
 * A unit's own declared symbols are subtracted from the `identsS` scan in
 * `unitDeps` so a self-reference (a `DeclStat` mentions the name it
 * declares) never looks like an external dependency; `luDepSymbols` needs no
 * such filtering since `collectIds` already excludes the binding's own
 * top-level names.
 *
 * `luRequired` (GHC's `StaticPtr` case - nothing else ever names a
 * `StaticPtr` binding directly, since it's found through the static-pointer
 * table instead) is the only other root category, matching
 * `requiredBlocks`'s `bi_must_link`. */
function reachableUnits(mods: ModuleCode[], extraRoots: readonly string[] = []): Set<LinkableUnit> {
  const declaredNames = (s: JStgStat): string[] => {
    switch (s.tag) {
      case "DeclStat": return [s.ident];
      case "IfStat": return [...declaredNames(s.then), ...declaredNames(s.else)];
      case "WhileStat": return declaredNames(s.body);
      case "ForStat": return [...declaredNames(s.init), ...declaredNames(s.step), ...declaredNames(s.body)];
      case "ForInStat": return declaredNames(s.body);
      case "SwitchStat": return [...s.cases.flatMap(([, st]) => declaredNames(st)), ...declaredNames(s.default)];
      case "TryStat": return [...declaredNames(s.body), ...declaredNames(s.catch), ...declaredNames(s.finally)];
      case "BlockStat": return s.stats.flatMap(declaredNames);
      case "LabelStat": return declaredNames(s.body);
      case "FuncStat": return [s.ident];
      default: return [];
    }
  };

  const bySymbol = new Map<string, LinkableUnit>();
  for (const m of mods)
    for (const u of m.units) {
      for (const sym of u.luObjBlock.oiSymbols) bySymbol.set(sym, u);
      for (const sym of declaredNames(u.luObjBlock.oiStat)) if (!bySymbol.has(sym)) bySymbol.set(sym, u);
    }

  const unitDeps = (u: LinkableUnit): string[] => {
    const ob = u.luObjBlock;
    const whole = mconcatJStgStat([
      ob.oiStat,
      ...ob.oiStatic.map(staticDeclStat),
      ...ob.oiStatic.map(staticInitStat),
      ...ob.oiClInfo.map((ci) => closureInfoStat(false, ci)),
    ]);
    const own = new Set([...ob.oiSymbols, ...declaredNames(ob.oiStat)]);
    return [...u.luDepSymbols, ...identsS(whole).filter((ident) => !own.has(ident))];
  };

  const reachable = new Set<LinkableUnit>();
  const queue: LinkableUnit[] = [];
  const addRoot = (u: LinkableUnit): void => {
    if (reachable.has(u)) return;
    reachable.add(u);
    queue.push(u);
  };

  // `ghc-prim`/`ghc-internal` (the two boot packages RTS_SEATS/hand-written
  // RTS glue reaches into) always stay in: their own units still turn out to
  // reference *each other* the same indirect way `Tip_con_e` did above (a
  // `_con_e`/canonical-nullary-constructor symbol reachable only from inside
  // another boot binding's own static/closure data, not from user code or
  // rts.ts/rts-static.ts text at all), so `textRoots` on the RTS text alone
  // doesn't reliably close every edge - each fix so far has traded one
  // `ReferenceError` for a smaller one. These two packages are a small,
  // fixed cost regardless (real GHC links its own boot packages unpruned
  // into every program too), unlike the large, genuinely per-program-varying
  // Miso/Native modules pruning exists to cut - so being unconditional here
  // trades a bounded, known amount of size for closing this entire class of
  // gap outright instead of chasing it one device crash at a time.
  const bootPackage = (sym: string): boolean => /^h\$ghczm(?:internal|prim)ZC/.test(sym);
  for (const m of mods)
    for (const u of m.units)
      if (u.luRequired || u.luObjBlock.oiSymbols.some((s) => s === MAIN_SYMBOL || bootPackage(s))) addRoot(u);
  for (const sym of extraRoots) {
    const target = bySymbol.get(sym);
    if (target) addRoot(target);
  }

  while (queue.length) {
    const u = queue.pop()!;
    for (const ident of unitDeps(u)) {
      const target = bySymbol.get(ident);
      if (target) addRoot(target);
    }
  }
  return reachable;
}

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
 * `debug = False` in `linkModules`, so closure infos carry no debug data.
 *
 * `getDeps`/`requiredBlocks` (`reachableUnits`) run first, exactly as in
 * GHC's own `link` (which computes `must_link`/`link_deps` before ever
 * touching `renderModules`): only units transitively reachable from `main`
 * (plus `StaticPtr` roots) are kept, so an unused function - or an entire
 * unused module pulled in only because something else in that module was
 * imported - never reaches the optimizer or the output file. */
export function renderModules(config: StgToJSConfig, mods: ModuleCode[], extraRoots: readonly string[] = []): string {
  const debug = false;
  const live = reachableUnits(mods, extraRoots);
  mods = mods
    .map((m) => ({ module: m.module, units: m.units.filter((u) => live.has(u)) }))
    .filter((m) => m.units.length > 0);
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

/** Every `h$<module>Zi<name>`-shaped identifier mentioned in a rendered
 * string. The RTS/boot JS (`rts`/`lib` below) is emitted as plain text, not
 * an AST `reachableUnits` can walk - but GHC's own hand-written RTS seat
 * closures do reference specific user/boot-library bindings by name outright
 * (`h$main`/`h$Thread` call the program's top-level exception handler,
 * `GHC.Internal.Conc.Sync.reportError`, on an uncaught exception - see
 * `ghcModules`'s `RTS_SEATS` comment in `src/build.ts`), so those names need
 * to be additional reachability roots or a program that never happens to
 * reference its own exception handler elsewhere loses it to pruning and dies
 * with a `ReferenceError` the moment the RTS actually needs it. */
function textRoots(text: string): string[] {
  return [...text.matchAll(/\bh\$[A-Za-z0-9_]*zi[A-Za-z0-9_]*\b/gi)].map((m) => m[0]);
}

/** `link`, reduced to the four artefacts and their concatenation
 * (`combineFiles`: rts.js, lib.js, out.js, [clibs.js], runmain.js). */
export function link(config: StgToJSConfig, mods: ModuleCode[]): LinkedJs {
  const rts = renderRts(config);
  const lib = renderStaticRts(config);
  const out = renderModules(config, mods, [...textRoots(rts), ...textRoots(lib)]);
  const runmain = runMainJS;
  return { rts, lib, out, runmain, all: rts + lib + out + runmain };
}
