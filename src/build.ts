/** Compile a project the way GHC's JavaScript backend does.
 *
 * parse -> elaborate -> desugar -> Core -> STG -> StgToJS -> link.
 *
 * This replaces the interpretive path that produced `lazy`/`force`/`apply`
 * closures against a bespoke runtime. That path could run Haskell but could
 * never produce what GHC produces, so no amount of repair would have reached
 * the goal - the emitted code has to speak GHC's calling convention, because
 * the RTS it links against is GHC's.
 *
 * What comes out is a real `.jsexe`: rts.js, lib.js, out.js, runmain.js, and
 * all.js as their concatenation, in GHC's own order.
 */
import { mkdir, readFile, readdir, writeFile } from "node:fs/promises";
import { dirname, join, relative } from "node:path";
import { parseModule } from "./parser.js";
import { elaborateProgram, USER_MAIN } from "./elaborate.js";
import { RTS_SEATS } from "./prelude.js";
import { desugarModule } from "./desugar.js";
import { coreToStg } from "./core-to-stg.js";
import { genUnits, stgToJS } from "./stg-js/codegen.js";
import { link, type ModuleCode } from "./linker/linker.js";
import { runG, type IdCache } from "./stg-js/monad.js";
import { defaultStgToJSConfig, type StgToJSConfig } from "./stg-js/types.js";
import { error } from "./diagnostics.js";
import type { Diagnostic, GhctsConfig } from "./types.js";
import type { Module } from "./ast.js";
import type { StgBinding } from "./stg.js";
import type { Ident } from "./js/ident.js";

export interface BuildResult {
  diagnostics: Diagnostic[];
  /** Written only when every module compiled. */
  jsexe?: { rts: string; lib: string; out: string; runmain: string; all: string };
}

async function walkHs(root: string, found: string[] = []): Promise<string[]> {
  let entries;
  try {
    entries = await readdir(root, { withFileTypes: true });
  } catch {
    return found;
  }
  for (const entry of entries) {
    const path = join(root, entry.name);
    if (entry.isDirectory()) await walkHs(path, found);
    else if (entry.name.endsWith(".hs")) found.push(path);
  }
  return found;
}

/** Parse the entry module and everything it transitively imports.
 *
 * Only the import closure, which is what GHC does: a module nothing imports
 * is never read, so its syntax cannot fail the build. That is not an
 * optimisation. miso ships Miso/FFI/QQ.hs, Miso/Lens/Generic.hs and
 * Miso/Lens/TH.hs - quasiquotes, type-level operators and Template Haskell -
 * which appear only inside comments in Miso.hs. Parsing every file under the
 * source roots made three unreachable modules gate the whole program. */
export async function loadProgram(
  project: string,
  config: GhctsConfig,
): Promise<{ modules: Map<string, Module>; diagnostics: Diagnostic[] }> {
  // A module's name is its path under a source root, so the index can be
  // built without reading anything.
  const byName = new Map<string, string>();
  for (const root of config.sourceRoots) {
    const base = join(project, root);
    for (const file of await walkHs(base)) {
      const name = relative(base, file).replace(/\.hs$/, "").split(/[\\/]/).join(".");
      if (!byName.has(name)) byName.set(name, file);
    }
  }

  // The CPP symbols the target selects. Without them every #ifdef in a
  // dependency takes its #else branch, which for miso means compiling the
  // neither-GHCJS-nor-native code - including the old `$r = $1` FFI dialect
  // that GHC 9.12 does not accept. arch(javascript) is what this backend is,
  // so GHCJS_BOTH and GHCJS_NEW come with it (miso.cabal:28-40).
  const defines = new Set<string>(["GHCJS_BOTH", "GHCJS_NEW", ...(config.cpp ?? [])]);

  const modules = new Map<string, Module>();
  const diagnostics: Diagnostic[] = [];
  const queue = [config.entry.module];
  const seen = new Set<string>();
  while (queue.length) {
    const name = queue.shift()!;
    if (seen.has(name)) continue;
    seen.add(name);
    const file = byName.get(name);
    // A module we cannot find is reported by the elaborator as unresolved
    // names, which says more than a missing-file error would.
    if (!file) continue;
    const parsed = parseModule(await readFile(file, "utf8"), relative(project, file), defines);
    diagnostics.push(...parsed.diagnostics);
    if (!parsed.module?.ast) continue;
    modules.set(parsed.module.ast.name, parsed.module.ast);
    for (const imported of parsed.module.ast.imports) queue.push(imported.module);
  }
  return { modules, diagnostics };
}

/** Put the program back into the modules GHC keeps its pieces in.
 *
 * GHC compiles `Main.hs` to a module `Main` and *also* generates a hidden
 * module literally named `:Main`, holding one binding,
 * `:Main.main = runMainIO Main.main`. That wrapper is what the RTS enters:
 * `runMainJS` is `h$main(h$mainZCZCMainzimain)`, and `ZCZCMain` is
 * `zEncode("main") ++ "ZC" ++ zEncode(":Main")`. Emitting the whole program as
 * one module called `Main` therefore names the wrapper `h$mainZCMainzimain`
 * and leaves the entry line pointing at nothing - the program links but cannot
 * start. The same is true of `RTS_SEATS`, the ghc-internal closures `h$main`
 * and `h$Thread` name outright.
 *
 * Elaboration produces one flat namespace, so it builds the wrapper as `main`
 * and renames the user's own action to `USER_MAIN`; the split hands both names
 * back, `Main.main` being the user's, exactly as GHC has it.
 *
 * The subtlety is the reference *across* a split. `makeIdentForId` names every
 * Id after the module being compiled, because a ghcts Binder carries no
 * defining module ("GHC uses the Id's own defining module when it is
 * exported"), so an independent second `stgToJS` call emits the wrapper's
 * references to `Main`'s bindings as `h$mainZCZCMainzi...`, which nothing
 * defines. Seeding the second run's Id cache with the one `Main`'s compilation
 * built supplies exactly the missing fact: an Id already named while compiling
 * `Main` keeps that name. `gsIdentMint` comes with it because it records the
 * order symbols were interned in - process-wide in GHC - and that order decides
 * how `globalOccs` sorts. */
function ghcModules(config: StgToJSConfig, root: string, bindings: StgBinding[]): ModuleCode[] {
  const mainMod = { unitId: "main", moduleName: root };
  const named = (b: StgBinding, n: string): boolean => b.tag === "StgNonRec" && b.binder.name === n;
  const rename = (b: StgBinding, n: string): StgBinding =>
    b.tag === "StgNonRec" ? { ...b, binder: { ...b.binder, name: n } } : b;

  // Where each binding goes and what GHC calls it once it is there.
  const moved = [
    { module: { unitId: "main", moduleName: ":Main" }, from: "main", name: "main" },
    ...RTS_SEATS.map((s) => ({ module: { unitId: s.unitId, moduleName: s.moduleName }, from: s.binding, name: s.name })),
  ].flatMap((m) => {
    const binding = bindings.find((b) => named(b, m.from));
    return binding ? [{ module: m.module, binding: rename(binding, m.name), from: m.from }] : [];
  });

  // Without the wrapper `main` is not an `IO` action, there is nothing for the
  // RTS to enter, and the seats the elaborator leaves out are not needed.
  if (!moved.some((m) => m.from === "main") || !bindings.some((b) => named(b, USER_MAIN))) {
    return [{ module: mainMod, units: stgToJS(config, mainMod, bindings) }];
  }

  const program = bindings
    .filter((b) => !moved.some((m) => named(b, m.from)))
    .map((b) => (named(b, USER_MAIN) ? rename(b, "main") : b));

  let idents: IdCache = new Map();
  let mint: Map<Ident, number> = new Map();
  const mainUnits = runG(config, mainMod, new Map(), (gs) => {
    const units = genUnits(gs, mainMod, program);
    idents = gs.gsIdents;
    mint = gs.gsIdentMint;
    return units;
  });

  return [
    { module: mainMod, units: mainUnits },
    ...moved.map((m) => ({
      module: m.module,
      units: runG(config, m.module, new Map(), (gs) => {
        for (const [key, ident] of idents) gs.gsIdents.set(key, ident);
        for (const [ident, order] of mint) gs.gsIdentMint.set(ident, order);
        return genUnits(gs, m.module, [m.binding]);
      }),
    })),
  ];
}

export async function build(options: {
  project: string;
  config: GhctsConfig;
  emit?: boolean;
}): Promise<BuildResult> {
  const { project, config } = options;
  const stgConfig = defaultStgToJSConfig;

  const loaded = await loadProgram(project, config);
  const diagnostics = [...loaded.diagnostics];
  if (diagnostics.some((d) => d.severity === "error")) return { diagnostics };

  const root = config.entry.module;
  if (!loaded.modules.has(root)) {
    diagnostics.push(error("E_MODULE_MISSING", `entry module \`${root}\` not found`, project));
    return { diagnostics };
  }

  // Elaboration resolves imports across the whole program and turns classes
  // and instances into dictionary passing, so what desugar sees is a single
  // flat pile of ordinary declarations.
  const elaborated = elaborateProgram(loaded.modules, root, `${root}.hs`);
  diagnostics.push(...(elaborated.diagnostics ?? []));

  const desugared = desugarModule(elaborated.module, `${root}.hs`);
  diagnostics.push(...desugared.diagnostics);
  if (diagnostics.some((d) => d.severity === "error")) return { diagnostics };

  const stg = coreToStg(desugared.program);
  const jsexe = link(stgConfig, ghcModules(stgConfig, root, stg.bindings));

  if (options.emit) {
    const out = join(project, config.outDir, "jsexe");
    await mkdir(out, { recursive: true });
    for (const [name, text] of [
      ["rts.js", jsexe.rts],
      ["lib.js", jsexe.lib],
      ["out.js", jsexe.out],
      ["runmain.js", jsexe.runmain],
      ["all.js", jsexe.all],
    ] as const) {
      await writeFile(join(out, name), text);
    }
  }

  return { diagnostics, jsexe };
}
