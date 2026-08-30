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
import { access, mkdir, readFile, readdir, writeFile } from "node:fs/promises";
import { dirname, join, relative, resolve } from "node:path";
import { listCabalTargets, parseCabalLibrary } from "./cabal.js";
import { parseModule } from "./parser.js";
import { elaborateProgram, USER_MAIN } from "./elaborate.js";
import { RTS_SEATS } from "./prelude.js";
import { BINDING_OVERRIDES } from "./binding-overrides.js";
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
    const overrides = BINDING_OVERRIDES[parsed.module.ast.name];
    if (overrides) {
      parsed.module.ast.declarations = parsed.module.ast.declarations.map((decl) => {
        if (decl.tag !== "value") return decl;
        if (!Object.hasOwn(overrides, decl.name)) return decl;
        const patch = overrides[decl.name];
        return {
          tag: "foreign" as const,
          name: decl.name,
          javascript: patch.javascript,
          signature: patch.signature,
          arity: Math.max(0, patch.signature.length - 1),
          span: decl.span,
        };
      });
    }
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

/** Finds a dependency with no `ghcts.json` sourceRoot to search from yet: the
 * nearest ancestor of `project` holding `<name>.cabal`, or a direct child of
 * that ancestor holding it. The first covers a dependency that IS an
 * ancestor (`sample-app`'s parent directory is the `miso` checkout itself);
 * the second covers one that is a sibling of an ancestor (`references/miso`
 * next to `references/misogram`) - the two shapes every dependency in this
 * repo actually uses. */
async function findCabalDir(start: string, name: string): Promise<string | undefined> {
  const hasIt = (dir: string) => access(join(dir, `${name}.cabal`)).then(() => true, () => false);
  for (let dir = resolve(start); ; dir = dirname(dir)) {
    if (await hasIt(dir)) return dir;
    try {
      for (const entry of await readdir(dir, { withFileTypes: true })) {
        if (!entry.isDirectory()) continue;
        const child = join(dir, entry.name);
        if (await hasIt(child)) return child;
      }
    } catch {
      // Unreadable directory: nothing more to find at this level.
    }
    if (dirname(dir) === dir) return undefined;
  }
}

/** Derives a `GhctsConfig` straight from a project's own `.cabal` file, for a
 * project with no `ghcts.json` at all - so a checkout with only the `.cabal`
 * layout it would hand to `cabal build` builds under ghcts too.
 *
 * Reads the `.cabal`'s sole `executable` stanza (a `library`-only package has
 * no runnable entry to guess, and cabal flag selection for a native/WASM
 * build usually lives outside the app's own file - in a `cabal.project` or a
 * Makefile - so this only ever derives the plain default build). Each of its
 * `build-depends` that resolves to a discoverable `<name>.cabal` becomes both
 * a dependency and a source root; one that does not (miso's boot packages,
 * which ghcts's own Prelude already covers) is silently skipped, exactly the
 * set a hand-written `ghcts.json` in this repo already leaves out. */
export async function deriveCabalConfig(project: string): Promise<GhctsConfig | undefined> {
  const cabalFile = (await readdir(project)).find((name) => name.endsWith(".cabal"));
  if (!cabalFile) return undefined;
  const source = await readFile(join(project, cabalFile), "utf8");
  const target = listCabalTargets(source).find((t) => t.startsWith("executable:"));
  if (!target) return undefined;

  const own = parseCabalLibrary(source, [], target);
  const sourceRoots = own.sourceDirs.length ? own.sourceDirs : ["."];
  const dependencies: string[] = [];
  for (const name of own.buildDepends) {
    if (name === "base") continue;
    const dir = await findCabalDir(project, name);
    if (!dir) continue;
    const depSource = await readFile(join(dir, `${name}.cabal`), "utf8");
    const dep = parseCabalLibrary(depSource, [], "library");
    dependencies.push(name);
    for (const root of dep.sourceDirs.length ? dep.sourceDirs : ["."])
      sourceRoots.push(relative(project, join(dir, root)));
  }

  return {
    version: 1,
    sourceRoots,
    entry: { module: "Main", export: "main" },
    ...(dependencies.length ? { dependencies } : {}),
    targets: ["browser", "node"],
    outDir: "dist",
  };
}

/** Reads a project's `ghcts.json`, or - when there is none - derives one from
 * its `.cabal` file (`deriveCabalConfig`). Throws the original ENOENT when
 * neither exists, so a project that is not a cabal package at all still gets
 * the familiar "no such file" pointing at `ghcts.json`. */
export async function loadConfig(project: string): Promise<GhctsConfig> {
  try {
    return JSON.parse(await readFile(join(project, "ghcts.json"), "utf8"));
  } catch (cause) {
    const derived = await deriveCabalConfig(project);
    if (derived) return derived;
    throw cause;
  }
}

/** Where a dependency lives: the nearest ancestor of one of the source roots
 * holding `<name>.cabal`.  A source root already points inside the package it
 * belongs to (miso's is `../../miso/src`), so nothing further has to be
 * configured to find the package's own JavaScript beside its Haskell. */
async function packageDir(project: string, config: GhctsConfig, name: string): Promise<string | undefined> {
  for (const root of config.sourceRoots) {
    for (let dir = resolve(project, root); ; dir = dirname(dir)) {
      if (await access(join(dir, `${name}.cabal`)).then(() => true, () => false)) return dir;
      if (dirname(dir) === dir) break;
    }
  }
  return undefined;
}

/** Every dependency's `js-sources`, concatenated in declaration order.
 *
 * This is the same thing `renderStaticRts` does for the boot packages, for the
 * packages a project names instead: GHC's linker makes no distinction, lib.js
 * is every package's `js-sources` in link order.  It matters far more than it
 * sounds - miso ships its whole runtime this way, and without it `globalThis.miso`
 * is never defined and the program dies the moment Haskell calls into it. */
async function packageJs(project: string, config: GhctsConfig): Promise<string> {
  const sources: string[] = [];
  for (const name of config.dependencies ?? []) {
    const dir = await packageDir(project, config, name);
    if (!dir) continue;
    const cabal = parseCabalLibrary(await readFile(join(dir, `${name}.cabal`), "utf8"), config.flags ?? []);
    for (const file of cabal.jsSources) sources.push(await readFile(join(dir, file), "utf8"));
  }
  return sources.map((source) => `${source}\n`).join("");
}

export async function build(options: {
  project: string;
  config: GhctsConfig;
  emit?: boolean;
  /** Logs each pipeline stage's duration and output size to stderr as it
   * finishes. For diagnosing where a build's time or a bundle's bytes went -
   * a normal run stays silent. */
  verbose?: boolean;
}): Promise<BuildResult> {
  const { project, config } = options;
  const stgConfig = {
    ...defaultStgToJSConfig,
    optimization: config.optimization ?? defaultStgToJSConfig.optimization,
  };
  const started = Date.now();
  const log = (message: string) =>
    options.verbose && console.error(`[ghcts +${((Date.now() - started) / 1000).toFixed(2)}s] ${message}`);

  const loaded = await loadProgram(project, config);
  log(`parsed ${loaded.modules.size} module${loaded.modules.size === 1 ? "" : "s"}`);
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
  log(`elaborated from \`${root}\``);

  const desugared = desugarModule(elaborated.module, `${root}.hs`);
  diagnostics.push(...desugared.diagnostics);
  log(`desugared to ${desugared.program.binds.length} Core binding${desugared.program.binds.length === 1 ? "" : "s"}`);
  if (diagnostics.some((d) => d.severity === "error")) return { diagnostics };

  const stg = coreToStg(desugared.program);
  log(`lowered to ${stg.bindings.length} STG binding${stg.bindings.length === 1 ? "" : "s"}`);
  const linked = link(stgConfig, ghcModules(stgConfig, root, stg.bindings));
  log(`linked (rts ${linked.rts.length}B, lib ${linked.lib.length}B, out ${linked.out.length}B)`);

  // `link` only knows the boot packages' JavaScript, so the project's own
  // dependencies join it at the end of lib.js - where GHC puts a leaf package's
  // js-sources, after the packages it depends on - and all.js is recomposed
  // from the same four parts in the same order.
  const packages = await packageJs(project, config);
  const lib = linked.lib + packages;
  const jsexe = { ...linked, lib, all: linked.rts + lib + linked.out + linked.runmain };
  log(`packaged ${config.dependencies?.length ?? 0} dependenc${config.dependencies?.length === 1 ? "y" : "ies"}, all.js is ${jsexe.all.length}B`);

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
    log(`wrote jsexe to ${out}`);
  }

  return { diagnostics, jsexe };
}
