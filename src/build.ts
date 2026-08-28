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
import { elaborateProgram } from "./elaborate.js";
import { desugarModule } from "./desugar.js";
import { coreToStg } from "./core-to-stg.js";
import { stgToJS } from "./stg-js/codegen.js";
import { link } from "./linker/linker.js";
import { defaultStgToJSConfig } from "./stg-js/types.js";
import { error } from "./diagnostics.js";
import type { Diagnostic, GhctsConfig } from "./types.js";
import type { Module } from "./ast.js";

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
    const parsed = parseModule(await readFile(file, "utf8"), relative(project, file));
    diagnostics.push(...parsed.diagnostics);
    if (!parsed.module?.ast) continue;
    modules.set(parsed.module.ast.name, parsed.module.ast);
    for (const imported of parsed.module.ast.imports) queue.push(imported.module);
  }
  return { modules, diagnostics };
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
  const units = stgToJS(stgConfig, { unitId: "main", moduleName: root }, stg.bindings);
  const jsexe = link(stgConfig, [{ module: { unitId: "main", moduleName: root }, units }]);

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
