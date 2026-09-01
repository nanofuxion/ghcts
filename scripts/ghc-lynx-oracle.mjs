#!/usr/bin/env node
/**
 * Salvage a GHC-built miso-native `.jsexe` from a nix build that cannot
 * finish linking.
 *
 * Every miso-native app fails the same way here: `references/miso/cbits/
 * foreign.c` goes through GHC's JS-backend emscripten step, and `wasm-ld`
 * dies with `section too large` - not a misogram-size problem, the plain
 * `counter` example hits it too. That step runs *after* GHC has already
 * written the JS backend's own output to `<exe>.jsexe/{out.js,lib.js,rts.js,
 * out.frefs.js}` - only the C-stub glue (`clibs.wasm`/`.js`) and the final
 * `runmain.js` never get written. `references/miso-lynx/oracle-jsexe` was
 * salvaged by hand from exactly this; this script does the same thing on
 * demand, for any app.
 *
 *   node scripts/ghc-lynx-oracle.mjs <exe-name> <out-dir> -- <nix-build-args...>
 *   node scripts/ghc-lynx-oracle.mjs counter references/miso-lynx/examples/dist/ghc-jsexe -- .#miso-lynx-examples
 *   node scripts/ghc-lynx-oracle.mjs miso-gram /tmp/ghc-misogram-jsexe -- --override-input miso path:../miso
 *     (run the misogram form from inside references/misogram)
 *
 * Runs `nix build --keep-failed <nix-build-args...>`, which fails but leaves
 * its sandbox under `/nix/var/nix/builds/nix-*` - this is a *local*
 * aarch64-darwin build on this host, not a remote/Linux builder, so the
 * directory is right there and readable with no container needed. Finds the
 * newest such sandbox holding `<exe-name>.jsexe/out.js`, copies the four JS
 * files GHC did write, and hand-writes `runmain.js` the way
 * `GHC.StgToJS.Linker.Linker.writeRunMain`'s non-emcc branch would: a single
 * `h$main(h$mainZCZCMainzimain);` call. That symbol is GHC's package-agnostic
 * alias for `Main.main` - stable across apps - not the versioned per-package
 * one `out.js` also carries.
 */
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, writeFileSync, mkdirSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";

const args = process.argv.slice(2);
const sep = args.indexOf("--");
const [exeName, outDir] = sep === -1 ? args : args.slice(0, sep);
const nixArgs = sep === -1 ? [] : args.slice(sep + 1);
if (!exeName || !outDir) {
  console.error("usage: ghc-lynx-oracle.mjs <exe-name> <out-dir> -- <nix-build-args...>");
  process.exit(2);
}

console.error(`running: nix build --keep-failed ${nixArgs.join(" ")}`);
console.error("(expected to fail at the C-stub emscripten link - that failure is what leaves the sandbox behind)");
try {
  execFileSync(
    "nix",
    ["--extra-experimental-features", "nix-command flakes", "build", "--keep-failed", ...nixArgs],
    { stdio: "inherit" },
  );
  console.error("nix build succeeded outright - no salvage needed, use its result/ output directly.");
  process.exit(0);
} catch {
  // Expected: the C-stub link fails. The JS backend's own output is already
  // on disk in the kept sandbox by the time it does.
}

const BUILDS = "/nix/var/nix/builds";
const jsexeRel = `source/dist/build/${exeName}/${exeName}.jsexe`;
const candidates = readdirSync(BUILDS)
  .map((name) => ({ name, path: join(BUILDS, name) }))
  .filter((c) => existsSync(join(c.path, jsexeRel, "out.js")))
  .map((c) => ({ ...c, mtime: statSync(join(c.path, jsexeRel, "out.js")).mtimeMs }))
  .sort((a, b) => b.mtime - a.mtime);

if (candidates.length === 0) {
  console.error(
    `no kept sandbox under ${BUILDS} has ${jsexeRel}/out.js.\n` +
      `Either the build failed before GHC finished compiling, or the sandbox was already garbage-collected - re-run promptly after a failed build.`,
  );
  process.exit(1);
}

const jsexe = join(candidates[0].path, jsexeRel);
console.error(`salvaging from ${jsexe} (mtime ${new Date(candidates[0].mtime).toISOString()})`);

mkdirSync(outDir, { recursive: true });
for (const file of ["out.js", "lib.js", "rts.js", "out.frefs.js"]) {
  writeFileSync(join(outDir, file), readFileSync(join(jsexe, file)));
}

const outJs = readFileSync(join(jsexe, "out.js"), "utf8");
const MAIN_ALIAS = "h$mainZCZCMainzimain";
if (!outJs.includes(MAIN_ALIAS)) {
  console.error(
    `${MAIN_ALIAS} not found in out.js - this app's entry point may not be a plain \`main :: IO ()\` in module Main. ` +
      `Write runmain.js by hand for it, the way references/miso-lynx/oracle-jsexe/runmain.js was.`,
  );
  process.exit(1);
}
writeFileSync(join(outDir, "runmain.js"), `h$main(${MAIN_ALIAS});\n`);
writeFileSync(join(outDir, "NOTES.txt"), "note: emscripten clibs.js omitted (wasm-ld link fails locally on this host, unrelated to JS codegen); runmain.js hand-written per GHC.StgToJS.Linker.Linker.writeRunMain's non-emcc branch\n");

console.error(`wrote ${outDir}/{out.js,lib.js,rts.js,out.frefs.js,runmain.js,NOTES.txt}`);
