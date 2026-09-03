#!/usr/bin/env node
/**
 * Build `dist/ghc.js` — GHC itself as one JavaScript file — from a GHC
 * JavaScript-target installation, and the trimmed `dist/lib/` that compiled
 * programs need.
 *
 * See build/README.md. Run once per GHC version; nothing at runtime needs
 * Haskell, nix, or a native toolchain.
 *
 *   node build/build-compiler.mjs [--ghc <binary|bindir>] [--out dist] [--no-lib]
 */
import { spawnSync } from "node:child_process";
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { findGhcJs, ghcInstallAt } from "../dist/find-ghc.js";

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "..");
const arg = (name, fallback) => {
  const i = process.argv.indexOf(`--${name}`);
  return i === -1 ? fallback : process.argv[i + 1];
};

const wanted = arg("ghc");
const install = wanted ? ghcInstallAt(wanted) : findGhcJs();
if (!install) {
  console.error(
    "No javascript-unknown-ghcjs-ghc found.\n" +
      "Looked at GHCTS_GHC, then PATH, then ghcup. Set GHCTS_GHC, or pass --ghc <binary|bindir>.",
  );
  process.exit(2);
}
const { ghc, libdir, ghcPkg } = install;
const out = resolve(root, arg("out", "dist"));
/** Packages that exist only to build the compiler, and ways nothing links. */
const buildOnly = /^(ghc-\d|Cabal|Cabal-syntax|haddock|xhtml|ghc-heap)/;
const unusedWay = (f) => f.endsWith(".p_hi") || f.endsWith("_p.a") || f.includes("_debug") || f.includes("_thr");

const run = (cmd, args, opts = {}) => {
  const r = spawnSync(cmd, args, { stdio: "inherit", ...opts });
  if (r.status !== 0) {
    console.error(`\n${cmd} failed (${r.status ?? r.signal})`);
    process.exit(1);
  }
};

console.log(`GHC     ${ghc} (${install.version})`);
console.log(`libdir  ${libdir}`);
console.log(`out     ${out}\n`);

// 1. Link the driver. `-ddisable-js-c-sources` is what keeps this pure
//    JavaScript: without it the link shells out to emcc.
mkdirSync(out, { recursive: true });
let work;
if (process.argv.includes("--lib-only")) {
  console.log("keeping the existing ghc.cjs (--lib-only)");
} else {
  work = mkdtempSync(join(tmpdir(), "ghcts-build-"));
  cpSync(join(here, "Driver.hs"), join(work, "Driver.hs"));
  console.log("linking the GHC API driver (this takes a few minutes)...");
  run(ghc, ["-package", "ghc", "-O0", "-ddisable-js-c-sources", "-o", "driver", "Driver.hs"], { cwd: work });

  // 2. The bundle plus the one shim it needs to start.
  const bundle = join(work, "driver.jsexe", "all.js");
  writeFileSync(join(out, "ghc.cjs"), readFileSync(join(here, "jsbi-shim.js"), "utf8") + readFileSync(bundle, "utf8"));
  console.log(`\nwrote ${join(out, "ghc.cjs")} (${(statSync(join(out, "ghc.cjs")).size / 1e6).toFixed(0)} MB)`);
}

// 3. The libdir a compiled program needs: boot packages only, one way each.
if (!process.argv.includes("--no-lib")) {
  const dst = join(out, "lib");
  // A GHC installation may be read-only (nix serves them that way), so a
  // previous run's copy cannot simply be deleted.
  if (existsSync(dst)) {
    run("chmod", ["-R", "u+w", dst], { stdio: "ignore" });
    rmSync(dst, { recursive: true, force: true });
  }
  console.log("copying the boot libraries...");
  cpSync(libdir, dst, {
    recursive: true,
    filter: (src) => {
      // <libdir>/<compiler-id>/<package>/...
      const pkg = src.slice(libdir.length + 1).split("/")[1];
      if (pkg && buildOnly.test(pkg)) return false;
      return !unusedWay(src);
    },
  });
  // The copy inherits the source's permissions; ghc-pkg has to rewrite the cache.
  run("chmod", ["-R", "u+w", dst], { stdio: "ignore" });
  // The package database caches absolute paths from the source installation.
  if (!ghcPkg) {
    console.error(`\n${ghc} has no ghc-pkg beside it, so the copied database cannot be recached.`);
    process.exit(1);
  }
  run(ghcPkg, ["recache", `--package-db=${join(dst, "package.conf.d")}`]);
  const size = spawnSync("du", ["-sm", dst], { encoding: "utf8" }).stdout?.split("\t")[0] ?? "?";
  console.log(`wrote ${dst} (${size} MB)`);
}

if (work) rmSync(work, { recursive: true, force: true });
console.log("\ndone. `node dist/cli.js --ghcts-version`");
