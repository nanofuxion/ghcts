#!/usr/bin/env node
/**
 * Build miso for the *web* and turn it into a relocatable package database
 * the playground can mount.
 *
 * The cabal store already holds miso, but built with `+native` — that is the
 * LynxJS backend, which renders through Lynx rather than the DOM. Web miso is
 * the same package with no flags at all, so only miso and ghcjs-base are
 * rebuilt here; aeson, vector and the rest are reused from the store.
 *
 *   node build/miso-web/build.mjs                # references/miso -> dist/pkgs
 *   node build/miso-web/build.mjs --ref 1.10.0   # that tag -> dist/pkgs-1.10.0
 *
 * `--ref` builds a second miso from a git ref of the same repository, for
 * projects whose `cabal.project` pins an older one. Only miso itself is kept:
 * its dependencies are the same builds the default database already holds, so
 * the two databases are stacked and the pinned `-package-id` picks the miso.
 *
 * The compiler must be the one that produced `dist/lib`, or the interfaces
 * will not match. Point `GHCTS_GHC` at it.
 */
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { findGhcJs, ghcInstallAt } from "../../dist/find-ghc.js";

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "..", "..");

/** The exact ghcjs-base miso pins (references/miso/nix/source.nix). */
const GHCJS_BASE = "https://github.com/ghcjs/ghcjs-base";
const GHCJS_BASE_REV = "b7ae2cafb082ff247d29ab50d651f4e955ada47a";

const run = (cmd, args, opts = {}) => {
  const r = spawnSync(cmd, args, { stdio: "inherit", ...opts });
  if (r.status !== 0) {
    console.error(`\n${cmd} ${args.join(" ")} failed (${r.status ?? r.signal})`);
    process.exit(1);
  }
};
const capture = (cmd, args, opts = {}) => spawnSync(cmd, args, { encoding: "utf8", ...opts }).stdout?.trim() ?? "";

const arg = (name) => {
  const i = process.argv.indexOf(`--${name}`);
  return i === -1 ? undefined : process.argv[i + 1];
};

const install = arg("ghc") ? ghcInstallAt(arg("ghc")) : findGhcJs();
if (!install) {
  console.error("No javascript-unknown-ghcjs-ghc found. Set GHCTS_GHC or pass --ghc <binary|bindir>.");
  process.exit(2);
}

// The interfaces this produces are read next to dist/lib's, so the compiler
// has to be the same one. Its libdir names the compiler id; dist/lib carries
// a copy of that directory.
const compilerId = readdirSync(join(root, "dist/lib")).find((f) => f.startsWith("javascript-ghcjs-ghc-"));
if (!compilerId) {
  console.error("dist/lib has no javascript-ghcjs-ghc-* directory. Run build/build-compiler.mjs first.");
  process.exit(2);
}
if (!existsSync(join(install.libdir, compilerId))) {
  console.error(
    `${install.ghc} is GHC ${install.version}, whose libdir has no ${compilerId}.\n` +
      `dist/lib was built by a different compiler. Point GHCTS_GHC at the one that produced it.`,
  );
  process.exit(2);
}

// 1. ghcjs-base, at miso's pinned revision, with the one fix it needs to
//    build under GHC 9.12 (see ghcjs-base-ghc912.patch).
const src = join(here, "ghcjs-base");
if (!existsSync(src)) {
  console.log(`cloning ghcjs-base @ ${GHCJS_BASE_REV.slice(0, 8)}`);
  run("git", ["init", "-q", src]);
  run("git", ["remote", "add", "origin", GHCJS_BASE], { cwd: src });
  run("git", ["fetch", "-q", "--depth", "1", "origin", GHCJS_BASE_REV], { cwd: src });
  run("git", ["checkout", "-q", "FETCH_HEAD"], { cwd: src });
}
const patch = join(here, "ghcjs-base-ghc912.patch");
if (spawnSync("git", ["apply", "--check", patch], { cwd: src }).status === 0) {
  console.log("patching ghcjs-base for GHC 9.12");
  run("git", ["apply", patch], { cwd: src });
}

// 1b. A `--ref` build gets its own worktree of references/miso and its own
//     cabal project beside it, so the default build's dist-newstyle is left
//     alone and the two can coexist.
const ref = arg("ref");
const projectDir = ref ? join(here, `alt-${ref}`) : here;
if (ref) {
  const worktree = join(here, `miso-${ref}`);
  if (!existsSync(worktree)) {
    console.log(`checking out miso ${ref}`);
    run("git", ["worktree", "add", "-f", "--detach", worktree, ref], { cwd: join(root, "references/miso") });
  }
  // An old miso may need a fix to build or run under this compiler, the same
  // way ghcjs-base does. `miso-<ref>.patch` beside this script is applied if
  // it is there.
  const fix = join(here, `miso-${ref}.patch`);
  if (existsSync(fix) && spawnSync("git", ["apply", "--check", fix], { cwd: worktree }).status === 0) {
    console.log(`patching miso ${ref}`);
    run("git", ["apply", fix], { cwd: worktree });
  }
  mkdirSync(projectDir, { recursive: true });
  writeFileSync(
    join(projectDir, "cabal.project"),
    readFileSync(join(here, "cabal.project"), "utf8")
      .replace("../../references/miso", `../miso-${ref}`)
      .replace("./ghcjs-base", "../ghcjs-base"),
  );
}

// 2. Point cabal at the same compiler.
const hsc2hs = ["javascript-unknown-ghcjs-hsc2hs", `javascript-unknown-ghcjs-hsc2hs-ghc-${install.version}`]
  .map((f) => join(dirname(install.ghc), f))
  .find((p) => existsSync(p));
writeFileSync(
  join(projectDir, "cabal.project.local"),
  [
    `with-compiler: ${install.ghc}`,
    ...(install.ghcPkg ? [`with-hc-pkg: ${install.ghcPkg}`] : []),
    ...(hsc2hs ? ["program-locations", `  hsc2hs-location: ${hsc2hs}`] : []),
    "",
  ].join("\n"),
);

// 3. Build miso. ghcjs-base comes with it; everything else is already in the
//    store from an earlier build against this same compiler.
console.log(`building miso${ref ? ` ${ref}` : ""} for the web with GHC ${install.version}`);
run("cabal", ["build", "miso"], { cwd: projectDir });

// 4. Collect miso's closure into a relocatable database.
// The store keeps one directory per compiler ABI, and this machine has more
// than one for 9.12.2. Only the ABI that matches dist/lib can be linked
// against: its unit ids are the ones dist/lib's boot packages carry.
const abi = compilerId.replace(/^javascript-ghcjs-ghc-/, "");
const storeDir = capture("cabal", ["path", "--store-dir"], { cwd: projectDir });
const storeDb = [join(storeDir, `ghc-${abi}`, "package.db")].filter(existsSync);
if (storeDb.length === 0) {
  console.error(`No cabal store for ghc-${abi}; miso's dependencies were built by another compiler.`);
  process.exit(1);
}
const inplaceDb = join(projectDir, "dist-newstyle", "packagedb", `ghc-${install.version}`);

const outDir = join(root, ref ? `dist/pkgs-${ref}` : "dist/pkgs");
run("node", [
  join(root, "build/build-packages.mjs"),
  ...[inplaceDb, ...storeDb].flatMap((d) => ["--db", d]),
  "--package",
  "miso",
  "--out",
  outDir,
]);

// 5. An alternate keeps only miso. Its dependencies came from the same store
//    as the default database's, with the same unit ids, so shipping them
//    twice would only make the download bigger.
if (ref) {
  const confs = join(outDir, "package.conf.d");
  for (const id of readdirSync(outDir)) {
    if (id === "package.conf.d" || id.startsWith("miso-")) continue;
    if (!existsSync(join(root, "dist/pkgs", id))) continue;
    rmSync(join(outDir, id), { recursive: true, force: true });
    rmSync(join(confs, `${id}.conf`), { force: true });
  }
  run(install.ghcPkg, ["recache", `--package-db=${confs}`]);
  const kept = readdirSync(confs).filter((f) => f.endsWith(".conf"));
  console.log(`wrote ${outDir} (${kept.join(", ")})`);
}
