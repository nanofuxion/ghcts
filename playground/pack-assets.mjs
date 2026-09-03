#!/usr/bin/env node
/**
 * Pack libraries into something a browser can fetch: one blob plus an index
 * of {path, offset, size}. The page mounts every entry lazily, so only the
 * files GHC actually opens are ever decoded.
 *
 *   node playground/pack-assets.mjs [--lib dist/lib] [--out playground/assets]
 *
 * `--minimal` keeps only the packages a Prelude program needs (78 MB rather
 * than 147 MB) and always copies `dist/ghc.cjs` alongside it. `--miso` packs
 * a second, separately-fetched blob: `node build/miso-web/build.mjs` first,
 * to produce `dist/pkgs` (miso, ghcjs-base, aeson… — everything web miso
 * needs that is not already a boot package).
 */
import { cpSync, existsSync, mkdirSync, readFileSync, readdirSync, statSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const arg = (n, d) => { const i = process.argv.indexOf(`--${n}`); return i === -1 ? d : process.argv[i + 1]; };
const lib = join(root, arg("lib", "dist/lib"));
const out = join(root, arg("out", "playground/assets"));
mkdirSync(out, { recursive: true });

const allFiles = (dir) => {
  const found = [];
  const walk = (d) => {
    for (const name of readdirSync(d)) {
      const p = join(d, name);
      statSync(p).isDirectory() ? walk(p) : found.push(p);
    }
  };
  walk(dir);
  return found;
};

/** Write one `{name}.bin` + `{name}.json` pair from disk paths and their VFS-relative paths. */
function pack(name, entries) {
  const chunks = [];
  let offset = 0;
  const index = entries.map(({ diskPath, vfsPath }) => {
    const bytes = readFileSync(diskPath);
    chunks.push(bytes);
    const entry = { path: vfsPath, offset, size: bytes.length };
    offset += bytes.length;
    return entry;
  });
  writeFileSync(join(out, `${name}.bin`), Buffer.concat(chunks));
  writeFileSync(join(out, `${name}.json`), JSON.stringify(index));
  console.log(`${index.length} files, ${(offset / 1e6).toFixed(0)} MB -> ${join(out, `${name}.bin`)}`);
  return index;
}

/** What a program that only imports the Prelude actually needs. */
const minimal = /^(base-|ghc-prim-|ghc-internal-|ghc-bignum-|rts-|ghc-boot-th-|integer-gmp-|ghc-platform-)/;

if (process.argv.includes("--minimal") || !process.argv.includes("--miso")) {
  // The compiler is copied, not symlinked: a static server that refuses to
  // follow a link out of its root answers 404, and the page then evaluates
  // the error document as JavaScript.
  const compiler = join(root, "dist/ghc.cjs");
  if (!existsSync(compiler)) {
    console.error(`${compiler} is missing. Build it first: node build/build-compiler.mjs`);
    process.exit(2);
  }
  cpSync(compiler, join(out, "ghc.cjs"));
  console.log(`${(statSync(compiler).size / 1e6).toFixed(0)} MB -> ${join(out, "ghc.cjs")}`);

  const wanted = process.argv.includes("--minimal");
  const kept = allFiles(lib)
    .map((p) => relative(lib, p))
    .filter((p) => {
      const pkg = p.split("/")[1];
      // package.conf.d is shipped in full regardless: it is one shared file
      // per package (~KB, not the .hi/.a payload), and every package this
      // build knows about - including ones only miso.bin's files back - has
      // to be registered somewhere for GHC to resolve `-package miso`'s
      // dependency closure onto boot packages by name.
      return !wanted || !pkg || minimal.test(pkg) || p.startsWith("package.conf.d");
    });
  pack("lib", kept.map((p) => ({ diskPath: join(lib, p), vfsPath: p })));
}

if (process.argv.includes("--miso")) {
  const pkgs = join(root, "dist/pkgs");
  if (!existsSync(pkgs)) {
    console.error(`${pkgs} is missing. Build it first: node build/miso-web/build.mjs`);
    process.exit(2);
  }

  // miso's closure depends on boot packages beyond the --minimal set
  // (bytestring, containers, mtl, text…). Their .conf is already in lib.bin
  // (package.conf.d ships whole); what is missing is their actual .hi/.a,
  // which --minimal left out. Find which ones by reading what dist/pkgs's
  // own packages declare as dependencies.
  const bootIds = new Set(readdirSync(join(lib, "package.conf.d")).filter((f) => f.endsWith(".conf")).map((f) => f.replace(/\.conf$/, "")));
  const minimalIds = new Set([...bootIds].filter((id) => minimal.test(id)));
  /** `depends:` is a list field: often the value starts on the next,
   * indented line, and (once `relocate` in build-packages.mjs has dropped
   * the haddock-* fields that used to follow it) it may be the last field
   * in the file, with nothing after it to mark where the list ends. */
  const confDepends = (text) => {
    const ids = [];
    let inDepends = false;
    for (const line of text.split("\n")) {
      const m = /^depends:(.*)$/.exec(line);
      if (m) { inDepends = true; ids.push(...m[1].trim().split(/\s+/).filter(Boolean)); continue; }
      if (/^\S/.test(line)) { inDepends = false; continue; }
      if (inDepends) ids.push(...line.trim().split(/\s+/).filter(Boolean));
    }
    return ids;
  };
  const confDir = join(pkgs, "package.conf.d");
  const extraBoot = new Set();
  for (const f of readdirSync(confDir).filter((f) => f.endsWith(".conf")))
    for (const id of confDepends(readFileSync(join(confDir, f), "utf8")))
      if (bootIds.has(id) && !minimalIds.has(id)) extraBoot.add(id);

  const entries = [];
  for (const p of allFiles(pkgs)) entries.push({ diskPath: p, vfsPath: `pkgs/${relative(pkgs, p)}` });
  for (const p of allFiles(lib))
    if (extraBoot.has(relative(lib, p).split("/")[1])) entries.push({ diskPath: p, vfsPath: relative(lib, p) });
  console.log(`extra boot packages for miso: ${[...extraBoot].join(", ") || "(none)"}`);
  pack("miso", entries);
}
