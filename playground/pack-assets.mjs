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
 * needs that is not already a boot package). It also writes `pkgs.json`, the
 * module-to-package index the page reads to decide whether a program needs
 * that blob at all.
 */
import { copyFileSync, existsSync, mkdirSync, readFileSync, readdirSync, statSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const arg = (n, d) => { const i = process.argv.indexOf(`--${n}`); return i === -1 ? d : process.argv[i + 1]; };
const lib = join(root, arg("lib", "dist/lib"));
const out = join(root, arg("out", "playground/assets"));
mkdirSync(out, { recursive: true });

// GHC's RTS names a `JSBI` polyfill nothing defines. build-compiler.mjs
// prepends it to the compiler; a *compiled program* needs it just as much, so
// the page prepends the same file to whatever it just built. One copy, one
// source of truth.
copyFileSync(join(root, "build/jsbi-shim.js"), join(out, "jsbi-shim.js"));

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

// Cloudflare Pages refuses any deployed file over 25 MiB, and these blobs
// are hundreds of MB. Split each one into `${path}.0`, `${path}.1`, … plus
// a `${path}.chunks.json` naming how many parts to fetch and reassemble;
// the offsets in `{name}.json` still index into the blob as a whole, so
// nothing downstream of pack() needs to know it was ever split.
const CHUNK = 20 * 1024 * 1024;
function writeChunked(path, buffer) {
  const n = Math.max(1, Math.ceil(buffer.length / CHUNK));
  for (let i = 0; i < n; i++) writeFileSync(`${path}.${i}`, buffer.subarray(i * CHUNK, (i + 1) * CHUNK));
  writeFileSync(`${path}.chunks.json`, String(n));
  return n;
}

/** Write one chunked `{name}.bin.*` + `{name}.json` pair from disk paths and their VFS-relative paths. */
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
  const binPath = join(out, `${name}.bin`);
  const n = writeChunked(binPath, Buffer.concat(chunks));
  writeFileSync(join(out, `${name}.json`), JSON.stringify(index));
  console.log(`${index.length} files, ${(offset / 1e6).toFixed(0)} MB -> ${binPath} (${n} chunk${n === 1 ? "" : "s"})`);
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
  const compilerOut = join(out, "ghc.cjs");
  const n = writeChunked(compilerOut, readFileSync(compiler));
  console.log(`${(statSync(compiler).size / 1e6).toFixed(0)} MB -> ${compilerOut} (${n} chunks)`);

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
  /** A `.conf` list field (`depends:`, `exposed-modules:`): the value often
   * starts on the next, indented line, and (once `relocate` in
   * build-packages.mjs has dropped the haddock-* fields that used to follow
   * it) it may be the last field in the file, with nothing after it to mark
   * where the list ends. */
  const confList = (text, field) => {
    const items = [];
    let inside = false;
    for (const line of text.split("\n")) {
      const m = new RegExp(`^${field}:(.*)$`).exec(line);
      if (m) { inside = true; items.push(...m[1].trim().split(/\s+/).filter(Boolean)); continue; }
      if (/^\S/.test(line)) { inside = false; continue; }
      if (inside) items.push(...line.trim().split(/\s+/).filter(Boolean));
    }
    return items;
  };
  const confName = (text) => /^name:\s*(\S+)/m.exec(text)?.[1];
  const confDir = join(pkgs, "package.conf.d");
  const extraBoot = new Set();
  for (const f of readdirSync(confDir).filter((f) => f.endsWith(".conf")))
    for (const id of confList(readFileSync(join(confDir, f), "utf8"), "depends"))
      if (bootIds.has(id) && !minimalIds.has(id)) extraBoot.add(id);

  // Template Haskell runs a splice in GHC's own interpreter, which is the
  // `ghci` package and everything under it - linked at compile time, so its
  // files have to be here even though no program imports them.
  const libConf = (id) => readFileSync(join(lib, "package.conf.d", `${id}.conf`), "utf8");
  const closure = (roots) => {
    const seen = new Set();
    const todo = [...roots];
    while (todo.length) {
      const id = todo.pop();
      if (!bootIds.has(id) || seen.has(id)) continue;
      seen.add(id);
      todo.push(...confList(libConf(id), "depends"));
    }
    return seen;
  };
  const ghci = [...bootIds].find((id) => id.startsWith("ghci-"));
  if (!ghci) {
    console.error(`${lib}/package.conf.d has no ghci package, so Template Haskell cannot run.`);
    process.exit(2);
  }
  for (const id of closure([ghci])) if (!minimalIds.has(id)) extraBoot.add(id);

  // What the page needs to decide, *before* fetching 120 MB, whether this
  // blob has anything a given program wants: which module comes from which
  // package, over everything the blob ships. `expose` are the ones that live
  // in this database and so need `-package name` on the command line; the
  // boot packages are already registered globally and only need their files.
  const index = { expose: [], boot: [], modules: {} };
  const addConf = (text, list) => {
    const name = confName(text);
    if (!name) return;
    list.push(name);
    for (const mod of confList(text, "exposed-modules"))
      if (/^[A-Z][A-Za-z0-9_.']*$/.test(mod)) index.modules[mod] = name;
  };
  for (const f of readdirSync(confDir).filter((f) => f.endsWith(".conf")))
    addConf(readFileSync(join(confDir, f), "utf8"), index.expose);
  for (const id of extraBoot)
    addConf(readFileSync(join(lib, "package.conf.d", `${id}.conf`), "utf8"), index.boot);


  // A `dist/pkgs-<ref>` is a second miso, for projects whose cabal.project
  // pins that one (see build/miso-web/build.mjs --ref). Each is its own small
  // blob, fetched only when a project asks for it, and holds only miso: its
  // dependencies are the ones `pkgs` already carries.
  index.alternates = {};
  const defaultMiso = readdirSync(confDir).find((f) => f.startsWith("miso-") && f.endsWith(".conf"));
  for (const dir of readdirSync(join(root, "dist")).filter((d) => d.startsWith("pkgs-"))) {
    const ref = dir.slice("pkgs-".length);
    const from = join(root, "dist", dir);
    const conf = readdirSync(join(from, "package.conf.d")).find((f) => f.startsWith("miso-") && f.endsWith(".conf"));
    if (!conf) {
      console.error(`${from} has no miso package; skipping`);
      continue;
    }
    // The same build the default database already carries. Recording it would
    // cost every project that pins this revision an 11 MB fetch for a package
    // it has.
    if (conf === defaultMiso) {
      console.error(`${ref} is what dist/pkgs holds; not packing it twice`);
      continue;
    }
    pack(`miso-${ref}`, allFiles(from).map((p) => ({ diskPath: p, vfsPath: `${dir}/${relative(from, p)}` })));
    index.alternates[ref] = { blob: `miso-${ref}`, db: dir, id: conf.replace(/\.conf$/, "") };
  }

  const entries = [];
  for (const p of allFiles(pkgs)) entries.push({ diskPath: p, vfsPath: `pkgs/${relative(pkgs, p)}` });
  for (const p of allFiles(lib))
    if (extraBoot.has(relative(lib, p).split("/")[1])) entries.push({ diskPath: p, vfsPath: relative(lib, p) });
  console.log(`extra boot packages for miso: ${[...extraBoot].join(", ") || "(none)"}`);
  pack("miso", entries);

  writeFileSync(join(out, "pkgs.json"), JSON.stringify(index));
  console.log(
    `${index.expose.length} packages, ${Object.keys(index.modules).length} modules, ` +
      `alternates ${Object.keys(index.alternates).join(", ") || "(none)"} -> ${join(out, "pkgs.json")}`,
  );
}
