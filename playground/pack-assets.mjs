#!/usr/bin/env node
/**
 * Pack the boot libraries into something a browser can fetch: one blob plus
 * an index of {path, offset, size}. The page mounts every entry lazily, so
 * only the files GHC actually opens are ever decoded.
 *
 *   node playground/pack-assets.mjs [--lib dist/lib] [--out playground/assets]
 *
 * `--minimal` keeps only the packages a Prelude program needs, which is what
 * makes the download 78 MB instead of 147 MB.
 */
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const arg = (n, d) => { const i = process.argv.indexOf(`--${n}`); return i === -1 ? d : process.argv[i + 1]; };
const lib = join(root, arg("lib", "dist/lib"));
const out = join(root, arg("out", "playground/assets"));

/** What a program that only imports the Prelude actually needs. */
const minimal = /^(base-|ghc-prim-|ghc-internal-|ghc-bignum-|rts-|ghc-boot-th-|integer-gmp-|ghc-platform-)/;
const wanted = process.argv.includes("--minimal");

const files = [];
const walk = (dir) => {
  for (const name of readdirSync(dir)) {
    const p = join(dir, name);
    const st = statSync(p);
    if (st.isDirectory()) walk(p);
    else if (st.isFile()) files.push({ path: relative(lib, p), size: st.size });
  }
};
walk(lib);

const kept = files.filter((f) => {
  const pkg = f.path.split("/")[1];
  return !wanted || !pkg || !f.path.includes("/") || minimal.test(pkg) || f.path.startsWith("package.conf.d") || !f.path.includes("/");
});

mkdirSync(out, { recursive: true });
const chunks = [];
let offset = 0;
const index = kept.map((f) => {
  const bytes = readFileSync(join(lib, f.path));
  chunks.push(bytes);
  const entry = { path: f.path, offset, size: bytes.length };
  offset += bytes.length;
  return entry;
});
writeFileSync(join(out, "lib.bin"), Buffer.concat(chunks));
writeFileSync(join(out, "lib.json"), JSON.stringify(index));
console.log(`${index.length} files, ${(offset / 1e6).toFixed(0)} MB -> ${join(out, "lib.bin")}`);
