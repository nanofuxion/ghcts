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
import { cpSync, existsSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
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

// The compiler is copied, not symlinked: a static server that refuses to
// follow a link out of its root answers 404, and the page then evaluates the
// error document as JavaScript.
const compiler = join(root, "dist/ghc.cjs");
if (!existsSync(compiler)) {
  console.error(`${compiler} is missing. Build it first: node build/build-compiler.mjs`);
  process.exit(2);
}
cpSync(compiler, join(out, "ghc.cjs"));
console.log(`${(statSync(compiler).size / 1e6).toFixed(0)} MB -> ${join(out, "ghc.cjs")}`);

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
