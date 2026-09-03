#!/usr/bin/env node
/**
 * Collect a package and everything it needs into one relocatable database.
 *
 * A cabal store's `.conf` files carry absolute paths, which is fine on the
 * machine that built them and useless anywhere else — including inside the
 * playground's virtual filesystem. This copies the closure and rewrites those
 * paths to `${pkgroot}`, the directory holding `package.conf.d`, so the same
 * tree works at `dist/pkgs` on disk and at `/lib/pkgs` in a browser.
 *
 *   node build/build-packages.mjs --db <dir>... --package miso [--out dist/pkgs]
 *
 * Boot packages are left out: they are already in `dist/lib`.
 */
import { spawnSync } from "node:child_process";
import { cpSync, existsSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { findGhcJs } from "../dist/find-ghc.js";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const many = (name) => process.argv.flatMap((a, i) => (a === `--${name}` ? [process.argv[i + 1]] : []));
const one = (name, fallback) => {
  const i = process.argv.indexOf(`--${name}`);
  return i === -1 ? fallback : process.argv[i + 1];
};

const dbs = many("db").filter(existsSync);
const wanted = many("package");
const out = resolve(root, one("out", "dist/pkgs"));
if (dbs.length === 0 || wanted.length === 0) {
  console.error("Usage: build-packages.mjs --db <dir>... --package <name>... [--out dir]");
  process.exit(2);
}

/** Fields start at column 0; their values may continue on indented lines. */
function parseConf(text) {
  const fields = new Map();
  let key;
  for (const line of text.split("\n")) {
    const m = /^([a-z][a-z0-9-]*):(.*)$/i.exec(line);
    if (m) {
      key = m[1];
      fields.set(key, [m[2].trim()].filter(Boolean));
    } else if (key && /^\s+\S/.test(line)) {
      fields.get(key).push(line.trim());
    }
  }
  const words = (k) => (fields.get(k) ?? []).flatMap((v) => v.split(/\s+/)).filter(Boolean);
  return { fields, id: words("id")[0], name: words("name")[0], depends: words("depends"), importDirs: words("import-dirs") };
}

const units = new Map();
for (const db of dbs)
  for (const f of readdirSync(db).filter((f) => f.endsWith(".conf"))) {
    const text = readFileSync(join(db, f), "utf8");
    const unit = parseConf(text);
    // First database named wins, so an inplace build shadows the store.
    if (unit.id && !units.has(unit.id)) units.set(unit.id, { ...unit, text });
  }

/** Anything already in dist/lib is a boot package; the playground has it. */
const bootDb = join(root, "dist/lib/package.conf.d");
const boot = new Set(
  existsSync(bootDb) ? readdirSync(bootDb).filter((f) => f.endsWith(".conf")).map((f) => f.replace(/\.conf$/, "")) : [],
);

// A name can appear more than once — an inplace build and a store copy, or
// two store copies from different compilers. The first database given wins,
// which is why the caller lists the inplace one first.
const closure = new Map();
const queue = wanted.map((name) => [...units.values()].find((u) => u.name === name)?.id).filter(Boolean);
if (queue.length === 0) {
  console.error(`None of ${wanted.join(", ")} is in the given databases.`);
  process.exit(1);
}
while (queue.length) {
  const id = queue.pop();
  if (closure.has(id) || boot.has(id)) continue;
  const unit = units.get(id);
  if (!unit) {
    console.error(`${id} is named as a dependency but is in none of the databases.`);
    process.exit(1);
  }
  closure.set(id, unit);
  queue.push(...unit.depends);
}

/** Ways nothing here links against. Same rule as build-compiler.mjs. */
const unusedWay = (f) => f.endsWith(".p_hi") || f.endsWith("_p.a") || f.includes("_debug") || f.includes("_thr");

rmSync(out, { recursive: true, force: true });
mkdirSync(join(out, "package.conf.d"), { recursive: true });

/**
 * Absolute paths, rewritten to sit under the database wherever it lands.
 * `${pkgroot}` is the directory holding `package.conf.d`, so a package's
 * files are `${pkgroot}/<id>/lib` — the same shape dist/lib's own confs use.
 * The value goes on its own indented line, which is the form ghc-pkg parses.
 */
const RELOCATED = {
  "import-dirs": (id) => `\${pkgroot}/${id}/lib`,
  "library-dirs": (id) => `\${pkgroot}/${id}/lib`,
  "library-dirs-static": (id) => `\${pkgroot}/${id}/lib`,
  "dynamic-library-dirs": (id) => `\${pkgroot}/${id}/lib`,
  "data-dir": (id) => `\${pkgroot}/${id}/share`,
};
const DROPPED = new Set(["haddock-interfaces", "haddock-html", "pkgroot"]);

function relocate(text, id) {
  const out = [];
  let field;
  for (const line of text.split("\n")) {
    const m = /^([a-z][a-z0-9-]*):(.*)$/i.exec(line);
    if (m) {
      field = m[1];
      if (DROPPED.has(field)) continue;
      if (field in RELOCATED) out.push(`${field}:`, `    ${RELOCATED[field](id)}`);
      else out.push(line);
    } else if (/^\s+\S/.test(line)) {
      // A continuation of a field we replaced or dropped goes with it.
      if (field && (DROPPED.has(field) || field in RELOCATED)) continue;
      out.push(line);
    } else {
      out.push(line);
    }
  }
  return out.join("\n");
}

let bytes = 0;
for (const [id, unit] of closure) {
  const from = unit.importDirs[0];
  if (from && existsSync(from)) {
    cpSync(from, join(out, id, "lib"), { recursive: true, filter: (p) => !unusedWay(p) });
    const size = spawnSync("du", ["-sk", join(out, id, "lib")], { encoding: "utf8" }).stdout;
    bytes += Number(size?.split("\t")[0] ?? 0) * 1024;
  }
  writeFileSync(join(out, "package.conf.d", `${id}.conf`), relocate(unit.text, id));
}

// GHC refuses a database that holds .conf files but no package.cache.
const ghcPkg = findGhcJs()?.ghcPkg;
if (!ghcPkg) {
  console.error("No ghc-pkg found, and GHC will not read a database without its cache.");
  process.exit(1);
}
spawnSync("chmod", ["-R", "u+w", out], { stdio: "ignore" });
const recache = spawnSync(ghcPkg, ["recache", `--package-db=${join(out, "package.conf.d")}`], { stdio: "inherit" });
if (recache.status !== 0) process.exit(1);

console.log(`${closure.size} packages, ${(bytes / 1e6).toFixed(0)} MB -> ${out}`);
for (const id of closure.keys()) console.log(`  ${id}`);
