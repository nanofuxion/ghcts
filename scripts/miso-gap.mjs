#!/usr/bin/env node
/**
 * How far is the new pipeline from compiling miso's counter?
 *
 * Resolves the counter against the real references/miso/src, elaborates the
 * whole closure, and histograms what comes back. The point is to work from a
 * current count rather than from memory: this is the list of things standing
 * between ghcts's own codegen and the RTS it already reproduces.
 *
 *   node scripts/miso-gap.mjs           # histogram
 *   node scripts/miso-gap.mjs --sample  # with example messages per bucket
 */
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join, relative } from "node:path";
import { parseModule } from "../dist/parser.js";
import { elaborateProgram } from "../dist/elaborate.js";

const COUNTER = "references/miso-lynx/examples/counter/Main.hs";
const ROOTS = ["references/miso-lynx/examples/counter", "references/miso/src"];

function walk(dir, out = []) {
  for (const e of readdirSync(dir)) {
    const p = join(dir, e);
    if (statSync(p).isDirectory()) walk(p, out);
    else if (p.endsWith(".hs")) out.push(p);
  }
  return out;
}

const modules = new Map();
for (const root of ROOTS) {
  for (const file of walk(root)) {
    const parsed = parseModule(readFileSync(file, "utf8"), relative(".", file));
    if (parsed.module?.ast) modules.set(parsed.module.ast.name, parsed.module.ast);
  }
}
console.log(`${modules.size} modules parsed`);

const result = elaborateProgram(modules, "Main", COUNTER);
const errors = (result.diagnostics ?? []).filter((d) => d.severity === "error");
console.log(`${errors.length} errors\n`);

/** Bucket by the shape of the message, not its particulars. */
const bucket = (m) =>
  m.replace(/`[^`]*`/g, "`_`")
   .replace(/'[^']*'/g, "'_'")
   .replace(/\b[A-Z][A-Za-z0-9_.]*\b/g, "T")
   .replace(/\d+/g, "N")
   .slice(0, 72);

const counts = new Map();
for (const e of errors) {
  const k = bucket(e.message);
  const seen = counts.get(k) ?? { n: 0, eg: e.message };
  seen.n++;
  counts.set(k, seen);
}
const rows = [...counts].sort((a, b) => b[1].n - a[1].n);
for (const [k, v] of rows.slice(0, 14)) {
  console.log(`${String(v.n).padStart(5)}  ${k}`);
  if (process.argv.includes("--sample")) console.log(`       e.g. ${v.eg.slice(0, 110)}`);
}
