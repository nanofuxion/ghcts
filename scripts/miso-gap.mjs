#!/usr/bin/env node
/**
 * How far is the new pipeline from compiling miso's counter?
 *
 * Loads the counter through `loadProgram` - the same entry `build` uses - so
 * the measurement sees exactly the source roots, the CPP defines and the
 * reachability closure the real build sees. Anything less measures a program
 * nobody compiles: reading the roots by hand once undercounted by hundreds,
 * and dropping the defines made every `#ifdef GHCJS_NEW` in miso's FFI take
 * its #else branch, so names that do exist looked missing.
 *
 *   node scripts/miso-gap.mjs           # histogram
 *   node scripts/miso-gap.mjs --sample  # with example messages per bucket
 */
import { readFileSync } from "node:fs";
import { loadProgram } from "../dist/build.js";
import { elaborateProgram } from "../dist/elaborate.js";

const PROJECT = "references/miso-lynx/examples";
const config = JSON.parse(readFileSync(`${PROJECT}/ghcts.json`, "utf8"));

const { modules, diagnostics } = await loadProgram(PROJECT, config);
console.log(`${modules.size} modules parsed`);

const result = elaborateProgram(modules, config.entry.module, `${PROJECT}/counter/Main.hs`);
const errors = [...diagnostics, ...(result.diagnostics ?? [])].filter((d) => d.severity === "error");
console.log(`${errors.length} errors\n`);

/** Bucket by the shape of the message, not its particulars. A type-mismatch
 * message carries the two types it could not unify - which is what makes it
 * actionable - so the bucket is what comes before the colon. */
const bucket = (m) =>
  m.replace(/:.*$/s, "")
   .replace(/`[^`]*`/g, "`_`")
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
