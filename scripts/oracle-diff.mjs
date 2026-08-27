#!/usr/bin/env node
/**
 * Compare ghcts's generated RTS against the golden GHC oracle.
 *
 * The oracle is real GHC 9.12.2 JavaScript-backend output for the miso counter
 * (references/miso-lynx/oracle-jsexe). GHC writes `rts.js` from `rts cfg`
 * alone, so it is a self-contained target: every symbol in it is something
 * GHC.StgToJS.Rts.Rts or GHC.StgToJS.Apply generated.
 *
 * Reports symbol-level coverage, which is the acceptance measure for the RTS
 * port. Exact text will differ until the port is complete; the symbol set is
 * what says whether it is complete.
 *
 *   node scripts/oracle-diff.mjs                 # coverage summary
 *   node scripts/oracle-diff.mjs --missing       # list every missing symbol
 *   node scripts/oracle-diff.mjs --family h\$ap   # focus on one family
 */
import { readFileSync, existsSync } from "node:fs";

const ORACLE = "references/miso-lynx/oracle-jsexe/rts.js";
const args = process.argv.slice(2);
const has = (f) => args.includes(f);
const value = (f) => (args.indexOf(f) >= 0 ? args[args.indexOf(f) + 1] : undefined);

/** Symbols a JS file *defines* (as opposed to merely references). */
function definedSymbols(source) {
  const found = new Set();
  // Fresh JSM identifiers (h$RTS_j33y in GHC, h$RTS_3126 here) are arbitrary
  // per-compilation names for block-local temporaries, not RTS symbols. GHC
  // numbers them from a Unique supply and we from a counter, so comparing
  // them measures nothing.
  const fresh = /^h\$RTS_/;
  for (const m of source.matchAll(/^(?:function|var|const|let)\s+(h\$[A-Za-z0-9_$]+)/gm))
    if (!fresh.test(m[1])) found.add(m[1]);
  // GHC also emits `h$foo = function(...)` and info-table registrations.
  for (const m of source.matchAll(/^(h\$[A-Za-z0-9_$]+)\s*=/gm)) if (!fresh.test(m[1])) found.add(m[1]);
  return found;
}

/** Collapse digits so h$ap_1_1 and h$ap_2_2 count as one family. */
const family = (name) => name.replace(/[0-9]+/g, "N");

if (!existsSync(ORACLE)) {
  console.error(`No oracle at ${ORACLE}.\nBuild it with: nix build .#miso-lynx-examples (in references/miso-lynx)`);
  process.exit(2);
}

const oracle = definedSymbols(readFileSync(ORACLE, "utf8"));

let ours = new Set();
try {
  const { renderRts } = await import("../dist/stg-js/rts.js");
  ours = definedSymbols(renderRts());
} catch (cause) {
  console.log(`ghcts RTS not emitting yet (${cause instanceof Error ? cause.message : cause}).`);
  console.log("Reporting the oracle's shape only - this is the target to hit.\n");
}

const families = new Map();
for (const name of oracle) {
  const key = family(name);
  const entry = families.get(key) ?? { total: 0, have: 0, missing: [] };
  entry.total++;
  if (ours.has(name)) entry.have++;
  else entry.missing.push(name);
  families.set(key, entry);
}

const focus = value("--family");
const rows = [...families].filter(([k]) => !focus || k.includes(focus)).sort((a, b) => b[1].total - a[1].total);

const width = Math.max(...rows.map(([k]) => k.length), 8);
console.log(`${"family".padEnd(width)}  have/total`);
for (const [key, entry] of rows) {
  const flag = entry.have === entry.total ? "ok" : "";
  console.log(`${key.padEnd(width)}  ${String(entry.have).padStart(4)}/${String(entry.total).padEnd(4)} ${flag}`);
}

const total = oracle.size;
const have = [...oracle].filter((n) => ours.has(n)).length;
console.log(`\n${have}/${total} RTS symbols (${((have / total) * 100).toFixed(1)}%)`);

const extra = [...ours].filter((n) => !oracle.has(n));
if (extra.length) console.log(`${extra.length} symbols ghcts defines that the oracle does not: ${extra.slice(0, 10).join(", ")}${extra.length > 10 ? ", ..." : ""}`);

if (has("--missing")) {
  const missing = [...oracle].filter((n) => !ours.has(n)).sort();
  console.log(`\nmissing (${missing.length}):`);
  for (const name of missing) console.log(`  ${name}`);
}
