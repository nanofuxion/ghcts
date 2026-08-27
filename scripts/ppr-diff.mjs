#!/usr/bin/env node
/**
 * Byte-fidelity check for src/js/ppr.ts against the golden GHC oracle.
 *
 * Renders ghcts's RTS, extracts every top-level `function h$x(...) {...}` that
 * both ghcts and references/miso-lynx/oracle-jsexe/rts.js define, and reports
 * how many are byte-identical.
 *
 *   node scripts/ppr-diff.mjs            # summary + first 3 differing funcs
 *   node scripts/ppr-diff.mjs -n 10      # show 10
 *   node scripts/ppr-diff.mjs --name h$c2
 */
import { readFileSync } from "node:fs";

const ORACLE = "references/miso-lynx/oracle-jsexe/rts.js";
const args = process.argv.slice(2);
const value = (f) => (args.indexOf(f) >= 0 ? args[args.indexOf(f) + 1] : undefined);
const show = Number(value("-n") ?? 3);
const only = value("--name");

/** Top-level `function h$name(...) { ... }` bodies, brace-matched with a
 * string-literal-aware scanner (the RTS has braces inside string literals). */
function topLevelFunctions(src) {
  const out = new Map();
  const re = /(^|\n)function (h\$[A-Za-z0-9_$]+)\(/g;
  for (const m of src.matchAll(re)) {
    const start = m.index + m[1].length;
    let depth = 0, quote = null, i = src.indexOf("{", start), seen = false;
    for (; i < src.length; i++) {
      const c = src[i];
      if (quote) {
        if (c === "\\") i++;
        else if (c === quote) quote = null;
        continue;
      }
      if (c === '"' || c === "'") { quote = c; continue; }
      if (c === "{") { depth++; seen = true; continue; }
      if (c === "}") { depth--; if (seen && depth === 0) break; }
    }
    out.set(m[2], src.slice(start, i + 1));
  }
  return out;
}

function unifiedDiff(name, a, b) {
  const al = a.split("\n"), bl = b.split("\n");
  const lines = [`--- oracle/${name}`, `+++ ghcts/${name}`];
  for (let i = 0; i < Math.max(al.length, bl.length); i++) {
    if (al[i] === bl[i]) lines.push(` ${al[i]}`);
    else {
      if (al[i] !== undefined) lines.push(`-${al[i]}`);
      if (bl[i] !== undefined) lines.push(`+${bl[i]}`);
    }
  }
  return lines.join("\n");
}

const oracle = topLevelFunctions(readFileSync(ORACLE, "utf8"));
const { renderRts } = await import("../dist/stg-js/rts.js");
const ours = topLevelFunctions(renderRts());

const shared = [...oracle.keys()].filter((n) => ours.has(n));
const differing = shared.filter((n) => oracle.get(n) !== ours.get(n));
const same = shared.length - differing.length;

console.log(`${same}/${shared.length} shared functions byte-identical (${((same / shared.length) * 100).toFixed(1)}%)`);
console.log(`${oracle.size} in oracle, ${ours.size} in ghcts, ${shared.length} in both`);

const picked = only ? [only] : differing.slice(0, show);
for (const name of picked) {
  if (!oracle.has(name) || !ours.has(name)) { console.log(`\n${name}: not defined by both`); continue; }
  console.log(`\n${unifiedDiff(name, oracle.get(name), ours.get(name))}`);
}
if (!only && differing.length > show) console.log(`\n... and ${differing.length - show} more differing`);
