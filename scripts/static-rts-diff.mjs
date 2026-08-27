#!/usr/bin/env node
/**
 * Fidelity check for src/stg-js/rts-static.ts against the golden GHC oracle.
 *
 * references/miso-lynx/oracle-jsexe/lib.js is real GHC 9.12.2 output. It holds
 * the rts/js/ sources already run through GHC's own CPP, alongside every other
 * package's JS, so it will not match line for line - but every function the
 * two have in common must have an identical body.
 *
 *   node scripts/static-rts-diff.mjs          # summary + first 3 differing
 *   node scripts/static-rts-diff.mjs -n 10
 *   node scripts/static-rts-diff.mjs --name h$rts_isThreaded
 */
import { readFileSync } from "node:fs";

const ORACLE = "references/miso-lynx/oracle-jsexe/lib.js";
const args = process.argv.slice(2);
const value = (f) => (args.indexOf(f) >= 0 ? args[args.indexOf(f) + 1] : undefined);
const show = Number(value("-n") ?? 3);
const only = value("--name");

/** Top-level `function h$name(...) { ... }` bodies, brace-matched with a
 * scanner that skips string literals and comments (the RTS has braces inside
 * both). */
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
      if (c === '"' || c === "'" || c === "`") { quote = c; continue; }
      if (c === "/" && src[i + 1] === "/") { i = src.indexOf("\n", i); if (i < 0) break; continue; }
      if (c === "/" && src[i + 1] === "*") { i = src.indexOf("*/", i + 2) + 1; continue; }
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
const { renderStaticRts } = await import("../dist/stg-js/rts-static.js");
const ours = topLevelFunctions(renderStaticRts());

const shared = [...ours.keys()].filter((n) => oracle.has(n));
const differing = shared.filter((n) => oracle.get(n) !== ours.get(n));
const same = shared.length - differing.length;

console.log(`${same}/${shared.length} shared functions byte-identical (${((same / shared.length) * 100).toFixed(1)}%)`);
console.log(`${oracle.size} in oracle lib.js, ${ours.size} in ghcts static RTS, ${shared.length} in both`);
const missing = [...ours.keys()].filter((n) => !oracle.has(n));
if (missing.length) console.log(`${missing.length} emitted by ghcts but absent from the oracle: ${missing.slice(0, 10).join(", ")}`);

const picked = only ? [only] : differing.slice(0, show);
for (const name of picked) {
  if (!oracle.has(name) || !ours.has(name)) { console.log(`\n${name}: not defined by both`); continue; }
  console.log(`\n${unifiedDiff(name, oracle.get(name), ours.get(name))}`);
}
if (!only && differing.length > show) console.log(`\n... and ${differing.length - show} more differing`);
