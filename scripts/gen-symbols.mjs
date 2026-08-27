import { readFileSync, writeFileSync } from 'node:fs';
const src = readFileSync('references/ghc/compiler/GHC/StgToJS/Symbols.hs','utf8');
const strs = new Map(), skipped = [];
// Every top-level `hdFoo = <literal>` binding. GHC declares the types
// separately - sometimes one signature for a whole comma-separated group -
// so keying off the equation rather than the signature is what catches all
// of them. OverloadedStrings makes the fsLit/name wrapper optional.
for (const m of src.matchAll(/^(hd[A-Za-z0-9_']*)\s*=\s*(.+)$/gm)) {
  const [, n, rhs] = m;
  if (strs.has(n)) continue;
  const lit = rhs.trim().match(/^(?:fsLit\s+|name\s+|mkFastString\s+)?"((?:[^"\\]|\\.)*)"$/);
  if (lit) strs.set(n, { text: JSON.parse(`"${lit[1]}"`) });
  else if (!/^global\b/.test(rhs.trim())) skipped.push(`${n} = ${rhs.trim()}`);
}
const globals = new Map();
for (const m of src.matchAll(/^(hd[A-Za-z0-9_']*)\s*::\s*JStgExpr\s*\n\1\s*=\s*global\s*(?:\(\s*identFS\s+)?([A-Za-z0-9_']+)\s*\)?/gm))
  globals.set(m[1], m[2]);
let out = `/** Ported from GHC/StgToJS/Symbols.hs - the RTS symbol vocabulary.
 *
 * Generated from the Haskell source, so every name and spelling is GHC's own.
 * A \`*Str\` binding is the raw symbol text (a FastString or Ident in GHC);
 * the matching bare binding is that same symbol as a global JStgExpr.
 *
 * Regenerate with scripts/gen-symbols.mjs after updating references/ghc. */
import type { JStgExpr } from "../js/jstg-syntax.js";
import { global } from "../js/jstg-syntax.js";

`;
for (const [n, v] of [...strs].sort((a, b) => a[0].localeCompare(b[0])))
  out += `export const ${n} = ${JSON.stringify(v.text)};\n`;
out += `\n`;
for (const [n, s] of [...globals].sort((a, b) => a[0].localeCompare(b[0])))
  if (strs.has(s)) out += `export const ${n}: JStgExpr = global(${s});\n`;
if (skipped.length)
  out += `\n// Computed in GHC rather than a literal; ported where used:\n` +
    skipped.map((s) => `//   ${s}`).join('\n') + '\n';
writeFileSync('src/stg-js/symbols.ts', out);
console.log('literals', strs.size, 'globals', globals.size, 'computed', skipped.length);
