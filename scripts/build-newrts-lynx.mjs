#!/usr/bin/env node
/**
 * Build a Lynx bundle containing nothing but ghcts's new pipeline.
 *
 * Every other bundle in this repo carries the old interpretive runtime -
 * src/runtime.ts's lazy/force/apply, ~30,000 calls of it. This one is the
 * whole point of the port: Haskell compiled through parse -> typecheck ->
 * desugar -> Core -> STG -> stgToJS, linked against ghcts's own RTS, with
 * not a single line of the old path present. The check at the end enforces
 * that rather than trusting it.
 *
 * The program has to be one the frontend can handle today: no type classes,
 * so no Prelude, no do-notation, no Show. It talks to Lynx through a foreign
 * import, which in GHC 9.12 is a JS expression denoting a function - not a
 * GHCJS $1/$r pattern.
 *
 *   node scripts/build-newrts-lynx.mjs
 *   node scripts/pack-lynx.mjs --js dist/newrts/all.js --out dist/newrts/lynx
 */
import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseModule } from "../dist/parser.js";
import { desugarModule } from "../dist/desugar.js";
import { coreToStg } from "../dist/core-to-stg.js";
import { stgToJS, renderModule } from "../dist/stg-js/codegen.js";
import { renderRts } from "../dist/stg-js/rts.js";
import { renderStaticRts } from "../dist/stg-js/rts-static.js";
import { defaultStgToJSConfig } from "../dist/stg-js/types.js";
import { formatDiagnostic } from "../dist/diagnostics.js";

const OUT = "dist/newrts";
const config = defaultStgToJSConfig;

/** Arithmetic the frontend can compile today, plus one foreign call so the
 * result is visible on the device rather than merely computed. */
const source = `module Main where

foreign import javascript unsafe "((n) => { globalThis.__ghctsResult = n; return n; })" report :: Int -> Int

square :: Int -> Int
square x = x * x

sumTo :: Int -> Int
sumTo n = if n < 1 then 0 else n + sumTo (n - 1)

main :: Int
main = report (square 6 + sumTo 10)
`;

const parsed = parseModule(source, "Main.hs");
if (parsed.diagnostics.some((d) => d.severity === "error")) {
  for (const d of parsed.diagnostics) console.error(formatDiagnostic(d));
  process.exit(1);
}
const { program, diagnostics } = desugarModule(parsed.module.ast, "Main.hs");
const fatal = diagnostics.filter((d) => d.severity !== "warning");
if (fatal.length) {
  for (const d of fatal) console.error(formatDiagnostic(d));
  process.exit(1);
}

const stg = coreToStg(program);
const units = stgToJS(config, { unitId: "main", moduleName: "Main" }, stg.bindings);
const out = renderModule(config, units);

/** The symbol codegen actually gave `main`. It is not GHC's
 * h$mainZCZCMainzimain: that is the spelling for a real `main :: IO ()`
 * entering through h$main, and this frontend has no IO yet. */
const mainBinder = stg.bindings
  .flatMap((b) => (b.tag === "StgNonRec" ? [b.binder] : b.pairs.map(([x]) => x)))
  .find((b) => b.name === "main");
if (!mainBinder) { console.error("no `main`"); process.exit(1); }
const mainSymbol = units.find((u) => u.luIdExports.some((b) => b === mainBinder)).luObjBlock.oiSymbols[0];

/** Base's jsbits supplies these platform predicates; rts/js/ calls them at
 * load time but never defines them. A real link gets them from base. */
const baseShim = `
function h$getGlobal(m) { return null; }
function h$isNode() { return typeof process !== 'undefined' && !!(process.versions && process.versions.node); }
function h$isJvm() { return false; }
function h$isJsShell() { return false; }
function h$isJsCore() { return false; }
function h$isBrowser() { return !h$isNode(); }
function h$isGHCJSi() { return false; }
`;

/** GHC's runmain.js. Our frontend has no IO yet, so main is entered directly
 * and its value stashed where the harness and the device can both read it. */
const runmain = `
h$stack = new Array(10000);
h$sp = 0;
function h$stopFrame() { globalThis.__ghctsMain = h$r1; return null; }
h$stopFrame.f = h$stopFrame;
h$o(h$stopFrame, -1, 0, 0, 0, null);
(function () {
  h$sp = 0;
  h$stack[0] = h$stopFrame;
  h$initStatic.forEach(function (f) { f(); });
  h$initStatic.length = 0;
  h$r1 = ${mainSymbol};
  var c = h$r1.f;
  while (c !== null) c = c();
})();
`;

/** Lynx's host contract. Every bundle must expose renderPage and processData
 * on the main thread; miso supplies them from its own JS, and a bare Haskell
 * program has to supply its own. This paints the value main computed, so the
 * proof is something visible on the device rather than a log line. */
const lynxPage = `
globalThis.processData = function () {};
globalThis.renderPage = function () {
  // The load-bearing proof: what the Haskell actually computed, on the device.
  console.error("[ghcts] main = " + globalThis.__ghctsMain + " foreign = " + globalThis.__ghctsResult);
  if (typeof __CreatePage !== "function") return;
  var page = __CreatePage("0", 0);
  var view = __CreateView(0);
  __SetInlineStyles(view, "display:flex;align-items:center;justify-content:center;height:100%;background:#ffa500;");
  var text = __CreateText(0);
  __SetInlineStyles(text, "font-size:96px;color:#000;");
  var raw = __CreateRawText(String(globalThis.__ghctsMain));
  __SetAttribute(text, "text", String(globalThis.__ghctsMain));
  __AppendElement(text, raw);
  __AppendElement(view, text);
  __AppendElement(page, view);
  __FlushElementTree(page);
};
`;

const all =
  baseShim + renderRts(config) + "\n" + renderStaticRts(config) + "\n" + out + runmain + lynxPage;

mkdirSync(OUT, { recursive: true });
const file = join(OUT, "all.js");
writeFileSync(file, all);

// The goal, checked rather than assumed. src/runtime.ts's calling convention
// must not appear anywhere in this bundle.
//
// The negative lookbehind matters: GHC's own RTS is full of JavaScript's
// Function.prototype.apply, and `\b` happily matches the tail of `.apply(`.
// The old runtime called these as bare globals, never as methods.
const oldRuntime = [...all.matchAll(/(?<![.\w$])(lazy|force|apply)\(/g)].length;
const ourRts = [...all.matchAll(/^function h\$/gm)].length;

console.log(`${file}  ${(all.length / 1024).toFixed(0)}KB`);
console.log(`  ${ourRts} h$ functions from ghcts's RTS`);
console.log(`  ${oldRuntime} calls into the old lazy/force/apply runtime`);
if (oldRuntime > 0) {
  console.error("\nFAIL: old runtime present");
  process.exit(1);
}
console.log("\nno old runtime present");
