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

/** A counter's update function, in Haskell, without a Prelude.
 *
 * The point is to enter Haskell on every tap - that is the counter's hot path
 * and the only thing that measures whether this is actually faster. `step`
 * does real work (a recursive sum) so a tap is not measuring an empty call. */
const source = `module Main where

step :: IntPrim -> IntPrim
step n = primIntAdd n 1

work :: IntPrim -> IntPrim
work n = step n
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

/** The symbol codegen gave a binding. Not GHC's h$mainZCZCMainzimain - that
 * is the spelling for a real `main :: IO ()` entering through h$main, which
 * this frontend cannot produce yet. */
function symbolFor(name) {
  const binder = stg.bindings
    .flatMap((b) => (b.tag === "StgNonRec" ? [b.binder] : b.pairs.map(([x]) => x)))
    .find((b) => b.name === name);
  if (!binder) { console.error(`no \`${name}\``); process.exit(1); }
  return units.find((u) => u.luIdExports.some((b) => b === binder)).luObjBlock.oiSymbols[0];
}
const workSymbol = symbolFor("work");

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

/** Entering Haskell from JavaScript, GHC's way.
 *
 * A one-argument call puts the closure in R1 and the argument in R2 and goes
 * through h$ap_1_1_fast, which returns the next thing to enter; the
 * trampoline runs until a stop frame returns null. h$ap_1_1 itself is a stack
 * frame, not a callable - calling it directly is the mistake to avoid. */
const runmain = `
h$stack = new Array(10000);
h$sp = 0;
var h$callResult;
function h$stopFrame() { h$callResult = h$r1; return null; }
h$stopFrame.f = h$stopFrame;
h$o(h$stopFrame, -1, 0, 0, 0, null);
h$initStatic.forEach(function (f) { f(); });
h$initStatic.length = 0;

globalThis.__ghctsCall1 = function (fn, x) {
  h$sp = 0;
  h$stack[0] = h$stopFrame;
  h$r1 = fn;
  h$r2 = x;
  var c = h$ap_1_1_fast();
  while (c !== null) c = c();
  return h$callResult;
};
globalThis.__ghctsWork = ${workSymbol};
`;

/** Lynx's host contract. Every bundle must expose renderPage and processData
 * on the main thread; miso supplies them from its own JS, and a bare Haskell
 * program has to supply its own. This paints the value main computed, so the
 * proof is something visible on the device rather than a log line. */
const lynxPage = `
globalThis.processData = function () {};
var count = 0;
var textEl = null;
var timeEl = null;

/** Tap handler: enter Haskell, repaint. This is the loop the old runtime
 * spent ~7.5 seconds in. */
function bump() {
  var t0 = Date.now();
  count = globalThis.__ghctsCall1(globalThis.__ghctsWork, count);
  var ms = Date.now() - t0;
  if (textEl) __SetAttribute(textEl, "text", String(count));
  if (timeEl) __SetAttribute(timeEl, "text", ms + " ms in Haskell");
  __FlushElementTree(globalThis.__ghctsPage);
}

globalThis.onTap = function () { bump(); };
globalThis.renderPage = function () {
  // console.log, never console.error: Lynx's JSErrorReporter escalates every
  // console.error into a reported error - red banner, error_code 1101 - so a
  // diagnostic logged that way ships as a permanent fault.
  console.log("[ghcts] main = " + globalThis.__ghctsMain + " foreign = " + globalThis.__ghctsResult);
  if (typeof __CreatePage !== "function") return;
  var page = __CreatePage("0", 0);
  globalThis.__ghctsPage = page;

  var view = __CreateView(0);
  __SetInlineStyles(view, "display:flex;flex-direction:column;align-items:center;justify-content:center;padding:56px;");

  var label = __CreateText(0);
  __SetInlineStyles(label, "font-size:14px;color:#888;letter-spacing:1px;");
  __SetAttribute(label, "text", "HASKELL ON GHC RTS");

  textEl = __CreateText(0);
  __SetInlineStyles(textEl, "font-size:96px;color:#111;margin-top:12px;");
  __SetAttribute(textEl, "text", String(count));

  timeEl = __CreateText(0);
  __SetInlineStyles(timeEl, "font-size:15px;color:#888;margin-top:12px;");
  __SetAttribute(timeEl, "text", "not run yet");

  var button = __CreateView(0);
  __SetInlineStyles(button, "margin-top:40px;padding:22px 64px;background:#ffa500;border-radius:14px;");
  var buttonText = __CreateText(0);
  __SetInlineStyles(buttonText, "font-size:26px;color:#111;");
  __SetAttribute(buttonText, "text", "step");
  __AppendElement(button, buttonText);
  // Lynx takes a worklet object, not a handler name: the fourth argument is
  // { type: 'worklet', value: fn }. Passing the string "onTap" registers a
  // listener that dispatches and then finds nothing to call - which looks
  // exactly like the event never arriving. This is how miso does it
  // (ts/miso/native/mts/context.ts).
  __AddEvent(button, "bindEvent", "tap", "onTap");

  __AppendElement(view, label);
  __AppendElement(view, textEl);
  __AppendElement(view, timeEl);
  __AppendElement(view, button);
  __AppendElement(page, view);
  __FlushElementTree(page);

  // Lynx's tap plumbing is miso's job, not the compiler's, and wiring it by
  // guesswork is not what this demo is for. Drive the same Haskell entry
  // point from a timer too, so the device reports a real number either way:
  // 200 entries into Haskell, timed, every second.
  setInterval(function () {
    var t0 = Date.now();
    for (var i = 0; i < 200; i++) count = globalThis.__ghctsCall1(globalThis.__ghctsWork, count);
    var us = ((Date.now() - t0) * 1000) / 200;
    __SetAttribute(textEl, "text", String(count));
    __SetAttribute(timeEl, "text", us.toFixed(1) + " us per call into Haskell");
    __FlushElementTree(page);
  }, 1000);
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
