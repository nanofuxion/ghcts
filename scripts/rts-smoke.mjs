#!/usr/bin/env node
/**
 * Run a swapped bundle under node, far enough to prove the RTS boots.
 *
 * Iterating on the phone costs a minute per attempt; this costs a second. It
 * stubs just enough of Lynx's host surface for the background thread to reach
 * `h$main`, then reports how far evaluation got. A broken RTS fails long
 * before that - while the RTS's own top-level declarations evaluate, or on
 * the first closure the program allocates.
 *
 *   node scripts/rts-swap.mjs && node scripts/rts-smoke.mjs
 */
import { readFileSync } from "node:fs";

const file = process.argv[2] ?? "dist/rts-swap/all.js";
const source = readFileSync(file, "utf8");

/** Minimal Lynx host surface. Enough to boot; not enough to render. */
const listeners = new Map();
const context = {
  dispatchEvent: (e) => (listeners.get(e?.type) ?? []).forEach((f) => f(e)),
  addEventListener: (n, f) => listeners.set(n, [...(listeners.get(n) ?? []), f]),
  removeEventListener: () => {},
};
Object.assign(globalThis, {
  __BACKGROUND__: true,
  __MAIN_THREAD__: false,
  lynx: {
    getCoreContext: () => context,
    getJSContext: () => context,
    requestAnimationFrame: (f) => setTimeout(() => f(0), 0),
    cancelAnimationFrame: (id) => clearTimeout(id),
    reportError: () => {},
    fetch: () => Promise.reject(new Error("no network in smoke test")),
  },
  requestAnimationFrame: (f) => setTimeout(() => f(0), 0),
  cancelAnimationFrame: (id) => clearTimeout(id),
  processData: () => {},
});

const started = Date.now();
let outcome = "ok";
try {
  // Indirect eval, so the RTS's top-level `var h$...` declarations land on
  // globalThis where the probes below (and the program itself) expect them.
  // `new Function(source)()` would scope them to that function instead.
  (0, eval)(source);
} catch (cause) {
  outcome = `threw: ${cause instanceof Error ? `${cause.name}: ${cause.message}` : String(cause)}`;
}

const rts = globalThis;
const probes = {
  "h$stack allocated": Array.isArray(rts.h$stack) || rts.h$stack === null,
  "h$sp defined": typeof rts.h$sp === "number",
  "h$apply table": Array.isArray(rts.h$apply) || typeof rts.h$apply === "function",
  "h$c1 callable": typeof rts.h$c1 === "function",
  "h$mainLoop present": typeof rts.h$mainLoop === "function",
  "threads ran": rts.h$currentThread !== undefined,
};

console.log(`${file}  (${(source.length / 1024 / 1024).toFixed(2)}MB)  ${Date.now() - started}ms`);
console.log(`evaluation: ${outcome}`);
for (const [what, ok] of Object.entries(probes)) console.log(`  ${ok ? "yes" : "NO "}  ${what}`);
process.exit(outcome === "ok" ? 0 : 1);
