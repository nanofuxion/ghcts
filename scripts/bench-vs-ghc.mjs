#!/usr/bin/env node
/**
 * Race ghcts's output against GHC's for the same Haskell, on the same engine.
 *
 * Byte-identity says whether we emit what GHC emits. This says whether what
 * we emit runs as fast — the question byte-identity is a proxy for, and the
 * one that actually matters. Both bundles get the same RTS shape, the same
 * entry, and the same node process.
 *
 *   node scripts/bench-vs-ghc.mjs <file.hs> <exportedName>
 */
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync, existsSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, basename } from "node:path";

const GHC_JS = "/nix/store/pbhncgl2a7y0wlvpc8nxanxf0lhlf074-javascript-unknown-ghcjs-ghc-native-bignum-9.12.2/bin/javascript-unknown-ghcjs-ghc";
const file = process.argv[2];
const want = process.argv[3] ?? "answer";
if (!file || !existsSync(file)) { console.error("usage: bench-vs-ghc.mjs <file.hs> [name]"); process.exit(2); }
const source = readFileSync(file, "utf8");

// --- GHC: compile, then run its own all.js and time the value ------------
const work = mkdtempSync(join(tmpdir(), "bench-"));
writeFileSync(join(work, "Main.hs"), `${source}
import GHC.JS.Prim (toJSInt)
foreign import javascript unsafe "((n) => { globalThis.__r = n; })" report :: Int -> IO ()
main :: IO ()
main = report ${want}
`.replace(/^import GHC\.JS\.Prim.*\n/m, ""));
execFileSync(GHC_JS, ["Main.hs", "-o", "out"], { cwd: work, stdio: "pipe" });
const ghcAll = readFileSync(join(work, "out.jsexe", "all.js"), "utf8");

/** GHC's h$main schedules a thread on the JS event loop rather than running
 * it inline, so the value is not there when eval returns - reading it
 * immediately reports `undefined` and times only the parse. Poll until the
 * program has actually produced its answer. */
async function timeIt(label, js) {
  globalThis.__r = undefined;
  const t0 = process.hrtime.bigint();
  try {
    (0, eval)(js);
    for (let i = 0; globalThis.__r === undefined && i < 100000; i++) {
      await new Promise((r) => setImmediate(r));
    }
  } catch (cause) {
    console.log(`${label.padEnd(6)} threw: ${cause instanceof Error ? cause.message.slice(0, 90) : cause}`);
    return undefined;
  }
  const ms = Number(process.hrtime.bigint() - t0) / 1e6;
  console.log(`${label.padEnd(6)} ${String(globalThis.__r).padEnd(12)} ${ms.toFixed(0)} ms`);
  return globalThis.__r === undefined ? undefined : ms;
}

const ghcMs = await timeIt("GHC", ghcAll);

// --- ghcts: same source, our whole pipeline ------------------------------
const { parseModule } = await import("../dist/parser.js");
const { elaborateModule } = await import("../dist/elaborate.js");
const { desugarModule } = await import("../dist/desugar.js");
const { coreToStg } = await import("../dist/core-to-stg.js");
const { stgToJS, renderModule } = await import("../dist/stg-js/codegen.js");
const { renderRts } = await import("../dist/stg-js/rts.js");
const { renderStaticRts } = await import("../dist/stg-js/rts-static.js");
const { defaultStgToJSConfig: config } = await import("../dist/stg-js/types.js");

const parsed = parseModule(source, basename(file));
const elaborated = elaborateModule(parsed.module.ast, basename(file));
const desugared = desugarModule(elaborated.module, basename(file));
const bad = [...(elaborated.diagnostics ?? []), ...desugared.diagnostics].filter((d) => d.severity === "error");
if (bad.length) { for (const d of bad) console.error(`  ${d.code} ${d.message}`); process.exit(1); }
const stg = coreToStg(desugared.program);
const units = stgToJS(config, { unitId: "main", moduleName: "Main" }, stg.bindings);
const out = renderModule(config, units);
const binder = stg.bindings.flatMap((b) => (b.tag === "StgNonRec" ? [b.binder] : b.pairs.map(([x]) => x))).find((b) => b.name === want);
const sym = units.find((u) => u.luIdExports.some((b) => b === binder)).luObjBlock.oiSymbols[0];

// Same shape of entry GHC uses: a stop frame, then enter the closure.
const entry = `
h$stack = new Array(100000); h$sp = 0;
function h$benchStop() { globalThis.__r = h$r1; return null; }
h$benchStop.f = h$benchStop;
h$o(h$benchStop, -1, 0, 0, 0, null);
h$initStatic.forEach(function (f) { f(); }); h$initStatic.length = 0;
(function () {
  h$sp = 0; h$stack[0] = h$benchStop;
  h$r1 = ${sym};
  var c = h$r1.f;
  while (c !== null) c = c();
})();
`;
const oursMs = await timeIt("ghcts", renderRts(config) + "\n" + renderStaticRts(config) + "\n" + out + entry);

if (ghcMs && oursMs) console.log(`\nghcts / GHC = ${(oursMs / ghcMs).toFixed(2)}x`);
