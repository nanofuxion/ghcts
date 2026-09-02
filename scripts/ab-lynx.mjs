#!/usr/bin/env node
/** Build and benchmark the Miso/Lynx micro-apps with one repeatable command.
 * GHC oracle bundles are optional: pass --oracle-root DIR when salvaged
 * bundles exist below DIR/<app>/all.js. */
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";

const ROOT = resolve(new URL("..", import.meta.url).pathname);
const EXAMPLES = join(ROOT, "references/miso-lynx/examples");
const apps = ["vtree", "hydrate", "eqcheck", "decode"];
const args = process.argv.slice(2);
const oracleAt = args.indexOf("--oracle-root");
const oracleRoot = oracleAt >= 0 ? resolve(args[oracleAt + 1]) : undefined;

function run(file, argv, cwd = ROOT) {
  return execFileSync(file, argv, { cwd, encoding: "utf8", stdio: ["ignore", "pipe", "inherit"] });
}

function report(bundle) {
  return JSON.parse(run(process.execPath, [join(ROOT, "scripts/runtime-report.mjs"), "--json", bundle]));
}

function bench(bundle) {
  const out = run(process.execPath, [join(ROOT, "scripts/lynx-run.mjs"), "--thread", "mts", "--ms", "5000", "--bench", "3", "--tap-key", "bench", bundle]);
  const m = /per-tap=([0-9.]+)ms/.exec(out);
  if (!m) throw new Error(`benchmark output did not contain per-tap: ${out}`);
  return Number(m[1]);
}

const rows = [];
for (const app of apps) {
  const project = join(EXAMPLES, app);
  run(process.execPath, [join(ROOT, "dist/cli.js"), "build", "--project", project]);
  const ghctsBundle = join(project, "dist/jsexe/all.js");
  const ghcts = { ms: bench(ghctsBundle), ...report(ghctsBundle) };
  const oracleCandidates = oracleRoot ? [
    join(oracleRoot, app, "all.js"),
    join(oracleRoot, app, "out.js"),
    join(oracleRoot, app, "dist/jsexe/all.js"),
    join(oracleRoot, app, "dist/ghc-jsexe/out.js"),
  ] : [];
  const oracle = oracleCandidates.find((candidate) => existsSync(candidate));
  const ghc = oracle && existsSync(oracle) ? { ms: bench(oracle), ...report(oracle) } : undefined;
  rows.push({ app, ghcts, ghc });
}

console.log("app       ghcts-ms  ghc-ms  ratio  ghcts-closures  ghc-closures  ghcts-decoders  ghc-decoders");
for (const { app, ghcts, ghc } of rows) {
  const ratio = ghc ? (ghcts.ms / ghc.ms).toFixed(2) : "-";
  console.log(`${app.padEnd(9)} ${ghcts.ms.toFixed(2).padStart(8)}  ${(ghc?.ms.toFixed(2) ?? "-").padStart(6)}  ${ratio.padStart(5)}  ${String(ghcts.closureAllocations).padStart(14)}  ${String(ghc?.closureAllocations ?? "-").padStart(12)}  ${String(ghcts.marshalDecoders).padStart(14)}  ${String(ghc?.marshalDecoders ?? "-").padStart(12)}`);
}
