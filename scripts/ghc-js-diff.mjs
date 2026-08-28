#!/usr/bin/env node
/**
 * Compile the same Haskell with GHC's JavaScript backend and with ghcts, and
 * put the two outputs side by side.
 *
 * The RTS has been compared byte-for-byte for a while, because the oracle
 * bundle shipped one. Generated *module* code never had an oracle: there was
 * no way to make GHC compile the same source. There is now - the nix store
 * holds the exact GHC 9.12.2 JavaScript compiler that produced the oracle, so
 * any .hs file can be built both ways on demand.
 *
 * That makes codegen checkable the way the RTS already was: not "does it run"
 * but "is it what GHC emits".
 *
 *   node scripts/ghc-js-diff.mjs path/to/Thing.hs
 *   node scripts/ghc-js-diff.mjs path/to/Thing.hs --rts    # compare rts.js too
 */
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync, existsSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, basename } from "node:path";

const GHC_JS = "/nix/store/pbhncgl2a7y0wlvpc8nxanxf0lhlf074-javascript-unknown-ghcjs-ghc-native-bignum-9.12.2/bin/javascript-unknown-ghcjs-ghc";

const file = process.argv[2];
if (!file || !existsSync(file)) {
  console.error("usage: ghc-js-diff.mjs <file.hs> [--rts]");
  process.exit(2);
}
if (!existsSync(GHC_JS)) {
  console.error(`No GHC JS compiler at ${GHC_JS}.\nIt comes from references/miso-lynx's flake: nix build .#miso-lynx-examples`);
  process.exit(2);
}

const source = readFileSync(file, "utf8");

// --- GHC ---------------------------------------------------------------
const work = mkdtempSync(join(tmpdir(), "ghcjs-diff-"));
const hs = join(work, "Main.hs");
// GHC needs a main; ghcts has no IO yet, so it gets the module without one.
//
// The appended main has to *reach* every binding, not just exist: GHC's JS
// linker emits only what main can reach, so `main = return ()` leaves out.js
// with nothing of the module in it and nothing to compare. `seq` is enough to
// make a binding a link root whatever its type. Keywords are skipped so a
// `data`/`class` line is not mistaken for a binder.
const KEYWORDS = new Set(["data", "type", "newtype", "class", "instance", "import", "module", "infixl", "infixr", "infix", "foreign", "where", "main"]);
const roots = [...new Set([...source.matchAll(/^([a-z_][A-Za-z0-9_']*)/gm)].map((m) => m[1]))].filter(
  (n) => !KEYWORDS.has(n),
);
const withMain = /^main\s*::/m.test(source)
  ? source
  : `${source}\nmain :: IO ()\nmain = ${roots.map((r) => `${r} \`seq\` `).join("")}return ()\n`;
writeFileSync(hs, withMain);
execFileSync(GHC_JS, [hs, "-o", join(work, "out")], { cwd: work, stdio: "pipe" });
const jsexe = join(work, "out.jsexe");
const ghcOut = readFileSync(join(jsexe, "out.js"), "utf8");
const ghcRts = readFileSync(join(jsexe, "rts.js"), "utf8");

// --- ghcts -------------------------------------------------------------
const { parseModule } = await import("../dist/parser.js");
const { elaborateModule } = await import("../dist/elaborate.js");
const { desugarModule } = await import("../dist/desugar.js");
const { coreToStg } = await import("../dist/core-to-stg.js");
const { stgToJS, renderModule } = await import("../dist/stg-js/codegen.js");
const { renderRts } = await import("../dist/stg-js/rts.js");
const { defaultStgToJSConfig: config } = await import("../dist/stg-js/types.js");

let ours = null;
let failure = null;
try {
  const parsed = parseModule(source, basename(file));
  const elaborated = elaborateModule(parsed.module.ast, basename(file));
  const desugared = desugarModule(elaborated.module, basename(file));
  const errors = [...(elaborated.diagnostics ?? []), ...desugared.diagnostics].filter((d) => d.severity === "error");
  if (errors.length) failure = errors;
  else {
    const stg = coreToStg(desugared.program);
    const units = stgToJS(config, { unitId: "main", moduleName: "Main" }, stg.bindings);
    ours = renderModule(config, units);
  }
} catch (cause) {
  failure = [{ code: "THREW", message: cause instanceof Error ? cause.message : String(cause) }];
}

/** Top-level `function h$name(...) { ... };` bodies, keyed by name. */
function functions(js) {
  const found = new Map();
  const re = /^function (h\$[A-Za-z0-9_$]+)\(/gm;
  for (let m = re.exec(js); m; m = re.exec(js)) {
    let depth = 0, i = m.index;
    for (; i < js.length; i++) {
      if (js[i] === "{") depth++;
      else if (js[i] === "}" && --depth === 0) break;
    }
    found.set(m[1], js.slice(m.index, i + 1));
  }
  return found;
}

if (process.argv.includes("--rts")) {
  const a = functions(ghcRts), b = functions(renderRts(config));
  const shared = [...a.keys()].filter((k) => b.has(k));
  const same = shared.filter((k) => a.get(k) === b.get(k)).length;
  console.log(`rts.js: ${same}/${shared.length} shared functions byte-identical\n`);
}

console.log(`GHC   out.js: ${(ghcOut.length / 1024).toFixed(0)}KB, ${functions(ghcOut).size} functions`);
if (!ours) {
  console.log(`ghcts out.js: cannot compile this yet`);
  for (const d of failure) console.log(`  ${d.code ?? ""} ${d.message}`);
  process.exit(1);
}
console.log(`ghcts out.js: ${(ours.length / 1024).toFixed(0)}KB, ${functions(ours).size} functions\n`);

// GHC links in every reachable base function; ghcts compiles one module. So
// the useful comparison is over the names both emit, not over the totals.
const a = functions(ghcOut), b = functions(ours);
const shared = [...a.keys()].filter((k) => b.has(k));
const same = shared.filter((k) => a.get(k) === b.get(k));
console.log(`${same.length}/${shared.length} shared functions byte-identical`);
for (const k of shared.filter((x) => !same.includes(x)).slice(0, 3)) {
  console.log(`\n--- GHC/${k}\n${a.get(k)}\n--- ghcts/${k}\n${b.get(k)}`);
}
