#!/usr/bin/env node
/**
 * Byte-identity corpus for generated *module* code.
 *
 * `scripts/ghc-js-diff.mjs` answers the question for one file. This runs the
 * same comparison over a fixed set of small programs and reports one number:
 * how many top-level `h$` functions ghcts emits byte-for-byte as GHC 9.12.2's
 * JavaScript backend does.
 *
 * Two things make the comparison possible at all:
 *
 *   - the corpus modules carry no `main`. GHC needs one, and its JS linker
 *     only emits what `main` reaches, so a `main` that `seq`s every top-level
 *     binder is appended for GHC's copy only. Without it GHC's out.js
 *     contains nothing from the module and the shared-name set is empty.
 *   - only names both compilers emit are compared. GHC links all of `base`;
 *     ghcts compiles one module with its own Prelude inlined into it. The
 *     names that coincide are exactly the module's own bindings.
 *
 *   node scripts/codegen-corpus.mjs              # the count, plus divergences
 *   node scripts/codegen-corpus.mjs -v           # ... with both bodies
 *   node scripts/codegen-corpus.mjs <name>       # one corpus entry
 */
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync, existsSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const GHC_JS =
  "/nix/store/pbhncgl2a7y0wlvpc8nxanxf0lhlf074-javascript-unknown-ghcjs-ghc-native-bignum-9.12.2/bin/javascript-unknown-ghcjs-ghc";

/** Each entry is a `module Main where` with no `main` - see the header. */
const CORPUS = [
  { name: "arith", source: "add :: Int -> Int -> Int\nadd a b = a + b\n" },
  { name: "arith3", source: "mix :: Int -> Int -> Int\nmix a b = a * b + a\n" },
  { name: "const", source: "konst :: Int -> Int -> Int\nkonst a _ = a\n" },
  { name: "saturated", source: "add :: Int -> Int -> Int\nadd a b = a + b\nuse :: Int -> Int\nuse x = add x x\n" },
  { name: "partial", source: "add :: Int -> Int -> Int\nadd a b = a + b\nplus1 :: Int -> Int\nplus1 = add 1\n" },
  { name: "apply", source: "twice :: (Int -> Int) -> Int -> Int\ntwice f x = f (f x)\n" },
  { name: "datacon", source: "data P = P Int Int\nmkP :: Int -> P\nmkP x = P x x\n" },
  { name: "casealt", source: "data P = P Int Int\nfstP :: P -> Int\nfstP p = case p of P a _ -> a\n" },
  { name: "enum", source: "data C = A | B | D\nrank :: C -> Int\nrank c = case c of\n  A -> 0\n  B -> 1\n  D -> 2\n" },
  { name: "letbind", source: "sq :: Int -> Int\nsq x = let y = x + x in y * y\n" },
  { name: "recursion", source: "count :: Int -> Int\ncount n = if n == 0 then 0 else count (n - 1)\n" },
  { name: "cmp", source: "big :: Int -> Bool\nbig n = n > 10\n" },
  { name: "lambda", source: "mk :: Int -> (Int -> Int)\nmk n = \\x -> x + n\n" },
  { name: "poly", source: "ident :: a -> a\nident x = x\n" },
  { name: "guards", source: "sign :: Int -> Int\nsign n\n  | n > 0 = 1\n  | n < 0 = 0\n  | otherwise = 2\n" },
  { name: "cafthunk", source: "ten :: Int\nten = 5 + 5\n" },
];

const args = process.argv.slice(2);
const verbose = args.includes("-v");
const only = args.find((a) => !a.startsWith("-"));

if (!existsSync(GHC_JS)) {
  console.error(`No GHC JS compiler at ${GHC_JS}.\nIt comes from references/miso-lynx's flake: nix build .#miso-lynx-examples`);
  process.exit(2);
}

const D = new URL("../dist/", import.meta.url).pathname;
const { parseModule } = await import(`${D}parser.js`);
const { elaborateModule } = await import(`${D}elaborate.js`);
const { desugarModule } = await import(`${D}desugar.js`);
const { coreToStg } = await import(`${D}core-to-stg.js`);
const { stgToJS, renderModule } = await import(`${D}stg-js/codegen.js`);
const { defaultStgToJSConfig: config } = await import(`${D}stg-js/types.js`);

/** Top-level `function h$name(...) { ... }` bodies, keyed by name. */
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

const KEYWORDS = new Set(["data", "type", "newtype", "class", "instance", "import", "module", "infixl", "infixr", "infix", "foreign", "where"]);

/** Names bound at column 0. Signature and equation give the same name, so a
 * set is enough; every one of them becomes a link root for GHC. */
const topLevelNames = (src) =>
  [...new Set([...src.matchAll(/^([a-z_][A-Za-z0-9_']*)/gm)].map((m) => m[1]))].filter((n) => !KEYWORDS.has(n));

function ghcCompile(source) {
  const roots = topLevelNames(source);
  const work = mkdtempSync(join(tmpdir(), "corpus-"));
  const main = `main :: IO ()\nmain = ${roots.map((r) => `${r} \`seq\` `).join("")}return ()\n`;
  writeFileSync(join(work, "Main.hs"), `module Main where\n${source}${main}`);
  execFileSync(GHC_JS, ["Main.hs", "-o", "out"], { cwd: work, stdio: "pipe" });
  return readFileSync(join(work, "out.jsexe", "out.js"), "utf8");
}

function ghctsCompile(source) {
  const src = `module Main where\n${source}`;
  const parsed = parseModule(src, "Main.hs");
  const elaborated = elaborateModule(parsed.module.ast, "Main.hs");
  const desugared = desugarModule(elaborated.module, "Main.hs");
  const errors = [...parsed.diagnostics, ...(elaborated.diagnostics ?? []), ...desugared.diagnostics].filter(
    (d) => d.severity === "error",
  );
  if (errors.length) throw new Error(errors.map((d) => `${d.code} ${d.message}`).join("\n"));
  const stg = coreToStg(desugared.program);
  return renderModule(config, stgToJS(config, { unitId: "main", moduleName: "Main" }, stg.bindings));
}

/** The JS linker rewrites every `h$$`-prefixed local symbol to `h$$<hex>`,
 * where the hex is the symbol's FastString unique - a number that exists only
 * inside the GHC process that linked it (GHC.StgToJS.Linker.Opt.ghcjsRenderJsI).
 * ghcts is not a linker and has no such number, so a function that names a
 * local symbol can never match byte-for-byte against a linked out.js. Masking
 * each local symbol by order of first appearance separates that one
 * unreachable difference from real codegen differences; it is reported as its
 * own number and never folded into the byte-identical count. */
function maskLocals(js) {
  const seen = new Map();
  return js.replace(/h\$\$[A-Za-z0-9_$]+/g, (sym) => {
    if (!seen.has(sym)) seen.set(sym, `h$$L${seen.size}`);
    return seen.get(sym);
  });
}

let totalSame = 0;
let totalMasked = 0;
let totalShared = 0;
const divergences = [];

for (const entry of CORPUS) {
  if (only && entry.name !== only) continue;
  let a, b;
  try {
    a = functions(ghcCompile(entry.source));
  } catch (e) {
    console.log(`${entry.name.padEnd(12)} GHC failed: ${String(e.message).split("\n").slice(-3).join(" ")}`);
    continue;
  }
  try {
    b = functions(ghctsCompile(entry.source));
  } catch (e) {
    console.log(`${entry.name.padEnd(12)} ghcts failed: ${e.message}`);
    continue;
  }
  const shared = [...a.keys()].filter((k) => b.has(k));
  const same = shared.filter((k) => a.get(k) === b.get(k));
  const masked = shared.filter((k) => maskLocals(a.get(k)) === maskLocals(b.get(k)));
  totalSame += same.length;
  totalMasked += masked.length;
  totalShared += shared.length;
  console.log(`${entry.name.padEnd(12)} ${same.length}/${shared.length}  (${masked.length}/${shared.length} modulo local-symbol renaming)`);
  for (const k of shared) {
    if (a.get(k) === b.get(k)) continue;
    divergences.push([entry.name, k, a.get(k), b.get(k), maskLocals(a.get(k)) === maskLocals(b.get(k))]);
  }
}

console.log(`\nTOTAL ${totalSame}/${totalShared} byte-identical`);
console.log(`      ${totalMasked}/${totalShared} identical modulo the linker's local-symbol renaming`);
if (divergences.length) {
  console.log(`\n${divergences.length} divergences:`);
  for (const [prog, k, ghc, ours, onlyNames] of divergences) {
    console.log(`  ${prog}: ${k}${onlyNames ? "   [local symbol names only]" : ""}`);
    if (verbose) console.log(`--- GHC\n${ghc}\n--- ghcts\n${ours}\n`);
  }
}
