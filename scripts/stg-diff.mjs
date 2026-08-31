#!/usr/bin/env node
/**
 * Per-stage differential: ghcts's STG against GHC's own, for the same program.
 *
 *   node scripts/stg-diff.mjs                 # the whole corpus
 *   node scripts/stg-diff.mjs --only add      # one case
 *   node scripts/stg-diff.mjs --show add      # both sides, printed
 *
 * WHY FACTS AND NOT TEXT
 *
 * GHC's `-ddump-stg-final` is a pretty-print in GHC's own syntax; ghcts's STG
 * is a TypeScript value. Diffing the two as text would report formatting, so
 * this compares the facts a backend actually reads off a binding:
 *
 *   kind    function | thunk | constructor  (which entry convention it gets)
 *   arity   how many arguments it takes before it does any work
 *   head    what its body does first - a call, a primop, a case, an allocation
 *   str     GHC's demand signature, e.g. <1!P(L)><1!P(L)>
 *   cpr     GHC's constructed-product result signature
 *
 * `str` and `cpr` have no ghcts counterpart yet, which is the point: they are
 * the analyses `src/core-opt/strictness.ts` currently approximates, and seeing
 * them side by side says exactly how far off the approximation is.
 *
 * The corpus is deliberately tiny. Each program isolates one lowering
 * decision, so a mismatch names the stage that made it rather than needing a
 * whole app to reproduce.
 */
import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, rmSync, writeFileSync, existsSync } from "node:fs";
import { join } from "node:path";

const GHC =
  "/nix/store/pbhncgl2a7y0wlvpc8nxanxf0lhlf074-javascript-unknown-ghcjs-ghc-native-bignum-9.12.2/bin/javascript-unknown-ghcjs-ghc";

const ROOT = "/Volumes/Storage/Projects/ghcts";
const WORK = "/private/tmp/claude-501/-Volumes-Storage-Projects-ghcts/03a5683c-f40f-40b1-896a-7ff7ed635f14/scratchpad/stgdiff";

/** Each case is one module. `main` is supplied so GHC links, and is ignored by
 * the comparison - only the named bindings are compared. */
const CORPUS = [
  {
    name: "add",
    // The simplest dictionary method at a known type. GHC's STG shows whether
    // it kept the class method or specialised it away.
    source: ["add :: Int -> Int -> Int", "add a b = a + b"],
    want: ["add"],
  },
  {
    name: "loop",
    // Self-recursion over Int: the worker/wrapper case.
    source: [
      "sumTo :: Int -> Int -> Int",
      "sumTo acc 0 = acc",
      "sumTo acc n = sumTo (acc + n) (n - 1)",
    ],
    want: ["sumTo", "$wsumTo"],
  },
  {
    name: "thunk",
    // Thunk vs function vs constructor, and the update flag that follows.
    // A literal list is not used here: GHC splits it into nums1..nums5, so the
    // source name survives on neither side and the case would compare nothing.
    source: [
      "expensive :: Int -> Int",
      "expensive n = n * n + n",
      "lazyPair :: Int -> (Int, Int)",
      "lazyPair n = (expensive n, n)",
    ],
    want: ["expensive", "lazyPair"],
  },
  {
    name: "lazyarg",
    // Strict in the first argument only. The demand signature is the fact.
    source: ["konst :: Int -> Int -> Int", "konst a _ = a"],
    want: ["konst"],
  },
  {
    name: "datacon",
    // Constructor allocation and a case on it.
    source: [
      "data P = P Int Int",
      "mk :: Int -> P",
      "mk x = P x x",
      "fstP :: P -> Int",
      "fstP (P a _) = a",
    ],
    want: ["mk", "fstP"],
  },
];

const args = process.argv.slice(2);
const only = args.includes("--only") ? args[args.indexOf("--only") + 1] : undefined;
const show = args.includes("--show") ? args[args.indexOf("--show") + 1] : undefined;

/** Parse `-ddump-stg-final`. Bindings are separated by a blank line; the head
 * line is `Name :: Type`, then a bracketed info line, then the right-hand
 * side after `=`. */
function parseGhcStg(text) {
  const out = new Map();
  // A binding is a blank-line-separated block: `Name :: Type`, then the
  // bracketed info line ending in `=`, then the right-hand side. Splitting on
  // unindented lines instead would cut the name away from its own flags.
  const blocks = text.split(/\n\s*\n/);
  for (const block of blocks) {
    // `Name :: Type`, but an inline pragma can sit between them and push the
    // `::` onto the next line: `Main.sumTo [InlPrag=[2]]\n  :: Int -> ...`.
    const m = /^([A-Za-z0-9_.$']+)(?:\s*\[[^\]]*\])?\s*::/.exec(block)
      || /^([A-Za-z0-9_.$']+)\s*\[InlPrag[^\n]*\n\s*::/.exec(block);
    if (!m) continue;
    const full = m[1];
    const name = full.replace(/^Main\./, "");
    // The flags run from the first `[` to the `] =` that ends the info line.
    // A character-class scan stops early, because `Unf=OtherCon []` puts a
    // `]` inside the flags.
    const cut = block.indexOf("] =");
    const open = block.indexOf("[");
    const flags = cut > open && open >= 0 ? block.slice(open + 1, cut) : "";
    const arity = /Arity=(\d+)/.exec(flags);
    // A demand signature contains commas and brackets of its own, so stop at
    // the next `, Key=` rather than at the next comma.
    const field = (k) => {
      const m = new RegExp(k + "=(.*?)(?:, [A-Z][A-Za-z]*=|$)", "s").exec(flags);
      return m ? m[1].trim() : undefined;
    };
    const str = field("Str");
    const cpr = field("Cpr");
    // The right-hand side: everything after the first `=` at the end of the
    // info line.
    const rhs = block.slice(block.indexOf("] =") + 3).trim();
    out.set(name, {
      name,
      arity: arity ? Number(arity[1]) : undefined,
      str,
      cpr,
      kind: ghcKind(rhs),
      head: ghcHead(rhs),
      rhs,
    });
  }
  return out;
}

/** `{fvs} \r [args] body` is a function, `\u []` a thunk, `Con! [..]` an
 * allocation. */
function ghcKind(rhs) {
  if (/^\S+!\s*\[/.test(rhs)) return "con";
  const lam = /\\([ruse]+)\s*\[([^\]]*)\]/.exec(rhs);
  if (!lam) return "other";
  return lam[2].trim().length > 0 ? "function" : "thunk";
}

function ghcHead(rhs) {
  const conAlloc = /^([A-Za-z0-9_.$']+)!\s*\[/.exec(rhs.trim());
  if (conAlloc) return `con:${short(conAlloc[1])}`;
  const body = rhs.replace(/^\{[^}]*\}\s*/, "").replace(/\\[ruse]+\s*\[[^\]]*\]\s*/, "").trim();
  if (/^case\b/.test(body)) return "case";
  if (/^let\b/.test(body)) return "let";
  // `Con! [..]` at the top of a binding, but plain `Con [..]` inside a lambda:
  // the bang marks a top-level allocation, not constructor-ness.
  const con = /^([A-Za-z0-9_.$']+)!?\s*\[/.exec(body);
  if (con && /^[A-Z:]/.test(short(con[1]))) return `con:${short(con[1])}`;
  const call = /^([A-Za-z0-9_.$'#]+)/.exec(body);
  if (call) return /#$/.test(call[1]) ? `prim:${call[1]}` : `call:${short(call[1])}`;
  return "?";
}

const short = (n) => n.replace(/^.*\./, "");

/** The same facts, read off ghcts's own STG. */
function ghctsFacts(bindings) {
  const out = new Map();
  const put = (binder, rhs) => {
    const kind =
      rhs.tag === "StgRhsCon" ? "con" : rhs.args.length > 0 ? "function" : "thunk";
    out.set(binder.name, {
      name: binder.name,
      arity: rhs.tag === "StgRhsCon" ? 0 : rhs.args.length,
      str: undefined, // ghcts computes no demand signature
      cpr: undefined, // nor a CPR signature
      kind,
      head: rhs.tag === "StgRhsCon" ? `con:${short(rhs.con.name)}` : ghctsHead(rhs.body),
      rhs: "",
    });
  };
  for (const b of bindings) {
    if (b.tag === "StgNonRec") put(b.binder, b.rhs);
    else for (const [binder, rhs] of b.pairs) put(binder, rhs);
  }
  return out;
}

function ghctsHead(e) {
  switch (e.tag) {
    case "StgCase":
      return "case";
    case "StgLet":
    case "StgLetNoEscape":
      return "let";
    case "StgApp":
      return `call:${short(e.fn.name)}`;
    case "StgConApp":
      return `con:${short(e.con.name)}`;
    case "StgOpApp":
      return `prim:${e.op.op ?? e.op.tag}`;
    case "StgLit":
      return "lit";
    default:
      return "?";
  }
}

async function ghctsStg(caseDir) {
  const { loadProgram, deriveCabalConfig } = await import(join(ROOT, "dist/build.js"));
  const { elaborateProgram } = await import(join(ROOT, "dist/elaborate.js"));
  const { desugarModule } = await import(join(ROOT, "dist/desugar.js"));
  const { coreToStg } = await import(join(ROOT, "dist/core-to-stg.js"));
  const { inlineKnownCalls } = await import(join(ROOT, "dist/core-opt/inline.js"));
  const { forceStrictArgs } = await import(join(ROOT, "dist/core-opt/strictness.js"));
  const config = JSON.parse(readFileSync(join(caseDir, "ghcts.json"), "utf8"));
  const loaded = await loadProgram(caseDir, config);
  const el = elaborateProgram(loaded.modules, "Main", "Main.hs");
  const core = desugarModule(el.module, "Main.hs").program;
  return coreToStg(forceStrictArgs(inlineKnownCalls(core))).bindings;
}

function runCase(c) {
  const dir = join(WORK, c.name);
  rmSync(dir, { recursive: true, force: true });
  mkdirSync(dir, { recursive: true });
  const src = ["module Main where", ...c.source, "main :: IO ()", "main = pure ()", ""].join("\n");
  writeFileSync(join(dir, "Main.hs"), src);
  writeFileSync(
    join(dir, "ghcts.json"),
    JSON.stringify({
      version: 1,
      sourceRoots: ["."],
      entry: { module: "Main", export: "main" },
      targets: ["node"],
      outDir: "dist",
    }),
  );
  execFileSync(GHC, ["-O2", "-ddump-stg-final", "-ddump-to-file", "Main.hs", "-o", "m"], {
    cwd: dir,
    stdio: "ignore",
  });
  return { dir, ghc: parseGhcStg(readFileSync(join(dir, "Main.dump-stg-final"), "utf8")) };
}

if (!existsSync(GHC)) {
  console.error(`No GHC JS compiler at ${GHC}`);
  process.exit(2);
}
mkdirSync(WORK, { recursive: true });

let compared = 0;
let mismatched = 0;
const missingAnalyses = new Set();

for (const c of CORPUS) {
  if (only && c.name !== only) continue;
  const { dir, ghc } = runCase(c);
  const ours = ghctsFacts(await ghctsStg(dir));

  if (show === c.name) {
    console.log(`--- GHC ---`);
    for (const [k, v] of ghc) console.log(`  ${k} ${JSON.stringify(v)}`);
    console.log(`--- ghcts ---`);
    for (const [k, v] of ours) console.log(`  ${k} ${JSON.stringify(v)}`);
  }

  console.log(`\n=== ${c.name} ===`);
  for (const want of c.want) {
    const g = ghc.get(want);
    const o = ours.get(want);
    if (!g && !o) continue;
    compared++;
    if (!g) {
      console.log(`  ${want}: ghcts only (GHC has no such binding)`);
      mismatched++;
      continue;
    }
    if (!o) {
      console.log(`  ${want}: MISSING in ghcts   GHC: kind=${g.kind} arity=${g.arity} head=${g.head}`);
      mismatched++;
      continue;
    }
    const diffs = [];
    // A non-function carries no Arity flag; that is the same fact as arity 0.
    const arityOf = (f) => (f.arity === undefined ? 0 : f.arity);
    if (arityOf(g) !== arityOf(o)) diffs.push(`arity: GHC ${arityOf(g)} vs ghcts ${arityOf(o)}`);
    if (g.kind !== o.kind) diffs.push(`kind: GHC ${g.kind} vs ghcts ${o.kind}`);
    // Two compilers name binders differently, so a body that just returns one
    // of its own arguments reads as the same head on both sides.
    const headOf = (f, self) =>
      f.head.startsWith("call:") && !f.head.startsWith(`call:${self}`) && /^[a-z]/.test(f.head.slice(5))
        ? "call:<local>"
        : f.head;
    if (headOf(g, want) !== headOf(o, want))
      diffs.push(`head: GHC ${g.head} vs ghcts ${o.head}`);
    for (const field of ["str", "cpr"])
      if (g[field] !== undefined && o[field] === undefined) missingAnalyses.add(field);
    if (diffs.length === 0) console.log(`  ${want}: match (kind=${g.kind} arity=${g.arity} head=${g.head})`);
    else {
      mismatched++;
      console.log(`  ${want}: ${diffs.join("; ")}`);
    }
    if (g.str) console.log(`      GHC Str=${g.str}${g.cpr ? ` Cpr=${g.cpr}` : ""}   ghcts: none`);
  }
}

console.log(`\ncompared ${compared}, mismatched ${mismatched}`);
if (missingAnalyses.size)
  console.log(`analyses GHC has and ghcts does not: ${[...missingAnalyses].join(", ")}`);
process.exitCode = mismatched > 0 ? 1 : 0;
