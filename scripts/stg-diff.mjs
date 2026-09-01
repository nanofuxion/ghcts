#!/usr/bin/env node
/**
 * Per-stage differential: ghcts against GHC's own dumps, for the same program.
 *
 *   node scripts/stg-diff.mjs                 # every stage, whole corpus
 *   node scripts/stg-diff.mjs --only add      # one case
 *   node scripts/stg-diff.mjs --stage core    # one stage: core | stg
 *   node scripts/stg-diff.mjs --show add      # both sides, printed
 *
 * TWO STAGES
 *
 * `core` reads `-ddump-simpl` and asks what GHC's Core-to-Core pipeline
 * produced that ours did not: which worker/wrapper splits it made, and how
 * many boxes each binding still allocates. Those are the two things
 * `src/core-opt/` is responsible for, so a gap here names the pass to fix.
 *
 * `stg` reads `-ddump-stg-final` and asks what the backend will see.
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
import { tmpdir } from "node:os";
import { join } from "node:path";

const GHC =
  "/nix/store/pbhncgl2a7y0wlvpc8nxanxf0lhlf074-javascript-unknown-ghcjs-ghc-native-bignum-9.12.2/bin/javascript-unknown-ghcjs-ghc";

const ROOT = "/Volumes/Storage/Projects/ghcts";
// One scratch directory per corpus case, kept between runs so a dump can be
// read by hand after a mismatch.
const WORK = join(tmpdir(), "ghcts-stg-diff");

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
  {
    name: "staticptr",
    // The construct behind every main-thread event handler in miso. On device
    // a `static` handler registers on the first render and never again, so
    // this compares how each compiler lowers the form and its key.
    pragmas: ["{-# LANGUAGE StaticPointers #-}"],
    imports: ["import GHC.StaticPtr (StaticPtr, staticKey, deRefStaticPtr)"],
    source: [
      "handler :: Int -> Int",
      "handler n = n + 1",
      "ptr :: StaticPtr (Int -> Int)",
      "ptr = static handler",
      "useKey :: Int",
      "useKey = length (show (staticKey ptr))",
      "useVal :: Int -> Int",
      "useVal = deRefStaticPtr ptr",
    ],
    want: ["handler", "ptr", "useKey", "useVal"],
  },
  {
    name: "maybeint",
    // Every decoded event field is an optional value scrutinised once. This is
    // the shape `fromJSVal` leaves behind at a known type.
    source: [
      "orZero :: Maybe Int -> Int",
      "orZero Nothing  = 0",
      "orZero (Just n) = n + 1",
    ],
    want: ["orZero", "$worZero"],
  },
  {
    name: "record",
    // A model update: read a field, write it back. The whole BTS dirty-draw
    // path is made of these.
    source: [
      "data M = M { count :: Int, flag :: Bool }",
      "bump :: M -> M",
      "bump m = m { count = count m + 1 }",
    ],
    want: ["bump", "$wbump"],
  },
  {
    name: "listmap",
    // Building a list of results, which is what building a VTree is.
    source: ["bumpAll :: [Int] -> [Int]", "bumpAll xs = map (+ 1) xs"],
    want: ["bumpAll"],
  },
  {
    name: "classctx",
    // A constrained instance at a closed type - the case `Specialise` has to
    // close for `FromJSVal (Maybe a)` to stop going through a dictionary.
    source: [
      "class Dec a where",
      "  dec :: Int -> a",
      "instance Dec Int where",
      "  dec n = n + 1",
      "instance Dec a => Dec (Maybe a) where",
      "  dec n = Just (dec n)",
      "decMaybe :: Int -> Maybe Int",
      "decMaybe n = dec n",
    ],
    want: ["decMaybe"],
  },
];

const args = process.argv.slice(2);
const only = args.includes("--only") ? args[args.indexOf("--only") + 1] : undefined;
const show = args.includes("--show") ? args[args.indexOf("--show") + 1] : undefined;
const stage = args.includes("--stage") ? args[args.indexOf("--stage") + 1] : "all";
const wantCore = stage === "all" || stage === "core";
const wantStg = stage === "all" || stage === "stg";

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
  const { optimiseCore } = await import(join(ROOT, "dist/build.js"));
  const { argStrictness } = await import(join(ROOT, "dist/core-opt/strictness.js"));
  const config = JSON.parse(readFileSync(join(caseDir, "ghcts.json"), "utf8"));
  const loaded = await loadProgram(caseDir, config);
  const el = elaborateProgram(loaded.modules, "Main", "Main.hs");
  const core = desugarModule(el.module, "Main.hs").program;
  const opt = optimiseCore(core);
  return { core: opt, bindings: coreToStg(opt).bindings, strictness: argStrictness(opt) };
}

/** GHC prints one `<...>` per argument in `Str=`. An argument is strict when
 * its demand starts with a use count or `S`; `A` means absent and `L` lazy.
 * Nested parens carry unboxing detail this does not model yet. */
function ghcStrictArgs(str) {
  if (!str) return undefined;
  const out = [];
  let depth = 0;
  let cur = "";
  for (const ch of str) {
    if (ch === "<" && depth++ === 0) { cur = ""; continue; }
    if (ch === ">" && --depth === 0) { out.push(/^[0-9S]/.test(cur)); continue; }
    if (depth > 0) cur += ch;
  }
  return out;
}

/** Parse `-ddump-simpl`. Same block shape as the STG dump: `Name :: Type`,
 * an optional bracketed info line, then `Name = rhs`. Only the binder names
 * and the shape of each right-hand side are read - this is a differential,
 * not a Core reader. */
function parseGhcCore(text) {
  const out = new Map();
  // Blank lines separate nothing useful here: a binding's own info block has
  // them, and a `Rec { ... }` group has none between its members. Every
  // binding is introduced by a `-- RHS size:` comment, so that is the cut.
  for (const chunk of text.split(/^-- RHS size:.*$/m).slice(1)) {
    const first = chunk.split("\n").find((l) => l.trim().length > 0);
    const m = first && /^([A-Za-z0-9_.$'#]+)/.exec(first.trim());
    if (!m) continue;
    const full = m[1];
    // The right-hand side is introduced by a second line starting with the
    // name, after the `::` type and the bracketed info block. GHC breaks
    // before the `=` when the name is long, so find the name line first and
    // the `=` after it - and start looking past `::` so the info block's own
    // `Unf=`/`Tmpl=` are not mistaken for it.
    const at = chunk.indexOf(`\n${full}`, chunk.indexOf("::"));
    const eq = at >= 0 ? chunk.indexOf("=", at) : -1;
    const rhs = eq >= 0 ? chunk.slice(eq + 1) : "";
    out.set(full.replace(/^Main\./, ""), { name: full, rhs, boxes: countBoxes(rhs) });
  }
  return out;
}

/** How many boxes the right-hand side builds. GHC writes a saturated
 * constructor application as `GHC.Types.I# x`, so counting the constructors
 * that wrap an unboxed payload counts the allocations worker/wrapper and
 * case-of-known-constructor are meant to remove. */
// No trailing `\b`: `#` is not a word character, so a boundary after it never
// holds and the whole pattern would silently match nothing.
const BOXES = /(?:GHC\.Types\.)?\b(?:I#|D#|F#|W#|C#)([^\n]*)/g;
/** Allocations only. The same constructor appears in a `case` alternative,
 * where it takes a box apart rather than building one, and counting those
 * would say GHC allocates most where it in fact unboxes most. An alternative
 * is the occurrence followed by a binder and an arrow. */
const countBoxes = (rhs) => {
  let n = 0;
  for (const m of rhs.matchAll(BOXES)) if (!/^\s+[A-Za-z0-9_']+\s*->/.test(m[1])) n++;
  return n;
};

/** The same count off ghcts's Core. ghcts spells the Int box `I` where GHC
 * spells it `I#`, so the type it belongs to is the fact, not the name. */
const BOXED_TYPES = new Set([
  "Int", "Int8", "Int16", "Int32", "Word", "Word8", "Word16", "Word32",
  "Char", "Float", "Double",
]);
function ghctsCoreFacts(program) {
  const out = new Map();
  const count = (e) => {
    if (!e || typeof e !== "object") return 0;
    let n = e.tag === "Con" && BOXED_TYPES.has(e.con.typeName) && e.args.length === 1 ? 1 : 0;
    for (const v of Object.values(e))
      n += Array.isArray(v) ? v.reduce((m, x) => m + count(x), 0) : count(v);
    return n;
  };
  const put = (binder, rhs) => out.set(binder.name, { name: binder.name, boxes: count(rhs) });
  for (const b of program.binds)
    if (b.tag === "NonRec") put(b.binder, b.rhs);
    else for (const [binder, rhs] of b.pairs) put(binder, rhs);
  return out;
}

function runCase(c) {
  const dir = join(WORK, c.name);
  rmSync(dir, { recursive: true, force: true });
  mkdirSync(dir, { recursive: true });
  const src = [
    ...(c.pragmas ?? []),
    "module Main where",
    ...(c.imports ?? []),
    ...c.source,
    "main :: IO ()",
    "main = pure ()",
    "",
  ].join("\n");
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
  execFileSync(
    GHC,
    ["-O2", "-ddump-stg-final", "-ddump-simpl", "-ddump-to-file", "Main.hs", "-o", "m"],
    { cwd: dir, stdio: "ignore" },
  );
  const simpl = join(dir, "Main.dump-simpl");
  return {
    dir,
    ghc: parseGhcStg(readFileSync(join(dir, "Main.dump-stg-final"), "utf8")),
    ghcCore: existsSync(simpl) ? parseGhcCore(readFileSync(simpl, "utf8")) : new Map(),
  };
}

if (!existsSync(GHC)) {
  console.error(`No GHC JS compiler at ${GHC}`);
  process.exit(2);
}
mkdirSync(WORK, { recursive: true });

let compared = 0;
let mismatched = 0;
let strictCompared = 0;
let strictMismatched = 0;
let coreCompared = 0;
let coreMismatched = 0;
const missingWorkers = [];
const missingAnalyses = new Set();

for (const c of CORPUS) {
  if (only && c.name !== only) continue;
  const { dir, ghc, ghcCore } = runCase(c);
  const { core, bindings, strictness } = await ghctsStg(dir);
  const ours = ghctsFacts(bindings);
  const oursCore = ghctsCoreFacts(core);

  if (show === c.name) {
    console.log(`--- GHC ---`);
    for (const [k, v] of ghc) console.log(`  ${k} ${JSON.stringify(v)}`);
    console.log(`--- ghcts ---`);
    for (const [k, v] of ours) console.log(`  ${k} ${JSON.stringify(v)}`);
  }

  console.log(`\n=== ${c.name} ===`);

  if (wantCore) {
    // Which worker/wrapper splits GHC made. A split GHC made and we did not is
    // a boxed argument still crossing a call on the hot path.
    const ghcWorkers = [...ghcCore.keys()].filter((n) => n.startsWith("$w")).sort();
    const ourWorkers = [...oursCore.keys()].filter((n) => n.startsWith("$w")).sort();
    const absent = ghcWorkers.filter((n) => !oursCore.has(n));
    console.log(
      `  [core] workers: GHC ${ghcWorkers.length ? ghcWorkers.join(",") : "none"}` +
        ` vs ghcts ${ourWorkers.length ? ourWorkers.join(",") : "none"}` +
        (absent.length ? `   <-- MISSING ${absent.join(",")}` : ""),
    );
    for (const n of absent) missingWorkers.push(`${c.name}:${n}`);
    for (const want of c.want) {
      const g = ghcCore.get(want);
      const o = oursCore.get(want);
      if (!g || !o) continue;
      coreCompared++;
      const worse = o.boxes > g.boxes;
      if (worse) coreMismatched++;
      console.log(
        `  [core] ${want}: boxes GHC ${g.boxes} vs ghcts ${o.boxes}` +
          (worse ? "   <-- ghcts allocates more" : ""),
      );
    }
  }

  if (!wantStg) continue;
  for (const want_ of c.want) {
    const want = want_;
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
    if (g.str) {
      const want = ghcStrictArgs(g.str);
      const got = strictness.get(want_);
      const fmt = (a) => (a ? a.map((x) => (x ? "S" : "L")).join("") : "?");
      const agree = want && got && want.length === got.length && want.every((x, i) => x === got[i]);
      strictCompared++;
      if (!agree) strictMismatched++;
      console.log(
        `      demand: GHC ${fmt(want)} vs ghcts ${fmt(got)}${agree ? " (agree)" : " <-- DIFFERS"}` +
          `   [GHC Str=${g.str}${g.cpr ? ` Cpr=${g.cpr}` : ""}]`,
      );
    }
  }
}

console.log(`\nstg: compared ${compared}, mismatched ${mismatched}`);
console.log(`core: compared ${coreCompared}, allocating more than GHC ${coreMismatched}`);
if (missingWorkers.length)
  console.log(`core: worker/wrapper splits GHC made and ghcts did not: ${missingWorkers.join(" ")}`);
console.log(`demand signatures compared ${strictCompared}, disagreeing ${strictMismatched}`);
if (missingAnalyses.size)
  console.log(`analyses GHC has and ghcts does not: ${[...missingAnalyses].join(", ")}`);
process.exitCode = mismatched + coreMismatched + missingWorkers.length > 0 ? 1 : 0;
