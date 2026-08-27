#!/usr/bin/env node
/**
 * Compile real Haskell source all the way to JavaScript and run it.
 *
 * parse -> typecheck -> desugar -> Core -> STG -> stgToJS -> renderRts, then
 * evaluate under the same trampoline `scripts/stg-run.mjs` uses. That script
 * proves codegen against hand-built STG; this one proves the frontend that
 * now produces that STG.
 *
 *   node scripts/hs-run.mjs                 # run the built-in programs
 *   node scripts/hs-run.mjs --print         # also show the generated JS
 *   node scripts/hs-run.mjs file.hs         # compile and run one file
 *
 * The language is the class-free fragment src/desugar.ts documents: integer
 * literals are Int#, arithmetic is primops, Bool is 0/1. `main` is entered as
 * a thunk and whatever lands in R1 is reported.
 */
import { readFileSync } from "node:fs";
import { renderRts } from "../dist/stg-js/rts.js";
import { stgToJS, renderModule } from "../dist/stg-js/codegen.js";
import { defaultStgToJSConfig } from "../dist/stg-js/types.js";
import { parseModule } from "../dist/parser.js";
import { checkModule } from "../dist/typecheck.js";
import { desugarModule } from "../dist/desugar.js";
import { coreToStg } from "../dist/core-to-stg.js";
import { formatDiagnostic } from "../dist/diagnostics.js";

const show = process.argv.includes("--print");
const config = defaultStgToJSConfig;
const rts = renderRts(config);

/** The hand-written half of GHC's RTS that emitted code touches, transcribed
 * from references/ghc/rts/js/*.js, plus a trampoline and a stop frame.
 * Identical to scripts/stg-run.mjs's. */
const bootstrap = `
function h$o(o, typ, a, size, regs, srefs) {
  h$setObjInfo(o, typ, "", [], a, size, regs, srefs);
}
function h$setObjInfo(o, typ, name, fields, a, size, regs, srefs) {
  o.t = typ; o.i = fields; o.n = name; o.a = a;
  o.r = regs; o.s = srefs; o.m = 0; o.size = size;
}
function h$init_closure(c, xs) {
  c.m = 0;
  switch(xs.length) {
    case 0: c.d1 = null;  c.d2 = null;   return c;
    case 1: c.d1 = xs[0]; c.d2 = null;   return c;
    case 2: c.d1 = xs[0]; c.d2 = xs[1];  return c;
    default:
      c.d1 = xs[0]; c.d2 = {};
      for (var i = 1; i < xs.length; i++) c.d2["d" + i] = xs[i];
      return c;
  }
}
var h$staticDelayed = [];
function h$sti(i, c, xs) { i.f = c; h$init_closure(i, xs); }
function h$stc(i, c, xs) { i.f = c; h$init_closure(i, xs); h$addCAF(i); }
function h$d()   { var c = h$c(null); h$staticDelayed.push(c); return c; }
function h$di(c) { h$staticDelayed.push(c); }
function h$p(x)  { h$staticDelayed.push(x); return x; }
function h$addCAF(o) { h$CAFs.push(o); h$CAFsReset.push([o.f, o.d1, o.d2]); }
function h$static_thunk(f) {
  var h = { f: f, d1: null, d2: null, m: 0 };
  h$CAFs.push(h); h$CAFsReset.push(f); return h;
}

h$stack = new Array(10000);
h$sp = 0;
function h$rs() { return h$stack[h$sp]; }
var h$testResult;
function h$stopFrame() { h$testResult = h$r1; return null; }
h$stopFrame.f = h$stopFrame;
h$o(h$stopFrame, -1, 0, 0, 0, null);
function h$runEntry(c) {
  h$sp = 0;
  h$stack[0] = h$stopFrame;
  h$testResult = undefined;
  while (c !== null) c = c();
  return h$testResult;
}
`;

/** parse -> ... -> JS. Returns the emitted module and `main`'s symbol. */
function compile(source, file) {
  const parsed = parseModule(source, file);
  if (parsed.diagnostics.some((d) => d.severity === "error")) {
    throw new Error(parsed.diagnostics.map(formatDiagnostic).join("\n"));
  }
  const ast = parsed.module.ast;
  const typed = checkModule(ast, file);
  const desugared = desugarModule(ast, file);
  const stg = coreToStg(desugared.program);
  const units = stgToJS(config, { unitId: "main", moduleName: ast.name }, stg.bindings);
  const emitted = renderModule(config, units);
  const mainBinder = stg.bindings
    .flatMap((b) => (b.tag === "StgNonRec" ? [b.binder] : b.pairs.map(([x]) => x)))
    .find((b) => b.name === "main");
  if (!mainBinder) throw new Error(`${file}: no \`main\``);
  const unit = units.find((u) => u.luIdExports.some((b) => b === mainBinder));
  return {
    emitted,
    symbol: unit.luObjBlock.oiSymbols[0],
    diagnostics: [...typed.diagnostics, ...desugared.diagnostics],
  };
}

function run(emitted, symbol) {
  // Indirect eval so the RTS's top-level `var h$...` land on globalThis.
  const entry = (0, eval)(
    `${rts}\n${bootstrap}\n${emitted}\n(function(){ h$initStatic.forEach(function(f){f();}); h$initStatic.length = 0;` +
      ` return h$runEntry(function(){ h$r1 = ${symbol}; return h$r1.f; }); })`,
  );
  return entry();
}

const programs = [
  { name: "arithmetic", source: "module Main where\nmain = 2 + 3\n", expect: 5 },
  {
    name: "nested arithmetic",
    source: "module Main where\nmain = 2 + 3 * 4 - 1\n",
    expect: 13,
  },
  {
    name: "top-level function",
    source: "module Main where\ndouble x = x + x\nmain = double 21\n",
    expect: 42,
  },
  {
    name: "let and where",
    source: "module Main where\nmain = a * seven\n  where\n    a = 6\n    seven = 3 + 4\n",
    expect: 42,
  },
  {
    name: "if / comparison",
    source: "module Main where\nmain = if 3 < 4 then 10 else 20\n",
    expect: 10,
  },
  {
    name: "guards",
    source: "module Main where\nclassify n\n  | n < 0 = 0\n  | n == 0 = 1\n  | otherwise = 2\nmain = classify 7\n",
    expect: 2,
  },
  {
    name: "literal pattern equations",
    source: "module Main where\nf 0 = 100\nf 1 = 200\nf n = n\nmain = f 1\n",
    expect: 200,
  },
  {
    name: "recursion",
    source: "module Main where\nfact n = if n == 0 then 1 else n * fact (n - 1)\nmain = fact 5\n",
    expect: 120,
  },
  {
    name: "data type and case",
    source:
      "module Main where\ndata Shape = Circle Int | Square Int\narea s = case s of\n  Circle r -> 3 * r * r\n  Square w -> w * w\nmain = area (Square 6)\n",
    expect: 36,
  },
  {
    name: "constructor patterns in equations",
    source:
      "module Main where\ndata Pair = Pair Int Int\nfst2 (Pair a b) = a + b\nmain = fst2 (Pair 20 22)\n",
    expect: 42,
  },
  {
    // GHC 9.12 requires the import string to be a JS expression denoting a
    // function, not a GHCJS `$r = ...` pattern.
    name: "foreign import javascript",
    source:
      'module Main where\nforeign import javascript unsafe "((x,y) => x + y)" jsAdd :: Int -> Int -> Int\nmain = jsAdd 19 23\n',
    expect: 42,
  },
  {
    name: "lambda",
    source: "module Main where\napply f x = f x\nmain = apply (\\y -> y * 3) 14\n",
    expect: 42,
  },
];

const file = process.argv.slice(2).find((a) => !a.startsWith("--"));
const cases = file
  ? [{ name: file, source: readFileSync(file, "utf8"), expect: undefined }]
  : programs;

let failures = 0;
for (const program of cases) {
  let compiled;
  try {
    compiled = compile(program.source, file ?? `${program.name}.hs`);
  } catch (cause) {
    console.log(`  FAIL  ${program.name}: ${cause instanceof Error ? cause.message : cause}`);
    failures++;
    continue;
  }
  for (const d of compiled.diagnostics) console.log(`        ${formatDiagnostic(d)}`);
  if (show) console.log(`--- ${program.name} (${compiled.symbol}) ---\n${compiled.emitted}\n`);
  try {
    const result = run(compiled.emitted, compiled.symbol);
    if (program.expect === undefined) {
      console.log(`  ${program.name} => ${JSON.stringify(result)}`);
    } else if (result === program.expect) {
      console.log(`  ok    ${program.name} => ${result}`);
    } else {
      console.log(`  FAIL  ${program.name}: expected ${program.expect}, got ${JSON.stringify(result)}`);
      failures++;
    }
  } catch (cause) {
    console.log(`  FAIL  ${program.name}: ${cause instanceof Error ? `${cause.name}: ${cause.message}` : cause}`);
    failures++;
  }
}

console.log(`\n${cases.length - failures}/${cases.length} Haskell programs compiled and ran`);
process.exit(failures ? 1 : 0);
