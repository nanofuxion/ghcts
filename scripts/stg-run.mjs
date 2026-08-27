#!/usr/bin/env node
/**
 * Compile a hand-built STG term and run it on ghcts's own RTS.
 *
 * This is how the code generator gets tested before any frontend exists to
 * feed it. STG is small enough to write by hand, and the RTS underneath is
 * already known good - it is byte-identical to GHC's and runs the real miso
 * counter on a phone - so anything that goes wrong here is codegen's fault
 * and nothing else's.
 *
 * The whole point is to fail loudly and early: the RTS expects GHC's exact
 * calling convention, so emitted code that gets a register, a stack slot or
 * a closure layout wrong crashes rather than quietly producing a wrong
 * answer.
 *
 *   node scripts/stg-run.mjs            # run the built-in terms
 *   node scripts/stg-run.mjs --print    # also show the generated JS
 *
 * Each term becomes a top-level binding `test = <expr>` and goes through the
 * real driver: codegen.stgToJS -> genToplevelRhs -> genBody -> genExpr. The
 * emitted module is linked against renderRts() and evaluated; the harness then
 * enters `test`'s thunk under a trampoline and inspects R1.
 */
import { renderRts } from "../dist/stg-js/rts.js";
import { stgToJS, renderModule } from "../dist/stg-js/codegen.js";
import { defaultStgToJSConfig } from "../dist/stg-js/types.js";
import { mkBinder, mkDataCon, UpdateFlag } from "../dist/stg.js";

const show = process.argv.includes("--print");
const config = defaultStgToJSConfig;
const mod = { unitId: "main", moduleName: "Test" };
const rts = renderRts(config);

/** ghcts's rts.ts generates the 533 *generated* RTS functions; GHC's RTS also
 * has a hand-written half (references/ghc/rts/js/{rts,mem,thread}.js) that
 * ghcts has not ported. These are the pieces of it that emitted code touches,
 * transcribed verbatim, plus a trampoline and a stop frame to drive one term.
 */
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

h$stack = new Array(1000);
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

/** The top-level binding GHC emits for a data constructor's worker; codegen
 * turns it into the `..._con_e` entry function that allocated closures point
 * at. Matches `dataConWorkId` in src/stg-js/ids.ts. */
const conWorkerBinding = (con) => ({
  tag: "StgNonRec",
  binder: { name: con.name, unique: con.unique, exported: true },
  rhs: { tag: "StgRhsCon", con, args: [] },
});

const just = mkDataCon("Just", 2, 1, "Maybe");

/** Terms to compile and run. Each says what it should evaluate to, so a
 * wrong answer is as visible as a crash. `cons` lists data constructors the
 * term needs worker entries for. */
const terms = [
  {
    name: "literal",
    build: () => ({ tag: "StgLit", lit: { tag: "LitNumInt", value: 42n } }),
    check: (r) => r === 42,
    expect: 42,
  },
  {
    name: "saturated constructor",
    build: () => {
      return {
        tag: "StgConApp",
        con: just,
        args: [{ tag: "StgLitArg", lit: { tag: "LitNumInt", value: 7n } }],
      };
    },
    cons: [just],
    // Just 7 is a real heap object: the payload lands in d1.
    check: (r) => r !== null && typeof r === "object" && r.d1 === 7,
    expect: "{ d1: 7 }",
  },
  {
    name: "unboxable constructor (I# 5)",
    build: () => {
      const int = mkDataCon("I#", 1, 1, "Int");
      return {
        tag: "StgConApp",
        con: int,
        args: [{ tag: "StgLitArg", lit: { tag: "LitNumInt", value: 5n } }],
      };
    },
    // Note [ Unboxable Literals Optimization ]: no wrapper object.
    check: (r) => r === 5,
    expect: 5,
  },
  {
    name: "case on a literal",
    build: () => {
      const b = mkBinder("b");
      return {
        tag: "StgCase",
        scrutinee: { tag: "StgLit", lit: { tag: "LitNumInt", value: 3n } },
        binder: b,
        altType: { tag: "PrimAlt" },
        alts: [
          { con: { tag: "LitAlt", lit: { tag: "LitNumInt", value: 3n } }, binders: [], body: { tag: "StgLit", lit: { tag: "LitNumInt", value: 111n } } },
          { con: { tag: "DEFAULT" }, binders: [], body: { tag: "StgLit", lit: { tag: "LitNumInt", value: 222n } } },
        ],
      };
    },
    check: (r) => r === 111,
    expect: 111,
  },
  {
    name: "case on a constructor (AlgAlt)",
    build: () => {
      const b = mkBinder("b");
      const x = mkBinder("x");
      return {
        tag: "StgCase",
        scrutinee: { tag: "StgConApp", con: just, args: [{ tag: "StgLitArg", lit: { tag: "LitNumInt", value: 8n } }] },
        binder: b,
        altType: { tag: "AlgAlt", typeName: "Maybe" },
        alts: [{ con: { tag: "DataAlt", con: just }, binders: [x], body: { tag: "StgApp", fn: x, args: [] } }],
      };
    },
    cons: [just],
    check: (r) => r === 8,
    expect: 8,
  },
  {
    name: "primop (2 +# 3)",
    build: () => {
      const b = mkBinder("b");
      return {
        tag: "StgCase",
        scrutinee: {
          tag: "StgOpApp",
          op: { tag: "StgPrimOp", op: "IntAddOp" },
          args: [
            { tag: "StgLitArg", lit: { tag: "LitNumInt", value: 2n } },
            { tag: "StgLitArg", lit: { tag: "LitNumInt", value: 3n } },
          ],
        },
        binder: b,
        altType: { tag: "PrimAlt" },
        alts: [{ con: { tag: "DEFAULT" }, binders: [], body: { tag: "StgApp", fn: b, args: [] } }],
      };
    },
    check: (r) => r === 5,
    expect: 5,
  },
  {
    name: "saturated function application",
    build: () => {
      const f = mkBinder("f");
      const x = mkBinder("x");
      const y = mkBinder("y");
      return {
        tag: "StgLet",
        binding: {
          tag: "StgNonRec",
          binder: f,
          rhs: {
            tag: "StgRhsClosure",
            freeVars: [],
            update: UpdateFlag.ReEntrant,
            args: [x],
            body: { tag: "StgApp", fn: x, args: [] },
          },
        },
        body: {
          tag: "StgCase",
          scrutinee: { tag: "StgApp", fn: f, args: [{ tag: "StgLitArg", lit: { tag: "LitNumInt", value: 21n } }] },
          binder: y,
          altType: { tag: "PolyAlt" },
          alts: [{ con: { tag: "DEFAULT" }, binders: [], body: { tag: "StgApp", fn: y, args: [] } }],
        },
      };
    },
    check: (r) => r === 21,
    expect: 21,
  },
  {
    name: "let-bound thunk, then entered",
    build: () => {
      const x = mkBinder("x");
      const y = mkBinder("y");
      return {
        tag: "StgLet",
        binding: {
          tag: "StgNonRec",
          binder: x,
          rhs: {
            tag: "StgRhsClosure",
            freeVars: [],
            update: UpdateFlag.Updatable,
            args: [],
            body: { tag: "StgLit", lit: { tag: "LitNumInt", value: 99n } },
          },
        },
        body: {
          tag: "StgCase",
          scrutinee: { tag: "StgApp", fn: x, args: [] },
          binder: y,
          altType: { tag: "PolyAlt" },
          alts: [{ con: { tag: "DEFAULT" }, binders: [], body: { tag: "StgApp", fn: y, args: [] } }],
        },
      };
    },
    check: (r) => r === 99,
    expect: 99,
  },
];

let failures = 0;
for (const term of terms) {
  const testId = mkBinder("test", { exported: true });
  const binding = {
    tag: "StgNonRec",
    binder: testId,
    rhs: {
      tag: "StgRhsClosure",
      freeVars: [],
      update: UpdateFlag.Updatable,
      args: [],
      body: term.build(),
    },
  };

  let emitted;
  let symbol;
  try {
    const units = stgToJS(config, mod, [...(term.cons ?? []).map(conWorkerBinding), binding]);
    emitted = renderModule(config, units);
    symbol = units.find((u) => u.luIdExports.some((b) => b === testId)).luObjBlock.oiSymbols[0];
  } catch (cause) {
    console.log(`  FAIL  ${term.name}: codegen threw ${cause instanceof Error ? cause.stack : cause}`);
    failures++;
    continue;
  }
  if (show) console.log(`--- ${term.name} (${symbol}) ---\n${emitted}\n`);
  try {
    // Indirect eval so the RTS's top-level `var h$...` land on globalThis,
    // where generated code expects to find them.
    const run = (0, eval)(
      `${rts}\n${bootstrap}\n${emitted}\n(function(){ h$initStatic.forEach(function(f){f();}); h$initStatic.length = 0;` +
        ` return h$runEntry(function(){ h$r1 = ${symbol}; return h$r1.f; }); })`,
    );
    const result = run();
    if (term.check(result)) {
      console.log(`  ok    ${term.name}`);
    } else {
      console.log(`  FAIL  ${term.name}: expected ${term.expect}, got ${JSON.stringify(result)}`);
      failures++;
    }
  } catch (cause) {
    console.log(`  FAIL  ${term.name}: ${cause instanceof Error ? `${cause.name}: ${cause.message}` : cause}`);
    failures++;
  }
}

console.log(`\n${terms.length - failures}/${terms.length} terms ran on ghcts's RTS`);
process.exit(failures ? 1 : 0);
