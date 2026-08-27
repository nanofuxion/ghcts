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
import { renderStaticRts } from "../dist/stg-js/rts-static.js";
import { stgToJS, renderModule } from "../dist/stg-js/codegen.js";
import { defaultStgToJSConfig } from "../dist/stg-js/types.js";
import { mkBinder, mkDataCon, UpdateFlag } from "../dist/stg.js";

const show = process.argv.includes("--print");
const config = defaultStgToJSConfig;
const mod = { unitId: "main", moduleName: "Test" };
/** rts/js/ calls the platform predicates and h$getGlobal at load time but does
 * not define them: they come from base's jsbits shim, which a real link
 * supplies and this harness does not (the oracle's all.js has them around line
 * 9155). Copied from there, with the node.js branch taken, and it has to land
 * before the RTS. */
const baseShim = `
var h$isNode_ = true, h$isJvm_ = false, h$isJsShell_ = false,
    h$isJsCore_ = false, h$isBrowser_ = false, h$isGHCJSi_ = false;
function h$isNode()    { return h$isNode_; }
function h$isJvm()     { return h$isJvm_; }
function h$isJsShell() { return h$isJsShell_; }
function h$isJsCore()  { return h$isJsCore_; }
function h$isBrowser() { return h$isBrowser_; }
function h$isGHCJSi()  { return h$isGHCJSi_; }
function h$getGlobal(that) {
    if(typeof global !== 'undefined') return global;
    return that;
}
`;

const rts = baseShim + renderRts(config) + "\n" + renderStaticRts(config);

/** Test-only scaffolding: the harness drives one term to completion itself
 * rather than starting a real thread, so it supplies its own stack, its own
 * trampoline, and a stop frame that captures R1. Everything else the emitted
 * code touches - h$o, h$init_closure, h$sti, h$stc, h$addCAF, h$rs - comes
 * from renderStaticRts(), which is GHC's own rts/js/ sources.
 */
const bootstrap = `
h$stack = new Array(1000);
h$sp = 0;
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
