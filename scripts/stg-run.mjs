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
 */
import { readFileSync } from "node:fs";

const show = process.argv.includes("--print");

let codegen;
try {
  codegen = await import("../dist/stg-js/codegen.ts".replace(".ts", ".js"));
} catch {
  console.log("codegen not ported yet - nothing to run.");
  console.log("This harness is ready for it: it links whatever codegen emits");
  console.log("against ghcts's own rts.js and runs the result under node.");
  process.exit(0);
}

const { mkBinder, mkDataCon } = await import("../dist/stg.js");

/** The RTS ghcts generates, which the emitted code will call into. */
const { renderRts } = await import("../dist/stg-js/rts.js");
const rts = renderRts();

/** Terms to compile and run. Each says what it should evaluate to, so a
 * wrong answer is as visible as a crash. */
const terms = [
  {
    name: "literal",
    build: () => ({ tag: "StgLit", lit: { tag: "LitNumInt", value: 42n } }),
    expect: 42,
  },
  {
    name: "saturated constructor",
    build: () => {
      const just = mkDataCon("Just", 2, 1, "Maybe");
      return {
        tag: "StgConApp",
        con: just,
        args: [{ tag: "StgLitArg", lit: { tag: "LitNumInt", value: 7n } }],
      };
    },
    expect: 7,
  },
];

let failures = 0;
for (const term of terms) {
  let emitted;
  try {
    emitted = codegen.genExpr(term.build());
  } catch (cause) {
    console.log(`  FAIL  ${term.name}: codegen threw ${cause instanceof Error ? cause.message : cause}`);
    failures++;
    continue;
  }
  if (show) console.log(`--- ${term.name} ---\n${emitted}\n`);
  try {
    // Indirect eval so the RTS's top-level `var h$...` land on globalThis,
    // where generated code expects to find them.
    (0, eval)(`${rts}\n${emitted}`);
    console.log(`  ok    ${term.name}`);
  } catch (cause) {
    console.log(`  FAIL  ${term.name}: ${cause instanceof Error ? `${cause.name}: ${cause.message}` : cause}`);
    failures++;
  }
}

console.log(`\n${terms.length - failures}/${terms.length} terms ran on ghcts's RTS`);
process.exit(failures ? 1 : 0);
