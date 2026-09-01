#!/usr/bin/env node
/**
 * Report runtime-shape counters for a linked GHCJS-shaped bundle.
 *
 * This deliberately does not execute the application: it is safe to run on
 * browser/Lynx bundles and gives a stable before/after signal while the
 * platform benchmark measures interaction latency separately.
 *
 *   node scripts/runtime-report.mjs references/misogram/dist/jsexe/out.js
 *   node scripts/runtime-report.mjs --json <bundle.js>
 */
import { existsSync, readFileSync } from "node:fs";

const args = process.argv.slice(2);
const json = args.includes("--json");
const file = args.find((x) => !x.startsWith("-")) ?? "references/misogram/dist/jsexe/out.js";
if (!existsSync(file)) {
  console.error(`bundle not found: ${file}`);
  process.exit(2);
}

const source = readFileSync(file, "utf8");
const count = (re) => [...source.matchAll(re)].length;
const report = {
  file,
  bytes: Buffer.byteLength(source),
  functions: count(/^function h\$/gm),
  genericApplies: count(/\bh\$ap_gen_fast\b/g),
  specializedApplies: count(/\bh\$ap_[0-9]+_[0-9]+_fast\b/g),
  enters: count(/\bh\$e\(/g),
  directEntryReturns: count(/return h\$[A-Za-z0-9_$]+_e;/g),
  updateFrames: count(/\bh\$upd\b|\bh\$update/gi),
  closureAllocations: count(/\bh\$c[0-9]?\s*\(/g),
  marshalDecoders: count(/fromJSVal(?:Unchecked)?/g),
  marshalEncoders: count(/toJSVal/g),
  ffiCalls: count(/\bh\$foreignCall\b|\bh\$ffi\b/g),
};

if (json) console.log(JSON.stringify(report, null, 2));
else {
  console.log(`bundle ${report.file} (${report.bytes} bytes)`);
  console.log(`functions ${report.functions}`);
  console.log(`direct entry returns ${report.directEntryReturns}`);
  console.log(`specialized applies ${report.specializedApplies}`);
  console.log(`generic applies ${report.genericApplies}`);
  console.log(`enters ${report.enters}`);
  console.log(`update-frame references ${report.updateFrames}`);
  console.log(`closure allocation call sites ${report.closureAllocations}`);
  console.log(`JS marshalling decoder references ${report.marshalDecoders}`);
  console.log(`JS marshalling encoder references ${report.marshalEncoders}`);
  console.log(`FFI call references ${report.ffiCalls}`);
}
