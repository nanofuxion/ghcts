// Two fixes the linked bundle needs before node can run it.
//
// 1. GHC's JS RTS calls `Module.HEAP8` for its Emscripten C shim, but this
//    Emscripten build does not put the heap views on `Module`.
// 2. The RTS's 64-bit division helpers call `JSBI.*`, a polyfill nothing in
//    the bundle defines. Node has native BigInt, which is what JSBI wraps.
import { readFileSync, writeFileSync } from "node:fs";
const [src, out] = [process.argv[2], process.argv[3]];
let s = readFileSync(src, "utf8");
const anchor = "  HEAPU64 = new BigUint64Array(b);\n}";
if (!s.includes(anchor)) throw new Error("updateMemoryViews not found");
s = s.replace(anchor, "  HEAPU64 = new BigUint64Array(b);\n  Module.HEAP8 = HEAP8; Module.HEAPU8 = HEAPU8; Module.HEAP16 = HEAP16; Module.HEAPU16 = HEAPU16; Module.HEAP32 = HEAP32; Module.HEAPU32 = HEAPU32; Module.HEAPF32 = HEAPF32; Module.HEAPF64 = HEAPF64;\n}");
s = s.replace("function unexportedRuntimeSymbol(sym) {", "function unexportedRuntimeSymbol(sym) {\n  if (/^HEAP/.test(sym)) return;");
const jsbi = `var JSBI = {
  BigInt: function (x) { return BigInt(x); },
  toNumber: function (x) { return Number(x); },
  add: function (a, b) { return a + b; },
  subtract: function (a, b) { return a - b; },
  multiply: function (a, b) { return a * b; },
  divide: function (a, b) { return a / b; },
  remainder: function (a, b) { return a % b; },
  bitwiseOr: function (a, b) { return a | b; },
  bitwiseAnd: function (a, b) { return a & b; },
  bitwiseXor: function (a, b) { return a ^ b; },
  leftShift: function (a, b) { return a << b; },
  signedRightShift: function (a, b) { return a >> b; },
  asIntN: function (n, x) { return BigInt.asIntN(n, x); },
  asUintN: function (n, x) { return BigInt.asUintN(n, x); },
  equal: function (a, b) { return a === b; },
  lessThan: function (a, b) { return a < b; },
  greaterThan: function (a, b) { return a > b; },
};
`;
writeFileSync(out, jsbi + s);
