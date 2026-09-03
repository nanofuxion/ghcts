// GHC's JS RTS calls `JSBI.*` in its 64-bit helpers - `h$hs_remWord64` is on
// the path of GHC's own `Unique` hashing, so the compiler cannot start
// without it. JSBI is a polyfill for BigInt on engines that lack it, and
// nothing in the bundle defines it. Node has BigInt natively, which is
// exactly what JSBI wraps, so these are the identity implementations.
var JSBI = {
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
