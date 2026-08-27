/** GHC.StgToJS: the faithful TypeScript port of GHC's JavaScript code
 * generator (compiler/GHC/StgToJS/**\/*.hs upstream). One namespace per
 * Haskell module - see each src/stg-js/*.ts header for the module it ports
 * and where TypeScript forced a documented deviation.
 *
 * The RTS half is the part that is live today: `Rts.renderRts()` emits the
 * same `rts.js` GHC's linker writes, which is a self-contained parity target
 * because GHC builds that file from `rts cfg` alone (the static
 * `rts/js/*.js` sources go into `lib.js` instead). Score it against real GHC
 * output with `node scripts/oracle-diff.mjs`.
 */
export * as Symbols from "./stg-js/symbols.js";
export * as Types from "./stg-js/types.js";
export * as Regs from "./stg-js/regs.js";
export * as Heap from "./stg-js/heap.js";
export * as Stack from "./stg-js/stack.js";
export * as Closure from "./stg-js/closure.js";
export * as RtsTypes from "./stg-js/rts-types.js";
export * as Apply from "./stg-js/apply.js";
export * as Rts from "./stg-js/rts.js";

// The code generator: STG in, JS calling the runtime above out. GHC reaches
// STG via Core, CorePrep and CoreToStg; ghcts is building that road from this
// end, so these consume `src/stg.ts` before anything produces it.
export * as Monad from "./stg-js/monad.js";
export * as Ids from "./stg-js/ids.js";
export * as ExprCtx from "./stg-js/expr-ctx.js";
export * as Utils from "./stg-js/utils.js";
export * as Literal from "./stg-js/literal.js";
export * as DataCon from "./stg-js/datacon.js";
export * as Arg from "./stg-js/arg.js";
