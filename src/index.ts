/**
 * ghc-js — GHC's JavaScript backend as a JavaScript program.
 *
 * The compiler here is GHC itself: GHC's compiler library, compiled to
 * JavaScript by GHC's own JavaScript backend, driven through the GHC API.
 * Its output is byte-identical to a native GHC cross compiler's.
 */
export { compile } from "./compiler.js";
export type { CompileOptions, CompileResult } from "./compiler.js";
export { bundledCompiler, findGhcJs, ghcLibdir } from "./find-ghc.js";
