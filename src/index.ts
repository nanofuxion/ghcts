export { build, loadProgram } from './build.js';
export { formatDiagnostic } from './diagnostics.js';
export { serveProject } from './server.js';
export { checkModule } from './typecheck.js';
export { classMembers, collectDictionaries, instanceHead, instanceMembers, instanceMethodValues, selectInstance } from './dictionary.js';
export { elaborateModule, elaborateProgram } from './elaborate.js';
export { PRELUDE_SOURCE } from './prelude.js';
export { desugarModule } from './desugar.js';
export { coreToStg } from './core-to-stg.js';
export { link, renderModules } from './linker/linker.js';
export type { RunningServer, ServeOptions } from './server.js';
export type { CompileProjectOptions, CompileResult, Diagnostic, GhctsConfig, Target } from './types.js';

/** GHC.JS: the JavaScript AST, printer and optimizer, ported 1:1. */
export * as GhcJs from './ghc-js.js';
/** GHC.StgToJS: the code generator and the RTS it emits. */
export * as StgToJs from './stg-to-js.js';
