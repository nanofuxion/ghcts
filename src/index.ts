export { compileProject } from './compiler.js';
export { formatDiagnostic } from './diagnostics.js';
export { serveProject } from './server.js';
export { checkModule } from './typecheck.js';
export { classMembers, collectDictionaries, instanceHead, instanceMembers, instanceMethodValues, selectInstance } from './dictionary.js';
export { lowerExpr, lowerModule, lowerModules } from './core.js';
export { global, jblock, jcall, jfunction, jglobal, jif, jindex, jinfix, jnumber, jraw, jrawStat, jselect, jstring, junary, jvar, optimizeExpr, optimizeStat, printExpr, printStat } from './js-ast.js';
export type { AOp, Ident, JExpr, JStat, JStgExpr, JStgStat, JStgVal, JVal, Op, UOp } from './js-ast.js';
export { JSM, jStgExprToJS, jStgStatToJS } from './js-ast.js';
export type { RunningServer, ServeOptions } from './server.js';
export type { CompileProjectOptions, CompileResult, Diagnostic, GhctsConfig, Target } from './types.js';

/** The faithful port of GHC's GHC.JS.* module family - see src/ghc-js.ts. */
export * as GhcJs from './ghc-js.js';
export * as StgToJs from './stg-to-js.js';
