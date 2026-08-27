/** GHC.JS: the faithful TypeScript port of GHC's JavaScript backend AST
 * library (compiler/GHC/JS/**\/*.hs upstream). One namespace per Haskell
 * module, mirroring its export list as closely as TypeScript allows - see
 * each src/js/*.ts file's header comment for the specific module it ports
 * and where TypeScript's lack of type classes/pattern synonyms/tuple-arity
 * dispatch forced a documented deviation.
 *
 * This is deliberately separate from js-ast.ts, which is the small ad hoc AST
 * ghcts's own compiler pipeline (compiler.ts) emits through today - migrating
 * that pipeline onto this faithful AST is tracked as separate follow-up work,
 * not folded into this port for fear of destabilizing the working pipeline
 * and its test suite. */
export * as Ident from "./js/ident.js";
export * as JStgSyntax from "./js/jstg-syntax.js";
export * as Syntax from "./js/syntax.js";
export * as JStgMonad from "./js/jstg-monad.js";
export * as Make from "./js/make.js";
export * as Transform from "./js/transform.js";
export * as Ppr from "./js/ppr.js";
export * as Optimizer from "./js/optimizer.js";
export * as OptExpr from "./js/opt-expr.js";
export * as OptSimple from "./js/opt-simple.js";
