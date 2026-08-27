import type { Declaration, Expr, LocalBinding, Module, Pattern, Span, ValueDeclaration } from './ast.js';

/** The compact, typed-Core-facing expression shape.  Type annotations and
 * dictionary arguments are attached by later elaboration; this boundary keeps
 * desugaring independent from the TypeScript emitter. */
export type CoreExpr =
  | { tag: 'literal'; value: number | string | null; span: Span }
  | { tag: 'variable'; name: string; span: Span }
  | { tag: 'apply'; fn: CoreExpr; arg: CoreExpr; span: Span }
  | { tag: 'lambda'; parameter: string; body: CoreExpr; span: Span }
  | { tag: 'let'; bindings: CoreBinding[]; body: CoreExpr; span: Span }
  | { tag: 'case'; subject: CoreExpr; alternatives: CoreAlternative[]; span: Span }
  | { tag: 'if'; condition: CoreExpr; thenBranch: CoreExpr; elseBranch: CoreExpr; span: Span }
  | { tag: 'constructor'; name: string; fields: CoreExpr[]; span: Span }
  | { tag: 'record'; constructor: string; fields: Array<{ name: string; value: CoreExpr }>; span: Span }
  | { tag: 'recordUpdate'; base: CoreExpr; fields: Array<{ name: string; value: CoreExpr }>; span: Span }
  | { tag: 'do'; statements: CoreDoStatement[]; span: Span }
  | { tag: 'ffi'; name: string; javascript: string; span: Span }
  | { tag: 'unsupported'; feature: string; span: Span };

export interface CoreAlternative { pattern: Pattern; guard?: CoreExpr; body: CoreExpr; }
/**
 * Preserve monadic sequencing structure through Core.  The previous compact
 * representation discarded bind patterns and local declarations, making it
 * impossible for a later effect backend to resume a suspended `do` block
 * with the names required by its continuation.
 */
export type CoreDoStatement =
  | { tag: 'expr'; expr: CoreExpr; span: Span }
  | { tag: 'bind'; pattern: Pattern; source: CoreExpr; span: Span }
  | { tag: 'let'; bindings: CoreBinding[]; span: Span };
export interface CoreBinding { name: string; equations: Array<{ patterns: Pattern[]; guards: Array<{ condition?: CoreExpr; body: CoreExpr }>; whereBindings: CoreBinding[] }>; span: Span; }
export interface CoreModule { name: string; bindings: CoreBinding[]; declarations: Declaration[]; }

export function lowerExpr(expr: Expr): CoreExpr {
  switch (expr.tag) {
    case 'int': return { tag: 'literal', value: expr.value, span: expr.span };
    case 'string': return { tag: 'literal', value: expr.value, span: expr.span };
    case 'unit': return { tag: 'literal', value: null, span: expr.span };
    case 'var': return { tag: 'variable', name: expr.name, span: expr.span };
    case 'app': return { tag: 'apply', fn: lowerExpr(expr.fn), arg: lowerExpr(expr.arg), span: expr.span };
    case 'lambda': return { tag: 'lambda', parameter: expr.parameter, body: lowerExpr(expr.body), span: expr.span };
    case 'let': return { tag: 'let', bindings: expr.bindings.map(lowerLocal), body: lowerExpr(expr.body), span: expr.span };
    case 'case': return { tag: 'case', subject: lowerExpr(expr.subject), alternatives: expr.alternatives.map(alternative => ({ pattern: alternative.pattern, guard: alternative.guard && lowerExpr(alternative.guard), body: lowerExpr(alternative.body) })), span: expr.span };
    case 'if': return { tag: 'if', condition: lowerExpr(expr.condition), thenBranch: lowerExpr(expr.thenBranch), elseBranch: lowerExpr(expr.elseBranch), span: expr.span };
    case 'tuple': return { tag: 'constructor', name: `Tuple${expr.items.length}`, fields: expr.items.map(lowerExpr), span: expr.span };
    case 'list': return expr.items.reduceRight<CoreExpr>((tail, item) => ({ tag: 'constructor', name: ':', fields: [lowerExpr(item), tail], span: expr.span }), { tag: 'constructor', name: '[]', fields: [], span: expr.span });
    case 'record': return { tag: 'record', constructor: expr.constructor, fields: expr.fields.map(field => ({ name: field.name, value: lowerExpr(field.value) })), span: expr.span };
    case 'recordUpdate': return { tag: 'recordUpdate', base: lowerExpr(expr.base), fields: expr.fields.map(field => ({ name: field.name, value: lowerExpr(field.value) })), span: expr.span };
    case 'do': return {
      tag: 'do',
      statements: expr.statements.map(statement =>
        statement.tag === 'expr'
          ? { tag: 'expr', expr: lowerExpr(statement.expr), span: statement.expr.span }
          : statement.tag === 'bind'
            ? { tag: 'bind', pattern: statement.pattern, source: lowerExpr(statement.source), span: statement.source.span }
            : { tag: 'let', bindings: statement.bindings.map(lowerLocal), span: expr.span },
      ),
      span: expr.span,
    };
    case 'lambdaCase': return { tag: 'lambda', parameter: `__lambdaCase${expr.span.start}`, body: { tag: 'case', subject: { tag: 'variable', name: `__lambdaCase${expr.span.start}`, span: expr.span }, alternatives: expr.alternatives.map(alternative => ({ pattern: alternative.pattern, guard: alternative.guard && lowerExpr(alternative.guard), body: lowerExpr(alternative.body) })), span: expr.span }, span: expr.span };
    case 'listComp': return { tag: 'unsupported', feature: 'list comprehension', span: expr.span };
    case 'jsQuote': return { tag: 'ffi', name: 'js', javascript: expr.body, span: expr.span };
  }
}

function lowerLocal(binding: LocalBinding): CoreBinding { return { name: binding.name, equations: [{ patterns: binding.patterns, guards: (binding.guards ?? [{ body: binding.value }]).map(guard => ({ condition: guard.condition && lowerExpr(guard.condition), body: lowerExpr(guard.body) })), whereBindings: (binding.whereBindings ?? []).map(lowerLocal) }], span: binding.span }; }
function lowerValue(binding: ValueDeclaration): CoreBinding { return { name: binding.name, equations: binding.equations.map(equation => ({ patterns: equation.patterns, guards: equation.guards.map(guard => ({ condition: guard.condition && lowerExpr(guard.condition), body: lowerExpr(guard.body) })), whereBindings: equation.whereBindings.map(lowerLocal) })), span: binding.span }; }
export function lowerModule(module: Module): CoreModule { return { name: module.name, bindings: module.declarations.filter((declaration): declaration is ValueDeclaration => declaration.tag === 'value').map(lowerValue), declarations: module.declarations }; }
export function lowerModules(modules: readonly Module[]): CoreModule[] { return modules.map(lowerModule); }
