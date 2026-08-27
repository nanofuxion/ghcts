/** The old surface-AST reshaping that `src/compiler.ts`'s interpretive
 * `lazy`/`force`/`apply` backend consumes. It is not Core in GHC's sense and
 * nothing downstream of `src/stg.ts` uses it; it lives here unchanged so the
 * old path keeps working until the STG path replaces it. New work belongs in
 * `src/core.ts`, `src/desugar.ts` and `src/core-to-stg.ts`. */
import type { Declaration, Expr, LocalBinding, Module, Pattern, Span, ValueDeclaration } from './ast.js';

export type LegacyCoreExpr =
  | { tag: 'literal'; value: number | string | null; span: Span }
  | { tag: 'variable'; name: string; span: Span }
  | { tag: 'apply'; fn: LegacyCoreExpr; arg: LegacyCoreExpr; span: Span }
  | { tag: 'lambda'; parameter: string; body: LegacyCoreExpr; span: Span }
  | { tag: 'let'; bindings: LegacyCoreBinding[]; body: LegacyCoreExpr; span: Span }
  | { tag: 'case'; subject: LegacyCoreExpr; alternatives: LegacyCoreAlternative[]; span: Span }
  | { tag: 'if'; condition: LegacyCoreExpr; thenBranch: LegacyCoreExpr; elseBranch: LegacyCoreExpr; span: Span }
  | { tag: 'constructor'; name: string; fields: LegacyCoreExpr[]; span: Span }
  | { tag: 'record'; constructor: string; fields: Array<{ name: string; value: LegacyCoreExpr }>; span: Span }
  | { tag: 'recordUpdate'; base: LegacyCoreExpr; fields: Array<{ name: string; value: LegacyCoreExpr }>; span: Span }
  | { tag: 'do'; statements: LegacyCoreDoStatement[]; span: Span }
  | { tag: 'ffi'; name: string; javascript: string; span: Span }
  | { tag: 'unsupported'; feature: string; span: Span };

export interface LegacyCoreAlternative { pattern: Pattern; guard?: LegacyCoreExpr; body: LegacyCoreExpr; }
export type LegacyCoreDoStatement =
  | { tag: 'expr'; expr: LegacyCoreExpr; span: Span }
  | { tag: 'bind'; pattern: Pattern; source: LegacyCoreExpr; span: Span }
  | { tag: 'let'; bindings: LegacyCoreBinding[]; span: Span };
export interface LegacyCoreBinding { name: string; equations: Array<{ patterns: Pattern[]; guards: Array<{ condition?: LegacyCoreExpr; body: LegacyCoreExpr }>; whereBindings: LegacyCoreBinding[] }>; span: Span; }
export interface LegacyCoreModule { name: string; bindings: LegacyCoreBinding[]; declarations: Declaration[]; }

export function lowerExpr(expr: Expr): LegacyCoreExpr {
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
    case 'list': return expr.items.reduceRight<LegacyCoreExpr>((tail, item) => ({ tag: 'constructor', name: ':', fields: [lowerExpr(item), tail], span: expr.span }), { tag: 'constructor', name: '[]', fields: [], span: expr.span });
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

function lowerLocal(binding: LocalBinding): LegacyCoreBinding { return { name: binding.name, equations: [{ patterns: binding.patterns, guards: (binding.guards ?? [{ body: binding.value }]).map(guard => ({ condition: guard.condition && lowerExpr(guard.condition), body: lowerExpr(guard.body) })), whereBindings: (binding.whereBindings ?? []).map(lowerLocal) }], span: binding.span }; }
function lowerValue(binding: ValueDeclaration): LegacyCoreBinding { return { name: binding.name, equations: binding.equations.map(equation => ({ patterns: equation.patterns, guards: equation.guards.map(guard => ({ condition: guard.condition && lowerExpr(guard.condition), body: lowerExpr(guard.body) })), whereBindings: equation.whereBindings.map(lowerLocal) })), span: binding.span }; }
export function lowerModule(module: Module): LegacyCoreModule { return { name: module.name, bindings: module.declarations.filter((declaration): declaration is ValueDeclaration => declaration.tag === 'value').map(lowerValue), declarations: module.declarations }; }
export function lowerModules(modules: readonly Module[]): LegacyCoreModule[] { return modules.map(lowerModule); }
