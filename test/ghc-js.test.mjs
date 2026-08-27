import test from 'node:test';
import assert from 'node:assert/strict';
import { GhcJs } from '../dist/index.js';

const { Ident, JStgSyntax, Syntax, JStgMonad, Make, Transform, Ppr, Optimizer, OptExpr, OptSimple } = GhcJs;

test('GHC.JS.Ident.name is the identity smart constructor', () => {
  assert.equal(Ident.name('h$foo'), 'h$foo');
});

test('GHC.JS.JStg.Monad newIdent/withTag tag and restore the prefix', () => {
  const js = new JStgMonad.JSM('js');
  assert.equal(js.newIdent(), 'js_0');
  assert.deepEqual(js.withTag('RTS', (env) => [env.newIdent(), env.newIdent()]), ['RTS_1', 'RTS_2']);
  assert.equal(js.newIdent(), 'js_3');
});

test('GHC.JS.Transform.jStgStatToJS translates staged nodes to final ones, sorting JHash', () => {
  const staged = JStgSyntax.mconcatJStgStat([
    { tag: 'DeclStat', ident: 'x', value: JStgSyntax.Int(1) },
    { tag: 'ReturnStat', value: { tag: 'ValExpr', value: { tag: 'JHash', entries: [['z', JStgSyntax.Int(1)], ['a', JStgSyntax.Int(2)]] } } },
  ]);
  const final = Transform.jStgStatToJS(staged);
  assert.equal(Ppr.renderStat(final), 'var x=1;\nreturn {a: 2, z: 1 };\n');
  assert.deepEqual(Transform.identsS(staged), ['x']);
});

test('GHC.JS.Ppr string escaping matches encodeJsonChar, including astral surrogate pairs', () => {
  assert.equal(Ppr.renderValue({ tag: 'JStr', value: 'a/b"c\né\u{1F600}' }), '"a\\/b\\"c\\n\\xe9\\ud83d\\ude00"');
});

test('GHC.JS.Ppr negative numerals and doubles are parenthesized like GHC', () => {
  assert.equal(Ppr.renderValue({ tag: 'JInt', value: -2n }), '(-2)');
  assert.equal(Ppr.renderValue({ tag: 'JInt', value: 2n }), '2');
  assert.equal(Ppr.renderValue({ tag: 'JDouble', value: 2 }), '2.0');
  assert.equal(Ppr.renderValue({ tag: 'JDouble', value: -0 }), '(-0.0)');
});

test('GHC.JS.Ppr omits empty else/catch/finally and sorts hash keys', () => {
  const empty = { tag: 'BlockStat', stats: [] };
  assert.equal(Ppr.renderStat({ tag: 'IfStat', cond: Syntax.Var('c'), then: empty, else: empty }), 'if(c) {}');
  assert.equal(Ppr.renderStat({ tag: 'TryStat', body: empty, ident: 'e', catch: empty, finally: empty }), 'try {}');
  assert.equal(Ppr.renderValue({ tag: 'JHash', entries: [] }), '{}');
});

test('GHC.JS.Optimizer folds h$sp stack adjustments and modify-assign patterns', () => {
  const sp = { tag: 'ValExpr', value: { tag: 'JVar', ident: 'h$sp' } };
  const body = {
    tag: 'BlockStat',
    stats: [
      { tag: 'AssignStat', lhs: sp, op: 'SubAssignOp', rhs: { tag: 'ValExpr', value: { tag: 'JInt', value: 2n } } },
      { tag: 'AssignStat', lhs: sp, op: 'AddAssignOp', rhs: { tag: 'ValExpr', value: { tag: 'JInt', value: 5n } } },
      { tag: 'ReturnStat', value: sp },
    ],
  };
  const optimized = Optimizer.jsOptimize(body);
  // the stack-adjust fusion feeds back through the full optimizer chain, so
  // the resulting `h$sp = h$sp + 3; return h$sp;` gets folded again by the
  // "assign; return" pattern into a single return - this is a real fixpoint,
  // not a one-shot rewrite, matching GHC's own `loop` continuation.
  assert.equal(Ppr.renderStat(optimized), 'return (h$sp+3);\n');
});

test('GHC.JS.Optimizer rewrites i = i + 1 to ++i and i = i + n to i += n', () => {
  const i = Syntax.Var('i');
  const body = {
    tag: 'BlockStat',
    stats: [
      { tag: 'AssignStat', lhs: i, op: 'AssignOp', rhs: { tag: 'InfixExpr', op: 'AddOp', left: i, right: { tag: 'ValExpr', value: { tag: 'JInt', value: 1n } } } },
      { tag: 'AssignStat', lhs: i, op: 'AssignOp', rhs: { tag: 'InfixExpr', op: 'AddOp', left: i, right: { tag: 'ValExpr', value: { tag: 'JInt', value: 4n } } } },
    ],
  };
  const optimized = Optimizer.jsOptimize(body);
  assert.equal(Ppr.renderStat(optimized), '++ i;\ni+=4;\n');
});

test('GHC.JS.Opt.Expr constant-folds integer arithmetic and comparisons', () => {
  const two = { tag: 'ValExpr', value: { tag: 'JInt', value: 2n } };
  const three = { tag: 'ValExpr', value: { tag: 'JInt', value: 3n } };
  const sum = OptExpr.opt({ tag: 'InfixExpr', op: 'AddOp', left: two, right: three });
  assert.deepEqual(sum, { tag: 'ValExpr', value: { tag: 'JInt', value: 5n } });
  const cmp = OptExpr.opt({ tag: 'InfixExpr', op: 'LtOp', left: two, right: three });
  assert.deepEqual(cmp, { tag: 'ValExpr', value: { tag: 'JBool', value: true } });
});

test('GHC.JS.Opt.Expr collapses (cond ? 1 : 0) === 1 to double negation', () => {
  const cond = Syntax.Var('c');
  const ternary = { tag: 'IfExpr', cond, then: { tag: 'ValExpr', value: { tag: 'JInt', value: 1n } }, else: { tag: 'ValExpr', value: { tag: 'JInt', value: 0n } } };
  const one = { tag: 'ValExpr', value: { tag: 'JInt', value: 1n } };
  const optimized = OptExpr.opt({ tag: 'InfixExpr', op: 'StrictEqOp', left: ternary, right: one });
  assert.deepEqual(optimized, { tag: 'UOpExpr', op: 'NotOp', value: { tag: 'UOpExpr', op: 'NotOp', value: cond } });
});

test('GHC.JS.Opt.Simple removes unused declarations and floats single-use values', () => {
  const body = {
    tag: 'BlockStat',
    stats: [
      { tag: 'DeclStat', ident: 'x', value: { tag: 'ValExpr', value: { tag: 'JInt', value: 7n } } },
      { tag: 'ApplStat', fn: Syntax.Var('h$c1'), args: [Syntax.Var('x')] },
    ],
  };
  const optimized = OptSimple.simpleOpt({ tag: 'FuncStat', ident: 'h$f', args: [], body });
  assert.equal(Ppr.renderStat(optimized), 'function h$f() {h$c1(7);\n}');
});

test('GHC.JS.Make builds if_/eq_/app the way GHC.JS.Make does', () => {
  const expr = Make.if_(Make.eq_(Make.one_, Make.two_), Make.jString('yes'), Make.jString('no'));
  assert.equal(Ppr.renderExpr(Transform.jStgExprToJS(expr)), '((1==2)?"yes":"no")');
  assert.equal(Ppr.renderExpr(Transform.jStgExprToJS(Make.app('h$foo', [Make.one_]))), 'h$foo(1)');
});

test('GHC.JS.Make.jVar/jFunction thread fresh identifiers through JStgMonad', () => {
  const js = JStgMonad.initJSM();
  const stat = Make.jFunction(js, 'h$test', 1, ([x]) => Make.returnS(x));
  assert.equal(Ppr.renderStat(Transform.jStgStatToJS(stat)), 'function h$test(js_0) {return js_0;\n}');
});
