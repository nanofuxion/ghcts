import test from 'node:test';
import assert from 'node:assert/strict';
import { JSM, jnumber, jstring, jvar, optimizeExpr, optimizeStat, printExpr, printStat } from '../dist/js-ast.js';

test('JStg fresh names are tagged and restored by withTag', () => {
  const jsm = new JSM('js');
  assert.equal(jsm.newIdent(), 'js_0');
  assert.deepEqual(jsm.withTag('RTS', (scope) => [scope.newIdent(), scope.newIdent()]), ['RTS_1', 'RTS_2']);
  assert.equal(jsm.newIdent(), 'js_3');
});

test('GHC.JS printer sorts object fields and parenthesizes negative numerals', () => {
  const object = { tag: 'value', value: { tag: 'object', fields: [['z', jnumber(1)], ['a', jnumber(-2)]] } };
  assert.equal(printExpr(object), '{"a": (-2), "z": 1}');
});

test('GHC.JS printer omits empty if and try branches', () => {
  const empty = { tag: 'block', body: [] };
  assert.equal(printStat({ tag: 'if', condition: jvar('c'), thenBranch: empty, elseBranch: empty }), 'if (c) {  }');
  assert.equal(printStat({ tag: 'try', body: empty, exception: 'e', handler: empty, finalizer: empty }), 'try {  }');
});

test('JFunc remains an expression with a block body', () => {
  const fn = { tag: 'value', value: { tag: 'function', parameters: ['x'], body: { tag: 'block', body: [{ tag: 'return', value: jstring('ok') }] } } };
  assert.equal(printExpr(fn), '(function(x) { return "ok"; })');
});

test('native AST optimizer folds constants and dead branches', () => {
  const expr = { tag: 'if-expr', condition: { tag: 'value', value: { tag: 'boolean', value: true } }, thenBranch: { tag: 'infix', operator: '+', left: jnumber(2), right: jnumber(3) }, elseBranch: jnumber(99) };
  assert.equal(printExpr(optimizeExpr(expr)), '5');
  const stat = { tag: 'if', condition: { tag: 'value', value: { tag: 'boolean', value: false } }, thenBranch: { tag: 'raw', source: 'bad();' }, elseBranch: { tag: 'return', value: jstring('ok') } };
  assert.equal(printStat(optimizeStat(stat)), 'return "ok";');
});
