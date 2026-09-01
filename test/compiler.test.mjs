import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { checkModule, classMembers, collectDictionaries, instanceHead, instanceMembers, instanceMethodValues, selectInstance } from '../dist/index.js';
import { applyLayout, lex, preprocess } from '../dist/lexer.js';
import { parseModule } from '../dist/parser.js';
import { collectInterface } from '../dist/interface.js';
import { parseCabalLibrary } from '../dist/cabal.js';
import { deriveCabalConfig } from '../dist/build.js';
import { copy, inlineKnownCalls } from '../dist/core-opt/inline.js';
import { specialiseKnownDicts } from '../dist/core-opt/specialise.js';
import { forceStrictArgs } from '../dist/core-opt/strictness.js';
import { workWrap } from '../dist/core-opt/workwrap.js';
import { simplifyCore } from '../dist/core-opt/simplify.js';
import { floatConstants } from '../dist/core-opt/float.js';
import { optimiseCore } from '../dist/build.js';
import { elaborateProgram } from '../dist/elaborate.js';
import { desugarModule } from '../dist/desugar.js';
import { coreFreeVars } from '../dist/core.js';

test('derives a ghcts.json from an executable-only .cabal, resolving a local dependency', async () => {
  // sample-app has no ghcts.json - only app.cabal (an `executable` stanza) -
  // and lives one directory inside the miso checkout, so miso.cabal is its
  // own parent directory rather than a sibling.
  const config = await deriveCabalConfig('references/miso/sample-app');
  assert.equal(config.entry.module, 'Main');
  assert.deepEqual(config.dependencies, ['miso']);
  assert.ok(config.sourceRoots.includes('../src'));
  assert.ok(config.sourceRoots.includes('../ffi/js'));
});

/** Desugar one module the way `build` does, so a Core pass can be tested on
 * the Core the compiler actually produces rather than a hand-built tree. */
function coreOf(source) {
  const parsed = parseModule(source, 'Opt.hs');
  assert.deepEqual(parsed.diagnostics.filter((d) => d.severity === 'error'), []);
  const modules = new Map([[parsed.module.ast.name, parsed.module.ast]]);
  const elaborated = elaborateProgram(modules, 'Main', 'Main.hs');
  return desugarModule(elaborated.module, 'Main.hs').program;
}

const bindNamed = (program, name) => {
  for (const b of program.binds) {
    const pairs = b.tag === 'NonRec' ? [[b.binder, b.rhs]] : b.pairs;
    for (const [binder, rhs] of pairs) if (binder.name === name) return rhs;
  }
  return undefined;
};

const contains = (e, pred) => {
  if (!e || typeof e !== 'object') return false;
  if (pred(e)) return true;
  return Object.values(e).some((v) =>
    Array.isArray(v) ? v.some((x) => contains(x, pred)) : contains(v, pred));
};

test('inlining replaces a known class method with the primop it is made of', () => {
  const source = 'module Main where\nadd :: Int -> Int -> Int\nadd a b = a + b\n';
  const before = bindNamed(coreOf(source), 'add');
  assert.ok(contains(before, (e) => e.tag === 'Var' && e.binder.name === '$cNumInt$+'));
  const after = bindNamed(inlineKnownCalls(coreOf(source)), 'add');
  // The dictionary method is gone and its IntAddOp is now in `add` itself.
  assert.ok(!contains(after, (e) => e.tag === 'Var' && e.binder.name === '$cNumInt$+'));
  assert.ok(contains(after, (e) => e.tag === 'Op' && e.op.op === 'IntAddOp'));
});

test('strict arguments are forced at the call site, lazy ones are left alone', () => {
  // `strict` forces both arguments; `konst` forces only the first. A `Case`
  // around the argument at the call site is the thunk that is not built.
  // Both callees are recursive, so the inliner leaves the calls in place and
  // what the `case`s say is the demand signature, not the inlining.
  const source = [
    'module Main where',
    'strictF :: Int -> Int -> Int',
    'strictF a b = if a + b > 0 then a else strictF (a + 1) (b + 1)',
    'konst :: Int -> Int -> Int',
    'konst a b = if a > 0 then a else konst (a + 1) b',
    'callStrict :: Int -> Int',
    'callStrict n = strictF (n + 1) (n + 2)',
    'callLazy :: Int -> Int',
    'callLazy n = konst (n + 1) (n + 2)',
    '',
  ].join('\n');
  const opt = forceStrictArgs(inlineKnownCalls(coreOf(source)));
  const isSat = (e) => e.tag === 'Case' && e.binder.name === 'sat';
  assert.ok(contains(bindNamed(opt, 'callStrict'), isSat), 'strict call should force its arguments');
  // konst's second argument may never be evaluated, so forcing it would turn
  // a defined result into a bottom.
  const lazy = bindNamed(opt, 'callLazy');
  const forced = [];
  const walk = (e) => {
    if (!e || typeof e !== 'object') return;
    if (isSat(e)) forced.push(e);
    Object.values(e).forEach((v) => (Array.isArray(v) ? v.forEach(walk) : walk(v)));
  };
  walk(lazy);
  assert.equal(forced.length, 1, 'only konst\'s first argument is strict');
});

test('constrained Eq [Int] specialises to the Int method, not a dictionary apply', () => {
  const source = [
    'module Main where',
    'eqInts :: [Int] -> [Int] -> Bool',
    'eqInts xs ys = xs == ys',
    '',
  ].join('\n');
  const spec = specialiseKnownDicts(coreOf(source));
  const eqInts = bindNamed(spec, 'eqInts');
  assert.ok(eqInts, 'eqInts should exist');
  // The list instance is applied to `$fEqInt` at most as a specialised `$s…`
  // binding; the call itself must not keep `== ($fEqList $fEqInt)`.
  assert.ok(
    !contains(eqInts, (e) => e.tag === 'Var' && e.binder.name === '=='),
    'the == selector should be gone',
  );
  assert.ok(
    contains(eqInts, (e) => e.tag === 'Var' && /\$cEqInt\$==|\$s\$cEqList/.test(e.binder.name)),
    'should mention the Int method or a specialised list method',
  );
});

test('toJSON xs at [Rec] does not keep a $fToJSONList dictionary apply', () => {
  const source = [
    'module Main where',
    'data Rec = Rec Int',
    'class ToJSON a where',
    '  toJSON :: a -> Int',
    'instance ToJSON Int where',
    '  toJSON n = n',
    'instance ToJSON Rec where',
    '  toJSON (Rec n) = toJSON n',
    'instance ToJSON a => ToJSON [a] where',
    '  toJSON xs = case xs of',
    '    [] -> 0',
    '    y:ys -> toJSON y',
    'jsonList :: [Rec] -> Int',
    'jsonList xs = toJSON xs',
    '',
  ].join('\n');
  const spec = specialiseKnownDicts(coreOf(source));
  const jsonList = bindNamed(spec, 'jsonList');
  assert.ok(jsonList, 'jsonList should exist');
  assert.ok(
    !contains(jsonList, (e) => e.tag === 'Var' && e.binder.name === '$fToJSONList'),
    'the list dictionary should not be applied at the call site',
  );
  assert.ok(
    !contains(jsonList, (e) => e.tag === 'Var' && e.binder.name === 'toJSON'),
    'the toJSON selector should be gone',
  );
});

test('work/wrap unpacks Int arguments on a strict adder', () => {
  const source = [
    'module Main where',
    'add :: Int -> Int -> Int',
    'add a b = a + b',
    '',
  ].join('\n');
  const wrapped = workWrap(inlineKnownCalls(coreOf(source)));
  const worker = [...wrapped.binds].find(
    (b) => b.tag === 'NonRec' && b.binder.name.startsWith('$w'),
  );
  assert.ok(worker, 'a $w worker should exist');
  const add = bindNamed(wrapped, 'add');
  assert.ok(contains(add, (e) => e.tag === 'Case'), 'the wrapper should case on its Int args');
});

test('work/wrap leaves every worker binder in scope on a self-recursive loop', () => {
  const source = [
    'module Main where',
    'sumTo :: Int -> Int -> Int',
    'sumTo acc 0 = acc',
    'sumTo acc n = sumTo (acc + n) (n - 1)',
    '',
  ].join('\n');
  const opt = workWrap(
    simplifyCore(forceStrictArgs(inlineKnownCalls(coreOf(source)))),
  );
  const tops = new Set();
  for (const b of opt.binds)
    if (b.tag === 'NonRec') tops.add(b.binder);
    else for (const [x] of b.pairs) tops.add(x);
  for (const b of opt.binds) {
    const pairs = b.tag === 'NonRec' ? [[b.binder, b.rhs]] : b.pairs;
    for (const [binder, rhs] of pairs) {
      const free = [...coreFreeVars(rhs)].filter((v) => ![...tops].some((t) => t.unique === v.unique));
      assert.deepEqual(free.map((v) => v.name), [], `${binder.name} should bind everything it reads`);
    }
  }
  // The worker calls itself, not back through the wrapper it was split from:
  // GHC inlines the wrapper's INLINE unfolding at every call site, and a
  // worker that re-entered the wrapper would rebox on every iteration.
  const worker = bindNamed(opt, '$wsumTo');
  assert.ok(worker, 'a $wsumTo worker should exist');
  assert.ok(
    contains(worker, (e) => e.tag === 'Var' && e.binder.name === '$wsumTo'),
    'the recursive call should reach the worker',
  );
});

test('inlining leaves work/wrap workers alone', () => {
  const source = [
    'module Main where',
    'add :: Int -> Int -> Int',
    'add a b = a + b',
    'twice :: Int -> Int',
    'twice n = add n n',
    '',
  ].join('\n');
  const wrapped = workWrap(inlineKnownCalls(coreOf(source)));
  const after = inlineKnownCalls(wrapped);
  assert.ok(
    [...after.binds].some((b) => b.tag === 'NonRec' && b.binder.name.startsWith('$w')),
    'the worker should survive a later inlining pass',
  );
});

test('the simplifier drops a case on a constructor it just built', () => {
  const source = [
    'module Main where',
    'unbox :: Int',
    'unbox = case (1 :: Int) of n -> n + 1',
    '',
  ].join('\n');
  const before = inlineKnownCalls(coreOf(source));
  assert.ok(contains(before, (e) => e.tag === 'Case'), 'there should be a case to remove');
  const after = bindNamed(simplifyCore(before), 'unbox');
  assert.ok(
    !contains(after, (e) => e.tag === 'Case'),
    'nothing is left to scrutinise once the constructor is known',
  );
  assert.ok(contains(after, (e) => e.tag === 'Op'), 'the primop should remain');
});

test('the simplifier reuses what an enclosing case already proved', () => {
  const source = [
    'module Main where',
    'twice :: Int -> Int',
    'twice n = n + n',
    '',
  ].join('\n');
  const before = inlineKnownCalls(coreOf(source));
  const countCases = (e) => {
    let n = 0;
    contains(e, (x) => {
      if (x.tag === 'Case') n += 1;
      return false;
    });
    return n;
  };
  const after = bindNamed(simplifyCore(before), 'twice');
  // `n` is unpacked once; the second `n` reads the payload already in scope.
  assert.equal(countCases(after), 1);
});

test('work/wrap unboxes an argument the body only cases further down', () => {
  // `sumTo` cases `n` at the top and `acc` inside a branch. GHC unboxes both -
  // Str=<1!P(L)><1!P(1L)> - so the accumulator must not stay boxed just
  // because no case for it sits on the spine.
  const source = [
    'module Main where',
    'sumTo :: Int -> Int -> Int',
    'sumTo acc 0 = acc',
    'sumTo acc n = sumTo (acc + n) (n - 1)',
    '',
  ].join('\n');
  const worker = bindNamed(optimiseCore(coreOf(source)), '$wsumTo');
  assert.ok(worker, 'a $wsumTo worker should exist');
  // Two unboxed payload parameters, so neither argument crosses the recursive
  // call in a box.
  let params = 0;
  for (let e = worker; e && e.tag === 'Lam'; e = e.body) params += 1;
  assert.equal(params, 2);
  // The recursive call passes primop results, not freshly built boxes.
  assert.ok(
    contains(worker, (e) => e.tag === 'Var' && e.binder.name === '$wsumTo'),
    'the worker should call itself',
  );
});

test('constant constructors are shared at the top level, not rebuilt', () => {
  const source = [
    'module Main where',
    'data Colour = Red | Green',
    'pick :: Int -> Colour',
    'pick 0 = Red',
    'pick _ = Red',
    '',
  ].join('\n');
  const floated = floatConstants(inlineKnownCalls(coreOf(source)));
  const shared = floated.binds.filter(
    (b) => b.tag === 'NonRec' && b.binder.name === 'lvl' && b.rhs.tag === 'Con' && b.rhs.con.name === 'Red',
  );
  assert.equal(shared.length, 1, 'both branches should reach one shared Red');
  const pick = bindNamed(floated, 'pick');
  assert.ok(
    !contains(pick, (e) => e.tag === 'Con' && e.con.name === 'Red'),
    'no branch should build Red for itself',
  );
});

test('an unboxed-representation box is left where it is', () => {
  // `I# 0` is the number itself on this backend, and GHC.StgToJS.Sinker
  // unfloats exactly these again, so floating one out only invents a name.
  const source = ['module Main where', 'zero :: Int', 'zero = 0', ''].join('\n');
  const floated = floatConstants(inlineKnownCalls(coreOf(source)));
  const boxes = floated.binds.filter(
    (b) =>
      b.tag === 'NonRec' &&
      b.binder.name === 'lvl' &&
      b.rhs.tag === 'Con' &&
      b.rhs.con.typeName === 'Int',
  );
  assert.deepEqual(boxes, [], 'an Int box is the number itself here');
});

test('a call on anything but constants is left where it is', () => {
  // Two occurrences of one closed call are not one value: miso's `(#)` frees
  // the JavaScript handle it built, calling it a temporary nobody else can
  // reach, so a second occurrence handed the first one's handle reads a freed
  // handle. Only a call on literals is safe to share.
  const source = [
    'module Main where',
    'seed :: Int',
    'seed = 7',
    'bump :: Int -> Int',
    'bump x = x + 1',
    'go :: Int -> Int',
    'go n = case n of',
    '  0 -> bump seed',
    '  _ -> bump seed',
    '',
  ].join('\n');
  const floated = floatConstants(inlineKnownCalls(coreOf(source)));
  const constant = (e) => e.tag === 'Lit' || (e.tag === 'Con' && e.args.every(constant));
  const args = (e) => (e.tag === 'App' ? [...args(e.fn), e.arg] : []);
  const lifted = floated.binds.filter(
    (b) => b.tag === 'NonRec' && b.binder.name === 'lvl' && b.rhs.tag === 'App',
  );
  for (const b of lifted)
    assert.ok(
      args(b.rhs).every(constant),
      'a call with a variable argument must stay where it is',
    );
});

test('copying renames a binder only where that binder is in scope', () => {
  // A desugared module already binds one unique at more than one site, and
  // specialising copies bodies that share more. A single renaming map for the
  // whole walk then hands a free reference the binder minted for some other
  // branch, and the name it points at exists nowhere - the swipe handler died
  // on `h$$mainZCMainzizuzupatternzu90_u_a812 is not defined`.
  const con = { name: 'Just', unique: 900, tag: 1, arity: 1, typeName: 'Maybe' };
  const y = { name: 'y', unique: 901 };
  const bound = {
    tag: 'Case',
    scrutinee: { tag: 'Var', binder: { name: 'x', unique: 902 } },
    binder: { name: 'wild', unique: 903 },
    alts: [{ con: { tag: 'DataAlt', con }, binders: [y], body: { tag: 'Var', binder: y } }],
  };
  // The second `y` is free: it is some other binding that happens to share the
  // unique, and copying must leave it alone.
  const copied = copy({ tag: 'App', fn: bound, arg: { tag: 'Var', binder: y } }, new Map(), new Map());
  assert.equal(copied.arg.binder.unique, y.unique, 'a free occurrence keeps its own binder');
  assert.notEqual(
    copied.fn.alts[0].binders[0].unique,
    y.unique,
    'the bound occurrence should have been renamed',
  );
  assert.equal(
    copied.fn.alts[0].body.binder.unique,
    copied.fn.alts[0].binders[0].unique,
    'a branch must name the binder its own alternative binds',
  );
});

test('checks record selector types from their declared field signature', () => {
  const parsed = parseModule('module Main where\ndata Model = Model { counter :: Int }\nbad :: String\nbad = counter (Model 1)\n', 'RecordType.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const data = parsed.module.ast.declarations.find(item => item.tag === 'data');
  assert.deepEqual(data.constructors[0].fieldTypes, ['Int']);
  const checked = checkModule(parsed.module.ast, 'RecordType.hs');
  assert.ok(checked.diagnostics.some(diagnostic => diagnostic.code === 'E_TYPE' && /Int.*String/.test(diagnostic.message)));
});

test('parses cons as a right-associative infix operator', () => {
  const parsed = parseModule('module Main where\nmain = 1 : 2 : []\n', 'ConsAssoc.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations[0].equations[0].guards[0].body;
  assert.equal(body.fn.fn.name, ':');
  assert.equal(body.fn.arg.tag, 'int');
  assert.equal(body.fn.arg.value, 1);
  assert.equal(body.arg.fn.fn.name, ':');
  assert.equal(body.arg.fn.arg.value, 2);
});

test('parses cons chains with append as a flat list spine', () => {
  const parsed = parseModule('module Main where\nmain = a : b : cs ++ ds\n', 'ConsAppend.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations[0].equations[0].guards[0].body;
  assert.equal(body.fn.fn.name, ':');
  assert.equal(body.fn.arg.name, 'a');
  assert.equal(body.arg.fn.fn.name, ':');
  assert.equal(body.arg.fn.arg.name, 'b');
  assert.equal(body.arg.arg.fn.fn.name, '++');
});

test('list index binds tighter than addition', () => {
  const parsed = parseModule('module Main where\nmain = xs !! n + 1\n', 'IndexPrec.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations[0].equations[0].guards[0].body;
  assert.equal(body.fn.fn.name, '+');
  assert.equal(body.fn.arg.fn.fn.name, '!!');
});

test('function equations treat a nullary constructor and the next binder as separate arguments', () => {
  const parsed = parseModule(
    'module Main where\ndata Mode = Sync | Async\nevalScheduled Sync x = x\nevalScheduled Async x = x\n',
    'Apat.hs',
  );
  assert.deepEqual(parsed.diagnostics, []);
  const evalScheduled = parsed.module.ast.declarations.find((declaration) => declaration.tag === 'value' && declaration.name === 'evalScheduled');
  assert.equal(evalScheduled.equations[0].patterns.length, 2);
  assert.equal(evalScheduled.equations[0].patterns[0].tag, 'con');
  assert.equal(evalScheduled.equations[0].patterns[0].name, 'Sync');
  assert.equal(evalScheduled.equations[0].patterns[0].args.length, 0);
  assert.equal(evalScheduled.equations[0].patterns[1].tag, 'var');
  assert.equal(evalScheduled.equations[1].patterns[0].name, 'Async');
});

test('parses record updates through lens & and +~ at Haskell precedence', () => {
  const parsed = parseModule('module Main where\nmain = model & counter +~ 1\n', 'LensPrec.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations[0].equations[0].guards[0].body;
  assert.equal(body.tag, 'app');
  assert.equal(body.fn.tag, 'app');
  assert.equal(body.fn.fn.tag, 'var');
  assert.equal(body.fn.fn.name, '&');
  assert.equal(body.arg.tag, 'app');
  assert.equal(body.arg.fn.tag, 'app');
  assert.equal(body.arg.fn.fn.tag, 'var');
  assert.equal(body.arg.fn.fn.name, '+~');
});

test('keeps callback argument arrows inside one foreign-import type argument', () => {
  const parsed = parseModule('module Main where\nforeign import javascript unsafe "(($1) => $1)" register :: (JSVal -> IO ()) -> IO Callback\n', 'ForeignCallbackType.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const declaration = parsed.module.ast.declarations.find(item => item.tag === 'foreign');
  assert.deepEqual(declaration.signature, ['( JSVal -> IO ( ) )', 'IO Callback']);
});

test('parses parenthesized symbolic foreign-import binders', () => {
  const parsed = parseModule('module FFI where\nforeign import javascript unsafe "(($1,$2) => $1)" (<|>) :: f a -> f a -> f a\n', 'SymbolicFFI.hs');
  assert.deepEqual(parsed.diagnostics, []);
  assert.equal(parsed.module.ast.declarations[0].name, '<|>');
});

test('preprocesses numeric CPP branches without leaking directives into the parser', () => {
  assert.equal(preprocess('#if __GLASGOW_HASKELL__ <= 865\nold\n#else\nnew\n#endif\n'), '\n\n\nnew\n\n');
});

test('reads source roots, JavaScript assets, and dependencies from a Cabal library stanza', () => {
  assert.deepEqual(parseCabalLibrary('name: demo\nlibrary\n  hs-source-dirs: src, generated\n  js-sources: js/runtime.js\n  build-depends: base >=4.18, text\n  cpp-options: -DFEATURE\n').sourceDirs, ['src', 'generated']);
  const parsed = parseCabalLibrary('name: demo\nlibrary\n  hs-source-dirs: src\n  js-sources: js/runtime.js\n  build-depends: base >=4.18, text\n');
  assert.deepEqual(parsed.jsSources, ['js/runtime.js']);
  assert.deepEqual(parsed.buildDepends, ['base', 'text']);
});

test('resolves an imported common stanza\'s flag conditionals to one js-sources branch', () => {
  // miso.cabal's shape verbatim: the js-sources live in a `common` stanza the
  // library imports, nested two conditionals deep. Reading only the library's
  // own unindented fields finds no JavaScript at all for this package.
  const cabal = [
    'name: demo',
    'common client',
    '  if impl(ghcjs) || arch(javascript) || arch(wasm32)',
    '    if flag(native) && flag(production)',
    '      js-sources:',
    '        js/miso-native.prod.js',
    '    elif flag(production)',
    '      js-sources:',
    '        js/miso.prod.js',
    '    elif flag(native)',
    '      js-sources:',
    '        js/miso-native.js',
    '    else',
    '      js-sources:',
    '        js/miso.js',
    'flag native',
    '  manual:',
    '    True',
    '  default:',
    '    False',
    'flag production',
    '  default:',
    '    False',
    'library',
    '  import:',
    '    client',
    '  hs-source-dirs:',
    '    src',
    '',
  ].join('\n');
  assert.deepEqual(parseCabalLibrary(cabal, ['native', 'production']).jsSources, ['js/miso-native.prod.js']);
  assert.deepEqual(parseCabalLibrary(cabal, ['production']).jsSources, ['js/miso.prod.js']);
  assert.deepEqual(parseCabalLibrary(cabal, ['native']).jsSources, ['js/miso-native.js']);
  assert.deepEqual(parseCabalLibrary(cabal).jsSources, ['js/miso.js']);
  assert.deepEqual(parseCabalLibrary(cabal, ['native']).sourceDirs, ['src']);

  // The real file, so the test cannot pass against a shape miso does not have.
  const miso = parseCabalLibrary(readFileSync('references/miso/miso.cabal', 'utf8'), ['native', 'production']);
  assert.deepEqual(miso.jsSources, ['js/miso-native.prod.js']);
  assert.ok(miso.cppOptions.includes('-DNATIVE') && miso.cppOptions.includes('-DPRODUCTION'));
  assert.ok(!miso.cppOptions.includes('-DVANILLA'), 'arch(javascript) must win the impl/arch chain');
});

test('collects module-owned values, constructors, and record fields before resolution', () => {
  const parsed = parseModule('module Lib where\ndata Model = Model { count :: Int }\ntype Identifier = Int\nrun = Model 0\n', 'Interface.hs');
  const iface = collectInterface(parsed.module.ast);
  assert.deepEqual([...iface.values], ['run']);
  assert.deepEqual([...iface.constructors], ['Model']);
  assert.deepEqual([...iface.fields], ['count']);
  assert.deepEqual([...iface.types], ['Model', 'Identifier']);
  const classModule = parseModule('module Classes where\nclass Render a where\n  render :: a -> String\n', 'ClassInterface.hs');
  assert.deepEqual([...collectInterface(classModule.module.ast).types], ['Render']);
});

test('inserts virtual layout punctuation without losing source tokens', () => {
  const tokens = applyLayout(lex('main = let\n  x = 1\n  y = 2\nin x + y\n', 'Layout.hs').tokens);
  // A leading `{`/trailing `}` wrap the whole module now too: the Haskell
  // report's own top-level layout rule applies even without `module X where`.
  assert.deepEqual(tokens.filter(token => token.kind === 'symbol').map(token => token.text), ['{', '=', '{', '=', ';', '=', '}', '+', '}']);
});

test('does not treat a brace character literal as explicit layout punctuation', () => {
  const tokens = applyLayout(lex('main = do\n  token \'{\'\n  value <- next\n  token \'}\'\n', 'CharLayout.hs').tokens);
  assert.deepEqual(tokens.filter(token => token.kind === 'char').map(token => token.text), ['{', '}']);
  assert.deepEqual(tokens.filter(token => token.virtual).map(token => token.text), ['{', '{', ';', ';', '}', '}']);
});

test('retains constraints on ordinary top-level signatures', () => {
  const parsed = parseModule('module Main where\nmerge :: Semigroup a => a -> a -> a\nmerge left right = left\n', 'ConstrainedSignature.hs');
  const checked = checkModule(parsed.module.ast, 'ConstrainedSignature.hs');
  assert.deepEqual(checked.constraints.get('Main.merge'), ['Semigroup a']);
});

test('represents type-constructor applications structurally in signatures', () => {
  const good = parseModule('module Main where\nf :: Maybe Int -> Maybe Int\nf x = x\n', 'TypeApplication.hs');
  const checked = checkModule(good.module.ast, 'TypeApplication.hs');
  assert.deepEqual(checked.diagnostics, []);
  assert.equal(checked.types.get('Main.f'), 'Maybe Int -> Maybe Int');

  const bad = parseModule('module Main where\nf :: Maybe Int -> Maybe String\nf x = x\n', 'TypeApplicationMismatch.hs');
  const rejected = checkModule(bad.module.ast, 'TypeApplicationMismatch.hs');
  assert.ok(rejected.diagnostics.some(diagnostic => diagnostic.code === 'E_TYPE' && /Int.*String/.test(diagnostic.message)));
});

test('preserves data declaration parameters in polymorphic constructor schemes', () => {
  const parsed = parseModule('module Main where\ndata Maybe a = Nothing | Just a\nkeep :: Maybe Int -> Maybe Int\nkeep (Just x) = Just x\nkeep Nothing = Nothing\n', 'PolymorphicData.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const declaration = parsed.module.ast.declarations.find(item => item.tag === 'data');
  assert.deepEqual(declaration.parameters, ['a']);
  const checked = checkModule(parsed.module.ast, 'PolymorphicData.hs');
  assert.deepEqual(checked.diagnostics, []);
  assert.equal(checked.types.get('Main.keep'), 'Maybe Int -> Maybe Int');
});

test('retains class and instance headers for the dictionary-lowering phase', () => {
  const parsed = parseModule('module Main where\nclass Render a where\n  render :: a -> String\ninstance Render Int where\n  render _ = "int"\n', 'Classes.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const [klass, instance] = parsed.module.ast.declarations;
  assert.deepEqual({ tag: klass.tag, name: klass.name, parameters: klass.parameters }, { tag: 'class', name: 'Render', parameters: ['a'] });
  assert.deepEqual(klass.members.map(member => member.tag === 'signature' ? [member.name, member.type] : member.tag), [['render', 'a -> String']]);
  assert.deepEqual({ tag: instance.tag, head: instance.head }, { tag: 'instance', head: 'Render Int' });
  const checked = checkModule(parsed.module.ast, 'Classes.hs');
  assert.equal(checked.diagnostics.filter(diagnostic => diagnostic.code === 'E_UNSUPPORTED').length, 0);
});

test('retains lossless instance member slices for dictionary lowering', () => {
  const parsed = parseModule('module Classes where\nclass Render a where\n  render :: a -> String\ninstance Render Int where\n  render value = "number"\n', 'ClassMembers.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const instance = parsed.module.ast.declarations.find(declaration => declaration.tag === 'instance');
  assert.deepEqual(instance.rawMembers[0].tokens.slice(0, 3), ['render', 'value', '=']);
});

test('class dictionary analysis distinguishes signatures, infix methods, and associated types', () => {
  const parsed = parseModule('module Classes where\nclass Compose a where\n  type Index a\n  combine :: Semigroup a => a -> a -> a\ninstance Compose Int where\n  left <> right = left\n', 'DictionaryMembers.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const classDeclaration = parsed.module.ast.declarations.find(declaration => declaration.tag === 'class');
  const instance = parsed.module.ast.declarations.find(declaration => declaration.tag === 'instance');
  // An associated type is no longer a raw member slice: the parser lifts it
  // onto the declaration, where `src/elaborate.ts` reads it as the extra class
  // parameter the class's own parameter determines.
  assert.deepEqual(classDeclaration.associatedTypes, [{ name: 'Index' }]);
  assert.deepEqual(classMembers(classDeclaration).map(member => [member.kind, member.name]), [['signature', 'combine']]);
  assert.deepEqual(instanceMembers(instance).map(member => [member.kind, member.name]), [['method', '<>']]);
  assert.deepEqual(instanceMethodValues(instance).map(value => value.name), ['<>']);
  const table = collectDictionaries([parsed.module.ast]);
  assert.equal(table.classes.get('Classes.Compose').members[0].name, 'combine');
  assert.deepEqual(table.instances[0].values.map(value => value.name), ['<>']);
  assert.deepEqual(instanceHead('Eq Int'), { className: 'Eq', target: 'Int' });
  assert.equal(selectInstance(table, 'Compose', 'Int').instance.methods[0].name, '<>');
  const parameterized = parseModule('module P where\nclass Equal a where\n  equal :: a -> a -> Bool\ninstance Equal (Maybe value) where\n  equal left right = True\n', 'ParameterizedInstance.hs');
  const match = selectInstance(collectDictionaries([parameterized.module.ast]), 'Equal', 'Maybe Int');
  assert.equal(match.substitutions.get('value'), 'Int');
  const checked = checkModule(parsed.module.ast, 'DictionaryMembers.hs');
  assert.equal(checked.dictionaries.classes.get('Classes.Compose').name, 'Compose');
  assert.deepEqual(checked.dictionaries.instances[0].values.map(value => value.name), ['<>']);
  assert.deepEqual(checked.constraints.get('Classes.combine'), ['Semigroup a']);
});

test('infix instance equations treat each operand as one constructor pattern', () => {
  const parsed = parseModule('module Classes where\nclass Semigroup a where\n  (<>) :: a -> a -> a\ndata Options = Options Bool Bool\ninstance Semigroup Options where\n  Options p1 s1 <> Options p2 s2 = Options p1 s2\n', 'InfixSemigroup.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const instance = parsed.module.ast.declarations.find(declaration => declaration.tag === 'instance');
  const values = instanceMethodValues(instance);
  assert.equal(values[0].equations[0].patterns.length, 2);
  assert.equal(values[0].equations[0].patterns[0].tag, 'con');
  assert.equal(values[0].equations[0].patterns[1].tag, 'con');
});

test('instance method equations keep record wildcards as a single constructor pattern', () => {
  const parsed = parseModule('module Classes where\nclass ToJSVal a where\n  toJSVal :: a -> Int\ndata Rec = Rec { recN :: Int }\ninstance ToJSVal Rec where\n  toJSVal Rec {..} = recN\n', 'RecordWildcardInstance.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const instance = parsed.module.ast.declarations.find(declaration => declaration.tag === 'instance');
  const values = instanceMethodValues(instance);
  assert.equal(values.length, 1);
  assert.equal(values[0].name, 'toJSVal');
  assert.equal(values[0].equations[0].patterns.length, 1);
  assert.equal(values[0].equations[0].patterns[0].tag, 'record');
  assert.equal(values[0].equations[0].patterns[0].name, 'Rec');
  assert.equal(values[0].equations[0].patterns[0].wildcard, true);
});

test('instance method equations keep string literals instead of turning them into identifiers', () => {
  const parsed = parseModule('module Classes where\nclass ToJSVal a where\n  toJSVal :: a -> Int\ndata Rec = Rec\ninstance ToJSVal Rec where\n  toJSVal Rec = get "staticKey"\nget _ = 42\n', 'StringLiteralInstance.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const instance = parsed.module.ast.declarations.find(declaration => declaration.tag === 'instance');
  const values = instanceMethodValues(instance);
  assert.equal(values.length, 1);
  const body = values[0].equations[0].guards[0].body;
  assert.equal(body.tag, 'app');
  assert.equal(body.arg.tag, 'string');
  assert.equal(body.arg.value, 'staticKey');
});

test('parses do-local let bindings without an expression-level in', () => {
  const parsed = parseModule('module Main where\nmain = do\n  let x = 41\n  pure (x + 1)\n', 'DoLet.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const main = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value' && declaration.name === 'main');
  assert.equal(main.equations[0].guards[0].body.tag, 'do');
});

test('keeps qualified symbolic constructors intact in patterns', () => {
  const parsed = parseModule('module Main where\nf (x S.:<| xs) = x\n', 'QualifiedPattern.hs');
  assert.deepEqual(parsed.diagnostics, []);
});

test('lexes long user-defined operators as one token', () => {
  const tokens = lex('(<##) x = x\n', 'Operators.hs').tokens;
  assert.ok(tokens.some(token => token.text === '<##'));
});

test('retains parenthesized symbolic operator signatures and definitions', () => {
  const parsed = parseModule('module Util where\n(=:) :: a -> b -> (a, b)\na =: b = (a, b)\n', 'OperatorDeclaration.hs');
  assert.deepEqual(parsed.diagnostics, []);
  assert.deepEqual(parsed.module.ast.declarations.map(declaration => [declaration.tag, declaration.name]), [['signature', '=:',], ['value', '=:',]]);
});

test('retains nested parenthesized operator items in import lists', () => {
  const parsed = parseModule('module Main where\nimport Util ((=:))\nmain = 1\n', 'OperatorImport.hs');
  assert.deepEqual(parsed.diagnostics, []);
  assert.deepEqual(parsed.module.ast.imports[0].exposing, ['=:']);
});

test('retains constructor wildcards in explicit import lists', () => {
  const parsed = parseModule('module Main where\nimport Data.Maybe (Maybe(..))\nmain = Just 1\n', 'ConstructorImport.hs');
  assert.deepEqual(parsed.diagnostics, []);
  assert.deepEqual(parsed.module.ast.imports[0].exposing, ['Maybe']);
  assert.deepEqual(parsed.module.ast.imports[0].exposingConstructors, ['Maybe']);
});

test('counts each atomic constructor field, including Type then type-variable', () => {
  const parsed = parseModule(
    'module Effect where\ndata Thread = BTS | MTS\ndata Schedule a = CrossThread Thread a | ContextModify (a -> a)\n',
    'Schedule.hs',
  );
  assert.deepEqual(parsed.diagnostics, []);
  const thread = parsed.module.ast.declarations.find((declaration) => declaration.name === 'Thread');
  const schedule = parsed.module.ast.declarations.find((declaration) => declaration.name === 'Schedule');
  assert.deepEqual(
    thread.constructors.map((constructor) => [constructor.name, constructor.arity]),
    [['BTS', 0], ['MTS', 0]],
  );
  assert.deepEqual(
    schedule.constructors.map((constructor) => [constructor.name, constructor.arity]),
    [['CrossThread', 2], ['ContextModify', 1]],
  );
});

test('a type synonym for a string literal keeps its quotes', () => {
  const parsed = parseModule('module M where\ntype Foo = "foo"\n', 'Sym.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const alias = parsed.module.ast.declarations.find((declaration) => declaration.tag === 'typeAlias');
  // `KnownSymbol` solving keys on the quoted spelling, so dropping the quotes
  // here left `Proxy Foo` with no symbol to match.
  assert.equal(alias.target, '"foo"');
});

test('does not treat deriving as a constructor field or type argument', () => {
  const parsed = parseModule(
    'module Model where\ndata Feed = FeedHome | FeedChannel MisoString\n  deriving (Eq)\n',
    'Feed.hs',
  );
  assert.deepEqual(parsed.diagnostics, []);
  const feed = parsed.module.ast.declarations.find((declaration) => declaration.tag === 'data');
  assert.deepEqual(
    feed.constructors.map((constructor) => [constructor.name, constructor.arity]),
    [['FeedHome', 0], ['FeedChannel', 1]],
  );
  assert.deepEqual(feed.deriving, ['Eq']);
});

test('retains existential and constrained constructor binders', () => {
  const parsed = parseModule('module Types where\ndata Box = forall a. Box a | (Eq a) => Constrained a\n', 'ExistentialData.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const declaration = parsed.module.ast.declarations.find(item => item.tag === 'data');
  assert.deepEqual(declaration.constructors.map(constructor => constructor.name), ['Box', 'Constrained']);
});

test('does not confuse a list-comprehension guard with a later generator', () => {
  const parsed = parseModule('module Main where\nmain = [ x | True, x <- [1] ]\n', 'ListGuard.hs');
  assert.deepEqual(parsed.diagnostics, []);
});

test('lexes Template Haskell type names and JavaScript quasiquotes', () => {
  const tokens = lex("makeLenses ''Model\nplay id = [js| document.getElementById(${id}) |]\n", 'TH.hs').tokens;
  assert.ok(tokens.some(token => token.text === "''"));
  const quote = tokens.find(token => token.kind === 'quasiquote');
  assert.equal(quote?.quoter, 'js');
  assert.match(quote?.text ?? '', /getElementById/);
});

test('lexes decimal character escapes in string literals', () => {
  const tokens = lex('module Main where\nmain = "a\\8212b"\n', 'Dash.hs').tokens;
  const string = tokens.find(token => token.kind === 'string');
  assert.equal(string?.text, 'a\u2014b');
});

test('parses arithmetic sequences and expands makeLenses', () => {
  const parsed = parseModule('module Model where\ndata Model = Model { _count :: Int }\nmakeLenses \'\'Model\nmain = [0 ..]\n', 'Lenses.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const names = parsed.module.ast.declarations.filter(declaration => declaration.tag === 'value').map(declaration => declaration.name);
  assert.ok(names.includes('count'));
  const main = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value' && declaration.name === 'main');
  assert.equal(main.equations[0].guards[0].body.fn.name, 'enumFrom');
});

test('expands the js quasi-quoter to createWith and inline like Miso.FFI.QQ', () => {
  const parsed = parseModule(
    'module Main where\nplay id = [js| document.getElementById(${id}) |]\nscroll = [js| window.scrollTo(0, 0); |]\n',
    'QQ.hs',
  );
  assert.deepEqual(parsed.diagnostics, []);
  const play = parsed.module.ast.declarations.find((declaration) => declaration.tag === 'value' && declaration.name === 'play');
  const playBody = play.equations[0].guards[0].body;
  assert.equal(playBody.tag, 'do');
  assert.equal(playBody.statements[0].source.fn.name, 'createWith');
  assert.equal(playBody.statements[1].expr.fn.fn.name, 'inline');
  assert.match(playBody.statements[1].expr.fn.arg.value, /getElementById\(a0\)/);
  const scroll = parsed.module.ast.declarations.find((declaration) => declaration.tag === 'value' && declaration.name === 'scroll');
  const scrollBody = scroll.equations[0].guards[0].body;
  assert.equal(scrollBody.statements[0].source.name, 'create');
  assert.equal(scrollBody.statements[1].expr.fn.arg.value.includes('window.scrollTo'), true);
});

test('recognizes tuple-pattern list-comprehension generators', () => {
  const parsed = parseModule('module Main where\nmain = [ k | (k, Just v) <- pairs ]\n', 'TupleGenerator.hs');
  assert.deepEqual(parsed.diagnostics, []);
});

test('parses comma-separated guards as conjunctions', () => {
  const parsed = parseModule('module Main where\nf x | x == 1, True = 1\n    | otherwise = 0\n', 'Guards.hs');
  assert.deepEqual(parsed.diagnostics, []);
});

test('parses generic right operator sections without preprocessing source text', () => {
  const parsed = parseModule('module Main where\nmain action = withSink (action >>=)\n', 'Sections.hs');
  assert.deepEqual(parsed.diagnostics, []);
});

test('parses parenthesized (op expr) right sections and unary minus', () => {
  const parsed = parseModule(
    'module Main where\nmain hits = sortOn (negate . (^. videoViews) . snd) hits\nskip = ActionSkip (-5)\n',
    'RightSection.hs',
  );
  assert.deepEqual(parsed.diagnostics, []);
  const find = (node) => {
    if (!node || typeof node !== 'object') return undefined;
    if (node.tag === 'lambda' && node.body?.fn?.fn?.name === '^.') return node;
    for (const value of Object.values(node)) {
      const found = Array.isArray(value) ? value.map(find).find(Boolean) : find(value);
      if (found) return found;
    }
  };
  assert.equal(find(parsed.module.ast)?.body?.arg?.name, 'videoViews');
  const skip = parsed.module.ast.declarations.find(
    (declaration) => declaration.tag === 'value' && declaration.name === 'skip',
  );
  assert.equal(skip.equations[0].guards[0].body.arg.fn.name, 'negate');
});

test('composition binds tighter than lens view', () => {
  const parsed = parseModule('module Main where\nmain q k = q ^. queue . at k\n', 'ComposeView.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value').equations[0].guards[0].body;
  assert.equal(body.fn.fn.name, '^.');
  assert.equal(body.arg.fn.fn.name, '.');
});

test('treats lowercase.ident as composition rather than qualification', () => {
  const parsed = parseModule('module Main where\nmain q k = q & queue.at k .~ k\n', 'QueueAt.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const tokens = lex('queue.at k', 'QueueAt.hs').tokens.filter(token => token.kind !== 'newline' && token.kind !== 'eof');
  assert.deepEqual(tokens.map(token => token.text), ['queue', '.', 'at', 'k']);
});

test('keeps visible type applications in expressions', () => {
  const parsed = parseModule('module Main where\nmain = readIORef @Int ref\n', 'TypeApp.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value').equations[0].guards[0].body;
  assert.equal(body.tag, 'app');
  assert.equal(body.arg.name, 'ref');
  assert.equal(body.fn.tag, 'typeApp');
  assert.equal(body.fn.type, 'Int');
  assert.equal(body.fn.expr.name, 'readIORef');
});

test('an as-pattern is not a visible type application', () => {
  const parsed = parseModule('module Main where\nmain xs@(y : ys) = y\n', 'AsPattern.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const pattern = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value').equations[0].patterns[0];
  assert.equal(pattern.tag, 'as');
  assert.equal(pattern.name, 'xs');
  assert.equal(pattern.pattern.tag, 'con');
});

test('parses qualified identifiers used as backticked infix operators', () => {
  const parsed = parseModule('module Main where\nmain value = prefix `Util.combine` value\n', 'Backticks.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value').equations[0].guards[0].body;
  assert.equal(body.tag, 'app');
  assert.equal(body.fn.fn.name, 'Util.combine');
});

test('parses qualified symbolic operators and left sections', () => {
  const parsed = parseModule('module Main where\nimport qualified Data.Sequence as S\nappend xs x = xs S.|> x\nsection x = (S.|> x)\n', 'QualifiedOp.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const append = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value' && declaration.name === 'append').equations[0].guards[0].body;
  assert.equal(append.tag, 'app');
  assert.equal(append.fn.fn.name, 'S.|>');
  const section = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value' && declaration.name === 'section').equations[0].guards[0].body;
  assert.equal(section.tag, 'lambda');
  assert.equal(section.body.fn.fn.name, 'S.|>');
});

test('parses parenthesized constructor and unit patterns as single lambda parameters', () => {
  const parsed = parseModule('module Main where\ndata VTree = VTree Int\nf = \\_model sink (VTree n) logLevel events -> n\ng = \\() _ _ -> 1\n', 'LambdaPatterns.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const countParams = (expr) => {
    let depth = 0;
    let current = expr;
    while (current) {
      if (current.tag === 'lambda') {
        depth++;
        current = current.body;
        continue;
      }
      if (current.tag === 'case') {
        current = current.alternatives[0].body;
        continue;
      }
      break;
    }
    return depth;
  };
  const f = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value' && declaration.name === 'f').equations[0].guards[0].body;
  assert.equal(countParams(f), 5);
  let current = f;
  while (current.tag === 'lambda' && current.body.tag !== 'case') current = current.body;
  assert.equal(current.body.tag, 'case');
  assert.equal(current.body.alternatives[0].pattern.tag, 'con');
  assert.equal(current.body.alternatives[0].pattern.name, 'VTree');
  const g = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value' && declaration.name === 'g').equations[0].guards[0].body;
  assert.equal(countParams(g), 3);
});

test('the generated RTS reproduces GHC rts.js symbols', async () => {
  // GHC writes rts.js from `jsOptimize (jStgStatToJS <$> rts cfg)` alone, so
  // it is a self-contained parity target: every symbol in it is something
  // GHC.StgToJS.Rts.Rts or GHC.StgToJS.Apply generated. The oracle is real
  // GHC 9.12.2 output for the miso counter.
  const { renderRts } = await import('../dist/stg-js/rts.js');
  const emitted = renderRts();
  const defined = (source) => {
    const names = new Set();
    for (const m of source.matchAll(/^(?:function|var|const|let)\s+(h\$[A-Za-z0-9_$]+)/gm)) names.add(m[1]);
    return names;
  };
  const ours = defined(emitted);
  // Whole families, not a sample: a partial family means the generator's
  // arity/bitmap enumeration drifted from GHC's.
  for (const [prefix, count] of [['h$r', 31], ['h$l', 32], ['h$p', 32], ['h$c', 25], ['h$d', 24], ['h$ret', 10]]) {
    const found = [...ours].filter((n) => new RegExp(`^${prefix.replace('$', '\\$')}\\d+$`).test(n));
    assert.equal(found.length, count, `${prefix}N: expected ${count}, got ${found.length}`);
  }
  // Partial stack pushes are keyed by bitmap, and a bitmap whose set bits are
  // all consecutive from 0 is already an h$pN, so those are skipped.
  const ppush = [...ours].filter((n) => /^h\$pp\d+$/.test(n));
  assert.equal(ppush.length, 247);
  assert.ok(ours.has('h$closureTypeName'));
  assert.ok(ours.has('h$getReg') && ours.has('h$setReg'));
});

test('the generated RTS behaves the same as real GHC rts.js', async () => {
  // A differential test against the golden oracle - real GHC 9.12.2 output
  // for the miso counter. Comparing behaviour, not text, is what catches a
  // port that reads plausibly but computes the wrong thing: this is how the
  // `toJExpr ClosureType` bug (ctNum, not the derived Enum) was found.
  const { renderRts } = await import('../dist/stg-js/rts.js');
  const oracle = await readFile('references/miso-lynx/oracle-jsexe/rts.js', 'utf8');
  // Symbols the oracle's rts.js references but that live in lib.js.
  const external = ['h$o', 'h$static_thunk', 'h$rs', 'h$init_closure', 'h$sti', 'h$stl', 'h$stc', 'h$log', 'h$traceAlloc'];
  const probe = `; return { c2: h$c2, tn: h$closureTypeName, get: h$getReg, set: h$setReg, l3: h$l3, p2: h$p2, pp5: h$pp5,
    reset: () => { h$stack = new Array(10).fill(0); h$sp = 0; },
    snap: () => [h$sp, h$stack.slice(0, 6)], regs: () => [h$r1, h$r2, h$r3] };`;
  const load = (source) => new Function(...external, source + probe)(...external.map(() => () => {}));
  const ours = load(renderRts());
  const theirs = load(oracle);
  const agree = (what, f) => assert.deepEqual(f(ours), f(theirs), what);

  agree('h$c2 allocates the same closure shape', (g) => g.c2('F', 'x', 'y'));
  // -1 is StackFrame and 4 names nothing: the tags come from ctNum, which is
  // a different numbering from ClosureType's derived Enum.
  agree('h$closureTypeName maps every tag alike', (g) => [-1, 0, 1, 2, 3, 4, 5, 9].map(g.tn));
  agree('registers round-trip through get/set', (g) => { g.set(7, 42); return g.get(7); });
  agree('h$l3 fills registers in descending order', (g) => { g.l3('a', 'b', 'c'); return g.regs(); });
  agree('h$p2 pushes two stack slots', (g) => { g.reset(); g.p2('u', 'v'); return g.snap(); });
  agree('h$pp5 pushes the slots its bitmap names', (g) => { g.reset(); g.pp5('u', 'v'); return g.snap(); });
});

test('derived ToJSON/FromJSON methods match aeson defaults and parse', async () => {
  const { derivedJsonSource } = await import('../dist/sugar.js');
  const span = { start: 0, end: 0, line: 1, column: 1 };
  const rec = {
    tag: 'data',
    name: 'User',
    surfaceName: 'User',
    parameters: [],
    constructors: [{
      name: 'User',
      arity: 2,
      fields: ['userId', 'bio'],
      fieldTypes: ['Int', 'Maybe JSString'],
      surface: { name: 'User', fields: ['userId', 'bio'] },
    }],
    deriving: ['Generic'],
    derivingAnyclass: ['ToJSON', 'FromJSON'],
    span,
  };
  const sum = {
    tag: 'data',
    name: 'Tab',
    surfaceName: 'Tab',
    parameters: [],
    constructors: ['Home', 'Search'].map((name) => ({
      name,
      arity: 0,
      surface: { name },
    })),
    deriving: ['Generic'],
    derivingAnyclass: ['ToJSON', 'FromJSON'],
    span,
  };
  const tagged = {
    tag: 'data',
    name: 'Screen',
    surfaceName: 'Screen',
    parameters: [],
    constructors: [
      { name: 'ScreenTab', arity: 0, surface: { name: 'ScreenTab' } },
      { name: 'ScreenProfile', arity: 1, fieldTypes: ['Int'], surface: { name: 'ScreenProfile' } },
      { name: 'ScreenViewer', arity: 2, fieldTypes: ['Int', 'Int'], surface: { name: 'ScreenViewer' } },
    ],
    deriving: ['Generic'],
    derivingAnyclass: ['ToJSON', 'FromJSON'],
    span,
  };
  const source = derivedJsonSource([rec, sum, tagged]);
  assert.match(source, /toJSON \(User x0 x1\) = object/);
  assert.match(source, /fromString "userId"/);
  assert.match(source, /o \.:\? \(fromString "bio"\)/);
  assert.match(source, /toJSON Home = fromString "Home"/);
  assert.match(source, /withText \(fromString "Tab"\)/);
  assert.match(source, /fromString "tag"\) \.= \(fromString "ScreenProfile"\)/);
  assert.match(source, /fromString "contents"\) \.= \(\(x0, x1\)\)/);
  assert.doesNotMatch(source, /genericToJSON|genericParseJSON/);
  const parsed = parseModule(source, 'GHCTS/DerivedJSON.hs');
  assert.deepEqual(parsed.diagnostics.filter((d) => d.severity === 'error'), []);
  const instances = parsed.module.ast.declarations.filter((d) => d.tag === 'instance');
  assert.equal(instances.length, 6);
  for (const inst of instances) {
    const methods = instanceMethodValues(inst, 'GHCTS/DerivedJSON.hs');
    assert.ok(methods.length > 0, `instance ${inst.head} dropped its methods on re-parse`);
  }
});
