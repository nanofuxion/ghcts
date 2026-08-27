import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import test from 'node:test';
import { checkModule, classMembers, collectDictionaries, compileProject, instanceHead, instanceMembers, instanceMethodValues, lowerModule, selectInstance, serveProject } from '../dist/index.js';
import { applyLayout, lex, preprocess } from '../dist/lexer.js';
import { parseModule } from '../dist/parser.js';
import { collectInterface } from '../dist/interface.js';
import { parseCabalLibrary } from '../dist/cabal.js';
import { apply, field, foreignFunction, force, fromJSValAs, isTrue, jsValue, lazy, prelude, prop, registerConstructorType, runFiber } from '../dist/runtime.js';

async function project(source, targets = ['node']) {
  const directory = await mkdtemp(join(tmpdir(), 'ghcts-core-'));
  await writeFile(join(directory, 'ghcts.json'), JSON.stringify({ version: 1, sourceRoots: ['.'], entry: { module: 'Main', export: 'main' }, targets, outDir: 'dist' }));
  await writeFile(join(directory, 'Main.hs'), source);
  return directory;
}

test('compiles generic functions and infix expressions to ESM TypeScript', async () => {
  const directory = await project('module Main where\ninc x = x + 1\nmain = inc (2 * 3)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /prelude\.add/);
    assert.doesNotMatch(generated, /Miso|Counter/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?generic`);
    assert.equal(main(), 7);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('show recurses into compound values instead of only printing the constructor tag', () => {
  const list = { tag: ':', fields: [1, { tag: ':', fields: [-2, { tag: ':', fields: [3, { tag: '[]', fields: [] }] }] }] };
  assert.equal(prelude.show(list), '[1,-2,3]');
  assert.equal(prelude.show({ tag: 'Just', fields: [-5] }), 'Just (-5)');
  assert.equal(prelude.show({ tag: 'Nothing', fields: [] }), 'Nothing');
  assert.equal(prelude.show({ tag: '(,,)', fields: [1, 2, 3] }), '(1,2,3)');
  assert.equal(prelude.show(-5), '-5');
  assert.equal(prelude.show({ tag: 'Left', fields: [5] }), 'Left 5');
  assert.equal(prelude.show('hello\nworld'), '"hello\\nworld"');
});

test('a bare negative literal parses as negate, not a partially applied subtraction', async () => {
  const directory = await project('module Main where\ny :: Int\ny = -5\nmain = y\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?negLit`);
    assert.equal(main(), -5);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('div/mod round toward negative infinity like real Haskell, not toward zero', () => {
  assert.equal(prelude.div(-7)(2), -4);
  assert.equal(prelude.mod(-7)(2), 1);
  assert.equal(prelude.div(7)(-2), -4);
  assert.equal(prelude.mod(7)(-2), -1);
  const [q, r] = prelude.divMod(-7)(2).fields.map((f) => force(f));
  assert.equal(q, -4);
  assert.equal(r, 1);
});

test('++ concatenates plain Haskell Strings, not just cons-list-shaped lists', async () => {
  const directory = await project('module Main where\nmain = putStrLn ("hello " ++ "world")\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /prelude\.appendList/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?appendListString`);
    let logged = '';
    const originalLog = console.log;
    console.log = (msg) => { logged = msg; };
    try { main(); } finally { console.log = originalLog; }
    assert.equal(logged, 'hello world');
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('quot/rem truncate toward zero, unlike div/mod', () => {
  assert.equal(prelude.quot(-7)(2), -3);
  assert.equal(prelude.rem(-7)(2), -1);
  const [q, r] = prelude.quotRem(-7)(2).fields.map((f) => force(f));
  assert.equal(q, -3);
  assert.equal(r, -1);
});

test('jsg-style globalThis lookup returns the global object', () => {
  assert.equal(prop(globalThis, 'globalThis'), globalThis);
});

test('force does not treat host objects as thunks when in lies', () => {
  const host = new Proxy({ tag: 'view' }, { has: () => true });
  assert.equal(force(host), host);
  assert.equal(force(0), 0);
  assert.equal(force(lazy(() => 7)), 7);
});

test('field access on host objects does not throw when properties are missing', () => {
  const host = new Proxy(
    {},
    {
      get() {
        throw new TypeError('value has no property');
      },
      ownKeys() {
        throw new TypeError('value has no property');
      },
      has() {
        throw new TypeError('value has no property');
      },
      getOwnPropertyDescriptor() {
        throw new TypeError('value has no property');
      },
    },
  );
  assert.equal(force(field(host, 'className')), force(prelude.unit));
  assert.throws(() => apply(host, lazy(() => 1)), /Attempted to apply a non-function/);
  assert.equal(fromJSValAs('Rec', lazy(() => host)), host);
  assert.equal(isTrue(host), true);
  assert.equal(isTrue({ tag: 'False', fields: [] }), false);
  assert.equal(isTrue({ tag: 'True', fields: [] }), true);
});

test('foreign constructor records may omit fields like GHCJS FromJSVal records', () => {
  registerConstructorType('PartialWire', 'PartialWire', ['wireType', 'wirePayload']);
  const decoded = fromJSValAs('PartialWire', lazy(() => ({ wireType: 'READY_ACK' })));
  assert.equal(prop(decoded, 'tag'), 'PartialWire');
  assert.equal(force(field(decoded, 'wireType')), 'READY_ACK');
  assert.equal(force(field(decoded, 'wirePayload')), undefined);
});

test('atomicModifyIORef\' forces pair fields that are already values', async () => {
  const directory = await project('module Main where\nimport Data.IORef\nmain = do\n  r <- newIORef (0 :: Int)\n  x <- atomicModifyIORef\' r (\\n -> (n + 1, n))\n  y <- readIORef r\n  pure (x + y)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?atomic-modify`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('imported Data.IORef writeIORef and modifyIORef\' use Data.IORef, not the importing module', async () => {
  const directory = await project(`module Main where
import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef')
main = do
  r <- newIORef (1 :: Int)
  writeIORef r 40
  modifyIORef' r (\\n -> n + 2)
  readIORef r
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /v_Data_2e_IORef_2e_writeIORef/);
    assert.match(generated, /v_Data_2e_IORef_2e_modifyIORef_27_/);
    assert.doesNotMatch(generated, /v_Main_2e_writeIORef/);
    assert.doesNotMatch(generated, /v_Main_2e_modifyIORef/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?ioref-write-modify`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('FromJSVal instances reconstruct constructor patterns, including null Maybe fields', async () => {
  const directory = await project(`module Main where
import Lib
data Rec = Rec { recN :: Int, recM :: Maybe Int }
instance FromJSVal Rec where
  fromJSVal x = do
    n <- fromJSVal =<< jsN x
    m <- fromJSVal =<< jsM x
    pure (Rec <$> n <*> m)
foreign import javascript unsafe "(() => ({n: 3, m: null}))" jsRec :: a
foreign import javascript unsafe "(($1) => $1.n)" jsN :: a -> IO a
foreign import javascript unsafe "(($1) => $1.m)" jsM :: a -> IO a
foreign import javascript unsafe "(($1) => $1)" fromJSValUnchecked :: a -> IO a
main = do
  Rec {..} <- fromJSValUnchecked jsRec
  case recM of
    Nothing -> recN
    Just k -> recN + k
`);
  try {
    await writeFile(join(directory, 'Lib.hs'), `module Lib where
class FromJSVal a where
  fromJSVal :: a -> IO (Maybe a)
`);
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /registerInstance\("FromJSVal"/);
    assert.match(generated, /fromJSValAs\("Rec"/);
    assert.match(generated, /prop\([^,]+,"tag"\)==="Rec"/);
    assert.doesNotMatch(generated, /\.tag === "Rec"/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?from-jsval-rec`);
    assert.equal(main(), 3);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('FromJSVal instances keep property-name strings and decode constructor tags from JS strings', async () => {
  const directory = await project(`module Main where
import Lib
data Kind = Alpha | Beta
data Rec = Rec { recN :: Int, recK :: Kind }
instance FromJSVal Kind where
  fromJSVal x = do
    m <- fromJSVal x
    case m of
      Just "alpha" -> pure (Just Alpha)
      Just "beta" -> pure (Just Beta)
      _ -> pure Nothing
instance FromJSVal Rec where
  fromJSVal x = do
    n <- fromJSVal =<< jsGet "n" x
    k <- fromJSVal =<< jsGet "ty" x
    pure (Rec <$> n <*> k)
foreign import javascript unsafe "(() => ({n: 3, ty: \\"alpha\\"}))" jsRec :: a
foreign import javascript unsafe "(($1,$2) => $2[$1])" jsGet :: String -> a -> IO a
foreign import javascript unsafe "(($1) => $1)" fromJSValUnchecked :: a -> IO a
main = do
  Rec {..} <- fromJSValUnchecked jsRec
  case recK of
    Alpha -> recN
    Beta -> 0
`);
  try {
    await writeFile(join(directory, 'Lib.hs'), `module Lib where
class FromJSVal a where
  fromJSVal :: a -> IO (Maybe a)
`);
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /"ty"/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?from-jsval-kind`);
    assert.equal(main(), 3);
  } finally { await rm(directory, { recursive: true, force: true }); }
});


test('record selectors named wait are not rewritten to a compiler stub', async () => {
  const directory = await project(`module Main where
data W = W { wait :: Int }
main = wait (W 42)
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?wait-field`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('parking a fiber resumes the do-block instead of restarting main', async () => {
  const directory = await project(`module Main where
import Control.Concurrent
main = do
  putStrLn "start"
  threadDelay 1000
  putStrLn "after"
`);
  const logged = [];
  const original = console.log;
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?park-resume`);
    console.log = value => logged.push(String(value));
    runFiber(main);
    await new Promise(resolve => setTimeout(resolve, 50));
    assert.deepEqual(logged, ['start', 'after']);
  } finally {
    console.log = original;
    await rm(directory, { recursive: true, force: true });
  }
});

test('runs JavaScript animation-frame callbacks through the lazy FFI boundary', () => {
  let timestamp = -1;
  const requestFrame = foreignFunction('(($1) => requestAnimationFrame($1))', 1);
  force(requestFrame(lazy(() => (value) => { timestamp = Number(force(value)); })));
  assert.equal(timestamp, 0);
});

test('invokes host requestAnimationFrame callbacks with a JS timestamp', () => {
  let timestamp = -1;
  const requestFrame = foreignFunction('(($1) => requestAnimationFrame($1))', 1);
  force(requestFrame(lazy(() => (value) => { timestamp = value; })));
  assert.equal(timestamp, 0);
});

test('lowers surface expressions through the explicit Core boundary', () => {
  const parsed = parseModule('module Main where\nmain = let value = 40 in value + 2\n', 'CoreBoundary.hs');
  const core = lowerModule(parsed.module.ast);
  assert.equal(core.bindings[0].name, 'main');
  assert.equal(core.bindings[0].equations[0].guards[0].body.tag, 'let');
});

test('preserves do bind patterns and local declarations in Core', () => {
  const parsed = parseModule('module Main where\nmain = do\n  let n = 1\n  x <- pure n\n  pure x\n', 'CoreDo.hs');
  const body = lowerModule(parsed.module.ast).bindings[0].equations[0].guards[0].body;
  assert.equal(body.tag, 'do');
  assert.deepEqual(body.statements.map(statement => statement.tag), ['let', 'bind', 'expr']);
  assert.equal(body.statements[1].tag === 'bind' && body.statements[1].pattern.tag, 'var');
});

test('links local imported modules before typechecking and lowering', async () => {
  const directory = await project('module Main where\nimport Lib\nmain = double 9\n');
  try {
    await writeFile(join(directory, 'Lib.hs'), 'module Lib where\ndouble x = x * 2\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?modules`);
    assert.equal(main(), 18);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('resolves qualified local module references', async () => {
  const directory = await project('module Main where\nimport qualified Lib as L\nmain = L.double 21\n');
  try {
    await writeFile(join(directory, 'Lib.hs'), 'module Lib where\ndouble x = x * 2\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?qualified`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('lowers duplicate exported names with stable module qualification', async () => {
  const directory = await project('module Main where\nimport qualified Alpha as A\nimport qualified Beta as B\nmain = A.value + B.value\n');
  try {
    await writeFile(join(directory, 'Alpha.hs'), 'module Alpha where\nvalue = 40\n');
    await writeFile(join(directory, 'Beta.hs'), 'module Beta where\nvalue = 2\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const source = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(source, /v_Alpha_2e_value/);
    assert.match(source, /v_Beta_2e_value/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?qualified-collision`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('resolves and lowers an explicit module re-export through its original binding', async () => {
  const directory = await project('module Main where\nimport API\nmain = answer\n');
  try {
    await writeFile(join(directory, 'API.hs'), 'module API (module Lib) where\nimport Lib\n');
    await writeFile(join(directory, 'Lib.hs'), 'module Lib where\nanswer = 42\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?reexport`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('re-exports an explicitly named imported value through a module header', async () => {
  const directory = await project('module Main where\nimport Lib\nmain = fromMaybe 40 (Just 2)\n');
  try {
    await writeFile(join(directory, 'Lib.hs'), 'module Lib (fromMaybe) where\nimport Data.Maybe (fromMaybe)\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?named-re-export`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('generated runtime preserves call-by-need for unused arguments', async () => {
  const directory = await project('module Main where\nfirst x y = x\nmain = first 42 (1 / 0)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?lazy`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles algebraic-data constructors through the common backend', async () => {
  const directory = await project('module Main where\ndata Answer = No | Yes\nmain = Yes\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?adt`);
    assert.deepEqual(main(), { tag: 'Yes', fields: [] });
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles record declarations through their typed constructor', async () => {
  const directory = await project('module Main where\ndata Model = Model { counter :: Int }\nmain = Model 42\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?record-declaration`);
    const model = main();
    assert.equal(model.tag, 'Model');
    assert.equal(model.fields[0].force(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles record construction syntax through the generic constructor', async () => {
  const directory = await project('module Main where\ndata Model = Model { counter :: Int }\nmain = Model { counter = 42 }\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?record-construction`);
    assert.equal(main().fields[0].force(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('constructs records in declaration field order regardless of source order', async () => {
  const directory = await project('module Main where\ndata Pair = Pair { left :: Int, right :: Int }\nmain = case Pair { right = 2, left = 1 } of Pair x y -> x * 10 + y\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?record-field-order`);
    assert.equal(main(), 12);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles record accessors and immutable updates', async () => {
  const directory = await project('module Main where\ndata Model = Model { counter :: Int }\nset record = record { counter = 42 }\nmain = counter (set (Model { counter = 1 }))\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?record-update`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('checks record selector types from their declared field signature', () => {
  const parsed = parseModule('module Main where\ndata Model = Model { counter :: Int }\nbad :: String\nbad = counter (Model 1)\n', 'RecordType.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const data = parsed.module.ast.declarations.find(item => item.tag === 'data');
  assert.deepEqual(data.constructors[0].fieldTypes, ['Int']);
  const checked = checkModule(parsed.module.ast, 'RecordType.hs');
  assert.ok(checked.diagnostics.some(diagnostic => diagnostic.code === 'E_TYPE' && /Int.*String/.test(diagnostic.message)));
});

test('compiles constructor and wildcard case alternatives', async () => {
  const directory = await project('module Main where\ndata Answer = No | Yes\nmain = case Yes of\n  Yes -> 1\n  _ -> 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?case`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('binds constructor fields lazily in case alternatives', async () => {
  const directory = await project('module Main where\ndata Maybe a = Nothing | Just a\nmain = case Just 41 of\n  Just x -> x + 1\n  Nothing -> 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?case-field`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles LambdaCase through the generic pattern matcher', async () => {
  const directory = await project('module Main where\ndata Maybe a = Nothing | Just a\nvalue = \\case\n  Just x -> x\n  Nothing -> 0\nmain = value (Just 42)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?lambda-case`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles recursive lazy let bindings', async () => {
  const directory = await project('module Main where\nmain = let x = 20 + 2 in x\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?let`);
    assert.equal(main(), 22);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles layout-separated recursive let binding groups', async () => {
  const directory = await project('module Main where\nmain = let\n  first = second + 20\n  second = 22\nin first\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?let-group`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles equation-local where binding groups', async () => {
  const directory = await project('module Main where\naddAnswer x = helper + x where\n  helper = 40\nmain = addAnswer 2\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?where-group`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles nested where bindings on a local equation', async () => {
  const directory = await project(`module Main where
outer n = inner n
  where
    inner x = vote x
      where
        vote r
          | r > 0 = r + helper
          | otherwise = 0
        helper = 41
main = outer 1
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?nested-where`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles ordered do-block IO statements', async () => {
  const directory = await project('module Main where\nmain = do\n  putStrLn "first"\n  putStrLn "second"\n'); const logged = []; const original = console.log;
  try {
    const result = await compileProject({ project: directory }); assert.deepEqual(result.diagnostics, []);
    console.log = value => logged.push(value); const { main } = await import(`${join(directory, 'dist/node/main.js')}?do`); main();
    assert.deepEqual(logged, ['first', 'second']);
  } finally { console.log = original; await rm(directory, { recursive: true, force: true }); }
});

test('preserves a do-bind pattern for subsequent statements', async () => {
  const directory = await project('module Main where\nmain = do\n  x <- 41\n  x + 1\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?do-bind`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('types and lowers IO do-bind payloads through pure and bind', async () => {
  const directory = await project('module Main where\nmain :: IO Int\nmain = do\n  x <- pure 41\n  pure (x + 1)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?typed-io`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('mapM_ traverses list values', async () => {
  const directory = await project('module Main where\nimport Data.IORef\nmain = do\n  r <- newIORef 0\n  mapM_ (atomicWriteIORef r) [42]\n  readIORef r\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?mapm-maybe`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('JSString unlines joins with a newline', async () => {
  const directory = await project('module Main where\nimport Data.JSString as J\nmain = J.unlines ["a", "b"]\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?unlines`);
    assert.equal(main(), 'a\nb');
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('forM sequences IO actions instead of lazily mapping them', async () => {
  const directory = await project('module Main where\nimport Control.Monad (forM)\nimport Data.IORef\nmain = do\n  r <- newIORef 0\n  _ <- forM [1, 2, 3] (\\x -> atomicWriteIORef r x >> pure x)\n  readIORef r\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?form-seq`);
    assert.equal(main(), 3);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('Prelude even, min, max, succ, and dropWhile match GHCJS', async () => {
  const directory = await project('module Main where\nmain = (even (2 :: Int), even (3 :: Int), min (1 :: Int) 4, max (1 :: Int) 4, succ (41 :: Int), dropWhile (< 3) [1, 2, 3, 4])\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?prelude-integral`);
    const value = main();
    assert.equal(!!value, true);
    const fields = value.fields.map((field) => {
      const forced = field.force ? field.force() : field;
      if (forced && forced.tag === ':') {
        const items = [];
        let node = forced;
        while (node && node.tag === ':') {
          items.push(node.fields[0].force ? node.fields[0].force() : node.fields[0]);
          node = node.fields[1].force ? node.fields[1].force() : node.fields[1];
        }
        return items;
      }
      return forced && forced.tag === 'True' ? true : forced && forced.tag === 'False' ? false : forced;
    });
    assert.deepEqual(fields, [true, false, 1, 4, 42, [3, 4]]);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('Applicative <*> runs the right-hand IO when fmap of an IO list is empty', async () => {
  const directory = await project('module Main where\nimport Data.IORef\nmain = do\n  r <- newIORef 0\n  _ <- (++) <$> pure ([] :: [Int]) <*> (atomicWriteIORef r 1 >> pure [2])\n  readIORef r\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?io-ap`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('evaluates Haskell Bool constructors in if expressions', async () => {
  const directory = await project('module Main where\ndata Bool = False | True\nmain = if False then 1 else 2\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?bool`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('provides Prelude Bool constructors without a local declaration', async () => {
  const directory = await project('module Main where\nmain = if not False then 42 else 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?prelude-bool`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('supports inclusive numeric comparisons from Prelude', async () => {
  const directory = await project('module Main where\nmain = if 42 >= 42 && 42 <= 42 then 1 else 0\n');
  try { const result = await compileProject({ project: directory }); assert.deepEqual(result.diagnostics, []); const { main } = await import(`${join(directory, 'dist/node/main.js')}?inclusive-comparison`); assert.equal(main(), 1); }
  finally { await rm(directory, { recursive: true, force: true }); }
});

test('compares independently allocated algebraic data structurally', async () => {
  const directory = await project('module Main where\ndata Tree = Leaf Int | Branch Tree Tree\nmain = Branch (Leaf 1) (Leaf 2) == Branch (Leaf 1) (Leaf 2)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?structural-eq`);
    assert.equal(main(), true);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles the Haskell unit value', async () => {
  const directory = await project('module Main where\nmain = ()\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?unit`);
    assert.deepEqual(main(), { tag: '()', fields: [] });
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles tuple literals and tuple patterns lazily', async () => {
  const directory = await project('module Main where\nmain = case (20, 22) of\n  (x, y) -> x + y\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?tuple`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('implements tuple projections and numeric conversion primitives', async () => {
  const directory = await project('module Main where\nmain = fromIntegral (fst (20, 22)) + snd (20, 22)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?tuple-primitives`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles lazy list literals and list patterns', async () => {
  const directory = await project('module Main where\nmain = case [20, 22] of\n  [x, y] -> x + y\n  _ -> 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?list`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('implements polymorphic Prelude map and foldr through the lazy runtime', async () => {
  const directory = await project('module Main where\nmain = foldr (+) 0 (map (\\x -> x * 2) [10, 11])\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?map-foldr`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('implements generic lazy list append through the overloaded append runtime', async () => {
  const directory = await project('module Main where\nmain = foldr (+) 0 ([1] ++ [2, 3])\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?append-list`);
    assert.equal(main(), 6);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('Prelude !! indexes a list', async () => {
  const directory = await project('module Main where\nmain = [10, 20, 42] !! 2\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /prelude\.index/);
    assert.doesNotMatch(generated, /v_Main_2e__21__21_/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?list-index`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('imported !! is the defining module, not Prelude list index', async () => {
  const directory = await project('module Main where\nimport Ops ((!!))\nmain = [0, 1] !! 99\n');
  try {
    await writeFile(join(directory, 'Ops.hs'), 'module Ops where\n(!!) _ _ = 42\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /v_Ops_2e__21__21_/);
    assert.doesNotMatch(generated, /prelude\.index/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?imported-index`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('Prelude last and init treat JavaScript strings as [Char]', () => {
  assert.equal(prelude.last(lazy(() => '2h')), 'h');
  assert.equal(prelude.init(lazy(() => '2h')), '2');
  assert.equal(prelude.last(lazy(() => 'x')), 'x');
  assert.equal(prelude.init(lazy(() => 'x')), '');
  const list = prelude.cons(lazy(() => 10))(lazy(() => prelude.cons(lazy(() => 20))(lazy(() => prelude.cons(lazy(() => 42))(lazy(() => prelude.nil))))));
  assert.equal(prelude.last(lazy(() => list)), 42);
  const prefix = force(prelude.init(lazy(() => list)));
  assert.equal(prefix.tag, ':');
  assert.equal(force(prefix.fields[0]), 10);
  assert.equal(force(force(prefix.fields[1]).fields[0]), 20);
  assert.equal(force(force(prefix.fields[1]).fields[1]).tag, '[]');
});

test('Prelude last and init work on unpacked JSString like longAgo', async () => {
  const directory = await project(`module Main where
import qualified Data.JSString as S
main = case S.unpack "2h" of
  [] -> 0
  cs -> if last cs == last "xh" && init cs == "2" then 1 else 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /prelude\.last/);
    assert.match(generated, /prelude\.init/);
    assert.doesNotMatch(generated, /v_Main_2e_last/);
    assert.doesNotMatch(generated, /v_Main_2e_init/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?last-init-string`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('list index binds tighter than addition', () => {
  const parsed = parseModule('module Main where\nmain = xs !! n + 1\n', 'IndexPrec.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations[0].equations[0].guards[0].body;
  assert.equal(body.fn.fn.name, '+');
  assert.equal(body.fn.arg.fn.fn.name, '!!');
});

test('right-associative cons with append is a flat list', async () => {
  const directory = await project(`module Main where
len [] = 0
len (_:xs) = 1 + len xs
main = len (True : False : [True] ++ [False, True])
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?cons-append-flat`);
    assert.equal(main(), 5);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('nullary constructor arguments on a function equation are not collapsed into one pattern', async () => {
  const directory = await project('module Main where\ndata Mode = Sync | Async\nrun Sync n = n + 1\nrun Async n = n + 2\nmain = run Sync 41\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /\(function\(arg0\) \{return \(function\(arg1\)/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?apat-arity`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('dispatches multiple pattern-matching function equations', async () => {
  const directory = await project('module Main where\ndata Bool = False | True\nisEmpty [] = True\nisEmpty _ = False\nmain = if isEmpty [] then 1 else 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?equations`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles guarded function equations', async () => {
  const directory = await project('module Main where\nchoose x | x > 0 = 1\n         | x < 1 = 2\nmain = choose 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?guards`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('supports otherwise and short-circuit Boolean operators', async () => {
  const directory = await project('module Main where\ndata Bool = False | True\nchoose x | x > 0 = 1\n         | otherwise = 2\nmain = choose 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?otherwise`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles recursive cons-pattern functions', async () => {
  const directory = await project('module Main where\nsum [] = 0\nsum (x:xs) = x + sum xs\nmain = sum [10, 32]\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?sum`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('lowers generic JavaScript foreign imports with curried lazy arguments', async () => {
  const directory = await project('module Main where\nforeign import javascript "($1 + $2)" addJs :: Int -> Int -> Int\nmain = addJs 20 22\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /foreignFunction/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?foreign-import`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('execRWS applies State modify to the model', async () => {
  const directory = await project(`module Main where
import Control.Monad.State (modify)
import Control.Monad.RWS (execRWS)
main = case execRWS (modify (\\n -> n + 1)) () 41 of
  (n, _) -> n
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?execrws`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('State gets projects the model through the RWS effect', async () => {
  const directory = await project(`module Main where
import Control.Monad.State (gets, modify)
import Control.Monad.RWS (execRWS)
action = do
  n <- gets (\\x -> x + 1)
  modify (\\_ -> n)
main = case execRWS action () 41 of
  (n, _) -> n
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /v_Control_2e_Monad_2e_State_2e_gets/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?state-gets`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('Exception catch recovers from a throwing IO action', async () => {
  const directory = await project(`module Main where
import Control.Exception (catch)
foreign import javascript unsafe "(() => { throw new Error(\\"boom\\"); })" boom :: IO Int
foreign import javascript unsafe "(() => 42)" ok :: IO Int
main = boom \`catch\` (\\_ -> ok)
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?io-catch`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('asyncCallback2 applies both JavaScript arguments to the Haskell function', async () => {
  const directory = await project(`module Main where
import GHC.JS.Foreign.Callback (asyncCallback2)
foreign import javascript unsafe "(() => { globalThis.ghctsSum = 0; })" reset :: IO ()
foreign import javascript unsafe "(($1) => { globalThis.ghctsSum = $1; })" writeSum :: Int -> IO ()
foreign import javascript unsafe "(($1) => { $1(40, 2); })" callWithTwo :: Callback -> IO ()
foreign import javascript unsafe "(() => globalThis.ghctsSum)" readSum :: IO Int
main = do
  reset
  cb <- asyncCallback2 $ \\a b -> writeSum 42
  callWithTwo cb
  readSum
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?async-callback2`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('invokes GHCJS_NEW callback-style JavaScript foreign imports', async () => {
  const directory = await project('module Main where\nforeign import javascript unsafe "(($1,$2) => { return $1 + $2; })" addJs :: Int -> Int -> Int\nmain = addJs 40 2\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?ffi-callback`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('checks foreign-import arguments against their declared signature', async () => {
  const directory = await project('module Main where\nforeign import javascript "($1 + 1)" increment :: Int -> Int\nmain = increment "not an Int"\n');
  try {
    const result = await compileProject({ project: directory });
    assert.ok(result.diagnostics.some(diagnostic => diagnostic.code === 'E_TYPE' && /Cannot unify/.test(diagnostic.message)));
    assert.equal(result.outputPaths.length, 0);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('retains JavaScript FFI IO result types as effects', async () => {
  const directory = await project('module Main where\nforeign import javascript "null" jsNull :: IO JSVal\nmain = jsNull\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('re-runs zero-arity IO foreign imports instead of caching the first result', async () => {
  const directory = await project('module Main where\nforeign import javascript unsafe "(() => { globalThis.ghctsTicks = (globalThis.ghctsTicks || 0) + 1; return globalThis.ghctsTicks; })" tick :: IO Int\nmain = do\n  a <- tick\n  b <- tick\n  pure (a + b)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /\bio\(\(function\(\) \{return foreignFunction/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?io-ffi`);
    assert.equal(main(), 3);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('server builds generic browser output through Node only', async () => {
  const directory = await project('module Main where\nmain = putStrLn "hello"\n', ['browser']);
  try {
    const running = await serveProject({ project: directory, port: 0 });
    try { const response = await fetch(running.url); assert.equal(response.status, 200); const html = await response.text(); assert.match(html, /<script>/); assert.doesNotMatch(html, /src="\.\/bootstrap\.js"/); const bootstrap = await readFile(join(directory, 'dist/browser/bootstrap.js'), 'utf8'); assert.match(bootstrap, /ghcts browser startup failed/); assert.match(bootstrap, /ghcts-startup-error/); } finally { await running.close(); }
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('rejects Miso instead of replacing it with an application-specific compiler path', async () => {
  const directory = await project('module Main where\nimport Miso\nmain = startApp defaultEvents app\n');
  try {
    const result = await compileProject({ project: directory });
    assert.ok(result.diagnostics.some(diagnostic => diagnostic.code === 'E_IMPORT'));
    assert.equal(result.outputPaths.length, 0);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('reports source-located type errors before lowering', async () => {
  const directory = await project('module Main where\nmain = 1 + "nope"\n');
  try {
    const result = await compileProject({ project: directory });
    const diagnostic = result.diagnostics.find(item => item.code === 'E_TYPE');
    assert.equal(diagnostic?.line, 2);
    assert.match(diagnostic?.message ?? '', /Cannot unify/);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('preprocesses CPP conditionals before parsing', async () => {
  const directory = await project('module Main where\n#ifdef FEATURE\nmain = 1\n#else\nmain = 2\n#endif\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?cpp`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('retains import qualification and restricts unqualified names to an explicit import list', async () => {
  const directory = await project('module Main where\nimport qualified Lib as API\nimport Other (one)\nmain = API.double one\n');
  try {
    await writeFile(join(directory, 'Lib.hs'), 'module Lib where\ndouble x = x * 2\n');
    await writeFile(join(directory, 'Other.hs'), 'module Other where\none = 21\ntwo = 2\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?import-scope`);
    assert.equal(main(), 42);

    await writeFile(join(directory, 'Main.hs'), 'module Main where\nimport Other (one)\nmain = two\n');
    const rejected = await compileProject({ project: directory, emit: false });
    assert.ok(rejected.diagnostics.some(diagnostic => diagnostic.code === 'E_TYPE' && /Not in scope: two/.test(diagnostic.message)));
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('inserts virtual layout punctuation without losing source tokens', () => {
  const tokens = applyLayout(lex('main = let\n  x = 1\n  y = 2\nin x + y\n', 'Layout.hs').tokens);
  assert.deepEqual(tokens.filter(token => token.kind === 'symbol').map(token => token.text), ['=', '{', '=', ';', '=', '}', '+']);
});

test('does not treat a brace character literal as explicit layout punctuation', () => {
  const tokens = applyLayout(lex('main = do\n  token \'{\'\n  value <- next\n  token \'}\'\n', 'CharLayout.hs').tokens);
  assert.deepEqual(tokens.filter(token => token.kind === 'char').map(token => token.text), ['{', '}']);
  assert.deepEqual(tokens.filter(token => token.virtual).map(token => token.text), ['{', ';', ';', '}']);
});

test('parses the unchanged Miso counter fixture through layout tokens', async () => {
  const file = join(process.cwd(), 'test/fixtures/miso-counter/Main.hs');
  const parsed = parseModule(await readFile(file, 'utf8'), file);
  assert.deepEqual(parsed.diagnostics, []);
  assert.deepEqual(parsed.module.ast.declarations.filter(declaration => declaration.tag !== 'signature').map(declaration => declaration.name), [
    'Model', 'counter', 'Action', 'main', 'app', 'emptyModel', 'updateModel', 'viewModel'
  ]);
  const model = parsed.module.ast.declarations.find(declaration => declaration.tag === 'data' && declaration.name === 'Model');
  assert.deepEqual(model.deriving, ['Show', 'Eq', 'Generic', 'ToJSON', 'FromJSON']);
});

test('retains and enforces simple top-level signatures', async () => {
  const directory = await project('module Main where\ninc :: Int -> Int\ninc x = x + 1\nmain = inc 41\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const source = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(source, /inc :: Int -> Int/);
  } finally { await rm(directory, { recursive: true, force: true }); }
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
  assert.deepEqual(classMembers(classDeclaration).map(member => [member.kind, member.name]), [['associatedType', 'Index'], ['signature', 'combine']]);
  assert.deepEqual(instanceMembers(instance).map(member => [member.kind, member.name]), [['method', '<>']]);
  assert.deepEqual(instanceMethodValues(instance).map(value => value.name), ['<>']);
  const table = collectDictionaries([parsed.module.ast]);
  assert.equal(table.classes.get('Classes.Compose').members[1].name, 'combine');
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

test('Semigroup instance equations append algebraic values through registered dictionaries', async () => {
  const directory = await project(`module Main where
class Semigroup a where
  (<>) :: a -> a -> a
data Options = Options Bool Bool
instance Semigroup Options where
  Options p1 s1 <> Options p2 s2 = Options (p1 || p2) (s1 || s2)
main = case Options True False <> Options False True of
  Options True True -> 1
  _ -> 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?semigroup-options`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('retains a type alias for signature validation', async () => {
  const directory = await project('module Main where\ntype Count = Int\ninc :: Count -> Count\ninc x = x + 1\nmain = inc 41\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('parses reachable real Miso modules under the JavaScript CPP branch', async () => {
  const flags = new Set(['GHCJS_BOTH', 'GHCJS_NEW']);
  for (const relative of ['Miso.hs', 'Miso/Lens.hs', 'Miso/JSON.hs', 'Miso/Event.hs', 'Miso/Fetch.hs', 'Miso/FFI/Internal.hs']) {
    const file = join(process.cwd(), 'references/miso/src', relative);
    const parsed = parseModule(await readFile(file, 'utf8'), file, flags);
    assert.deepEqual(parsed.diagnostics, [], relative);
    assert.ok(parsed.module.ast.declarations.length > 0, relative);
  }
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

test('qualified constructor patterns match the unqualified constructor tag', async () => {
  const directory = await project('module Main where\nimport qualified Types as T\ncross = \\case\n  T.BTS -> 1\n  T.MTS -> 2\nmain = cross T.MTS\n');
  try {
    await writeFile(join(directory, 'Types.hs'), 'module Types where\ndata Thread = BTS | MTS\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /prop\([^,]+,"tag"\)==="MTS"/);
    assert.doesNotMatch(generated, /tag === "T\.MTS"/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?qualified-ctor-tag`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('applies a two-field constructor whose second field is a type variable', async () => {
  const directory = await project('module Main where\ndata Thread = BTS | MTS\ndata Schedule a = CrossThread Thread a\nmain = case CrossThread BTS True of\n  CrossThread BTS True -> 1\n  _ -> 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /constructor\("CrossThread",2\)/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?cross-thread-ctor`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('GHCJS $r FFI statements return the assigned result', () => {
  const object = foreignFunction('$r = {};', 0);
  assert.equal(typeof object, 'object');
  assert.notEqual(object, null);
  const setProp = foreignFunction('$3[$1]=$2', 3);
  force(apply(apply(apply(setProp, lazy(() => 'a0')), lazy(() => 'player')), lazy(() => object)));
  assert.equal(object.a0, 'player');
});

test('Miso [js| |] interpolation runs through createWith and inline', async () => {
  const directory = await mkdtemp(join(process.cwd(), '.tmp-ghcts-'));
  await writeFile(join(directory, 'ghcts.json'), JSON.stringify({ version: 1, sourceRoots: ['.'], entry: { module: 'Main', export: 'main' }, dependencies: ['miso'], targets: ['node'], outDir: 'dist' }));
  await writeFile(join(directory, 'Main.hs'), 'module Main where\nimport Miso.DSL (createWith)\nimport Miso.FFI.Internal (inline)\nplayQuiet domId = do\n  o <- createWith [("a0", domId)]\n  inline "var el = document.getElementById(a0); if (el) { var p = el.play(); if (p && p.catch) { p.catch(function(){}); } }" o\nmain = do\n  playQuiet ("player" :: String)\n  pure (0 :: Int)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    globalThis.ghctsPlayCalls = [];
    const player = globalThis.document.createElement('video');
    player.setAttribute('id', 'player');
    player.play = () => {
      globalThis.ghctsPlayCalls.push(player.id || player.getAttribute('id'));
      return Promise.resolve();
    };
    globalThis.document.body.appendChild(player);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?js-inline`);
    main();
    assert.deepEqual(globalThis.ghctsPlayCalls, ['player']);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('ToJSVal of [Char] is a JavaScript string, matching GHCJS h$fromHsString', () => {
  const haskellList = (items) =>
    items.reduceRight((tail, item) => apply(apply(prelude.cons, lazy(() => item)), lazy(() => tail)), prelude.nil);
  assert.equal(jsValue(haskellList(['s', 't', 'y', 'l', 'e'])), 'style');
  assert.deepEqual(jsValue(haskellList([1, 2, 3])), [1, 2, 3]);
  assert.deepEqual(jsValue(haskellList(['style'])), ['style']);
  assert.deepEqual(jsValue(prelude.nil), []);
});

test('property FFI keys convert Haskell strings the way GHCJS h$fromHsString does', () => {
  const haskellList = (items) =>
    items.reduceRight((tail, item) => apply(apply(prelude.cons, lazy(() => item)), lazy(() => tail)), prelude.nil);
  const getProp = foreignFunction('(($1,$2) => { return $2[$1]; })', 2);
  const object = { createElement: 'ok' };
  const result = force(apply(apply(getProp, lazy(() => haskellList([...'createElement']))), lazy(() => object)));
  assert.equal(result, 'ok');
});

test('jsValue leaves host arrow callbacks unwrapped so getVTree receives a JS object', () => {
  const vtree = { type: 1, children: [], events: { captures: {}, bubbles: {} }, domRef: { nodeId: 1 } };
  let received;
  const continuation = (tree) => {
    received = tree;
  };
  const invoke = foreignFunction('(($1,$2,$3) => { return $1.apply($2, $3); })', 3);
  const wrapped = prelude.toJSVal(lazy(() => continuation));
  force(apply(apply(apply(invoke, lazy(() => wrapped)), lazy(() => globalThis)), lazy(() => [vtree])));
  assert.equal(received, vtree);
  assert.equal(received.type, 1);
});

test('invokeFunction FFI uses Function.prototype.apply so PrimJS host methods work', () => {
  const invoke = foreignFunction('(($1,$2,$3) => { return $1.apply($2, $3); })', 3);
  const object = { n: 41, add(x) { return this.n + x; } };
  const result = force(apply(apply(apply(invoke, lazy(() => object.add)), lazy(() => object)), lazy(() => [1])));
  assert.equal(result, 42);
  const detached = function (x) { return this.n + x; };
  Object.setPrototypeOf(detached, null);
  const host = force(apply(apply(apply(invoke, lazy(() => detached)), lazy(() => object)), lazy(() => [1])));
  assert.equal(host, 42);
});

test('Miso DSL global getProp invokeFunction chain does not use new Function', () => {
  const globalF = foreignFunction('(() => { return globalThis; })', 0);
  assert.equal(globalF, globalThis);
  globalThis.__ghctsMisoProbe = { onMTS() { return 7; } };
  try {
    const getProp = foreignFunction('(($1,$2) => { return $2[$1]; })', 2);
    const invoke = foreignFunction('(($1,$2,$3) => { return $1.apply($2, $3); })', 3);
    const miso = force(apply(apply(getProp, lazy(() => '__ghctsMisoProbe')), lazy(() => globalF)));
    const fn = force(apply(apply(getProp, lazy(() => 'onMTS')), lazy(() => miso)));
    const result = force(apply(apply(apply(invoke, lazy(() => fn)), lazy(() => miso)), lazy(() => [])));
    assert.equal(result, 7);
  } finally {
    delete globalThis.__ghctsMisoProbe;
  }
});

test('recognizes tuple-pattern list-comprehension generators', () => {
  const parsed = parseModule('module Main where\nmain = [ k | (k, Just v) <- pairs ]\n', 'TupleGenerator.hs');
  assert.deepEqual(parsed.diagnostics, []);
});

test('list comprehensions bind as-patterns before the constructor test', async () => {
  const directory = await project(`module Main where
main = case [ k | kv@(k, _) <- [(41, True)] ] of
  (n:_) -> n + 1
  _ -> 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?as-listcomp`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('function composition applies right-to-left', async () => {
  const directory = await project('module Main where\nmain = ((+ 2) . (* 2)) 20\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?compose`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('treats lowercase.ident as composition rather than qualification', () => {
  const parsed = parseModule('module Main where\nmain q k = q & queue.at k .~ k\n', 'QueueAt.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const tokens = lex('queue.at k', 'QueueAt.hs').tokens.filter(token => token.kind !== 'newline' && token.kind !== 'eof');
  assert.deepEqual(tokens.map(token => token.text), ['queue', '.', 'at', 'k']);
});

test('skips visible type applications in expressions', () => {
  const parsed = parseModule('module Main where\nmain = readIORef @Int ref\n', 'TypeApp.hs');
  assert.deepEqual(parsed.diagnostics, []);
  const body = parsed.module.ast.declarations.find(declaration => declaration.tag === 'value').equations[0].guards[0].body;
  assert.equal(body.tag, 'app');
  assert.equal(body.fn.name, 'readIORef');
  assert.equal(body.arg.name, 'ref');
});

test('binds names from let constructor and tuple patterns', async () => {
  const directory = await project('module Main where\nmain = let Just x = Just 40 in let (y, z) = (1, 1) in x + y + z\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?let-patterns`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('binds names from do-let record patterns', async () => {
  const directory = await project('module Main where\ndata Box = Box { n :: Int }\nmain = do\n  let Box {..} = Box 41\n  pure (n + 1)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?do-let-record`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('unit patterns accept JS null and Bool equality treats JS booleans as True/False', async () => {
  const directory = await project(`module Main where
g = \\() _ _ -> 1
main = g () True False
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?unit-lambda`);
    assert.equal(main(), 1);
    assert.equal(prop(fromJSValAs('()', lazy(() => null)), 'tag'), '()');
    assert.equal(isTrue(apply(apply(prelude.equal, lazy(() => true)), lazy(() => prelude.true))), true);
    assert.equal(isTrue(apply(apply(prelude.equal, lazy(() => false)), lazy(() => prelude.false))), true);
  } finally { await rm(directory, { recursive: true, force: true }); }
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

test('composes record lenses and looks up Map values with at', () => {
  const lens = (get, set) => ({ tag: 'Lens', fieldNames: ['_get', '_set'], fields: [lazy(() => get), lazy(() => set)] });
  const inner = new Map([[1, 41]]);
  const record = { tag: 'Box', fieldNames: ['_map'], fields: [lazy(() => inner)] };
  const mapLens = lens(
    (value) => field(value, '_map'),
    (next) => (value) => ({ ...force(value), fields: [lazy(() => force(next))] }),
  );
  const composed = prelude.compose(lazy(() => mapLens))(lazy(() => prelude.at(lazy(() => 1))));
  const viewed = force(apply(field(composed, '_get'), lazy(() => record)));
  assert.equal(viewed.tag, 'Just');
  assert.equal(force(viewed.fields[0]), 41);
});

test('Map insert FFI keeps Haskell records instead of flattening them', () => {
  const insert = foreignFunction('(($1,$2,$3) => { const copy = new Map($3); copy.set($1, $2); return copy; })', 3);
  const record = { tag: 'Box', fields: [lazy(() => 41)], fieldNames: ['n'] };
  const map = force(insert(lazy(() => 1))(lazy(() => record))(lazy(() => new Map())));
  assert.equal(map.get(1)?.tag, 'Box');
  assert.equal(force(map.get(1).fields[0]), 41);
});

test('qualified Set.toList uses Data.Set, not the importing module', async () => {
  const directory = await project(`module Main where
import qualified Data.Set as Set
main = case Set.toList (Set.fromList [True, True]) of
  True:_ -> 1
  _ -> 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /v_Data_2e_Set_2e_toList/);
    assert.doesNotMatch(generated, /v_Main_2e_Set_2e_toList/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?set-tolist`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('Set member tests the element against the set', async () => {
  const directory = await project(`module Main where
import qualified Data.Set as Set
main = if Set.member "haskell-miso" (Set.fromList ["haskell-miso"]) then 1 else 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?set-member`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('IntMap lookup returns the original record constructor', async () => {
  const directory = await project(`module Main where
import qualified Data.IntMap.Strict as IM
data Box = Box Int
main = case IM.lookup 1 (IM.insert 1 (Box 41) IM.empty) of
  Just (Box n) -> n + 1
  Nothing -> 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?intmap-record`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('imports record field selectors from a T(..) import list', async () => {
  const directory = await project('module Main where\nimport Lib (Box(..))\nmain = n (Box 41) + 1\n');
  try {
    await writeFile(join(directory, 'Lib.hs'), 'module Lib where\ndata Box = Box { n :: Int }\n');
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?record-fields-import`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('applies lambdas with unit and constructor patterns', async () => {
  const directory = await project('module Main where\ndata Tree = Tree Int\nmain = (\\(Tree n) -> n) (Tree 41) + (\\() _ -> 1) () True\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?lambda-patterns`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('appends sequence elements with the qualified snoc operator', async () => {
  const directory = await project('module Main where\nimport qualified Data.Sequence as S\nmain = S.length ((S.empty S.|> 40) S.|> 2)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?sequence-snoc`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('looks up IntMap values with the qualified index operator', async () => {
  const directory = await project('module Main where\nimport qualified Data.IntMap.Strict as IM\nmain = IM.insert 1 42 IM.empty IM.! 1\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /v_Data_2e_IntMap_2e_Strict_2e__21_/);
    assert.doesNotMatch(generated, /v_Main_2e_IM_2e__21_/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?intmap-index`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('resolves compiler-owned boot interfaces through the ordinary module loader', async () => {
  const directory = await project('module Main where\nimport Data.Maybe\nmain = Just 41\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?boot`);
    assert.equal(main().tag, 'Just');
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('executes declarations from the boot Data.Maybe module through ordinary lowering', async () => {
  const directory = await project('module Main where\nimport Data.Maybe\nmain = fromMaybe 40 (Just 2)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?boot-maybe`);
    assert.equal(main(), 2);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('imported Data.Maybe listToMaybe uses Data.Maybe, not the importing module', async () => {
  const directory = await project(`module Main where
import Data.Maybe (listToMaybe)
main = case listToMaybe [42] of
  Just n -> n
  Nothing -> 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /v_Data_2e_Maybe_2e_listToMaybe/);
    assert.doesNotMatch(generated, /v_Main_2e_listToMaybe/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?list-to-maybe`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('executes Data.Maybe catMaybes using shared lazy list constructors', async () => {
  const directory = await project('module Main where\nimport Data.Maybe\nmain = foldr (+) 0 (catMaybes [Just 20, Nothing, Just 22])\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?boot-cat-maybes`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('executes declarations from the boot Data.Either module through ordinary lowering', async () => {
  const directory = await project('module Main where\nimport Data.Either\nmain = either (\\x -> x + 1) (\\x -> x + 2) (Left 41)\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?boot-either`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('forM_ traverses Right and skips Left', () => {
  const seen = [];
  const collect = (item) => {
    seen.push(force(item));
    return prelude.unit;
  };
  force(apply(apply(prelude.forM_, lazy(() => prelude.right(lazy(() => 12.5)))), lazy(() => collect)));
  assert.deepEqual(seen, [12.5]);
  seen.length = 0;
  force(apply(apply(prelude.forM_, lazy(() => prelude.left(lazy(() => 'no')))), lazy(() => collect)));
  assert.deepEqual(seen, []);
});

test('fromMisoStringEither parses Doubles like Miso.DSL.FFI parseFloat', () => {
  const ok = force(apply(prelude.fromMisoStringEither, lazy(() => '12.5')));
  assert.equal(ok.tag, 'Right');
  assert.equal(force(ok.fields[0]), 12.5);
  const text = force(apply(prelude.fromMisoStringEither, lazy(() => 'type')));
  assert.equal(text.tag, 'Right');
  assert.equal(force(text.fields[0]), 'type');
});

test('fromJSVal converts eventJSON objects that copy nodeType', () => {
  const serialized = { value: '45.2', type: 'range', nodeType: 1, nodeName: 'INPUT', localName: 'input' };
  const decoded = force(apply(prelude.fromJSVal, lazy(() => serialized)));
  assert.equal(decoded.tag, 'Just');
  const value = force(decoded.fields[0]);
  assert.equal(value.tag, 'Object');
  const map = force(value.fields[0]);
  assert.equal(map.get('value').tag, 'String');
  assert.equal(force(map.get('value').fields[0]), '45.2');
  const parsed = force(apply(prelude.parseJSON, lazy(() => map.get('value'))));
  assert.equal(parsed.tag, 'Parser');
  const either = force(parsed.fields[0]);
  assert.equal(either.tag, 'Right');
  assert.equal(force(either.fields[0]), '45.2');
});

test('compiles FromMisoString Double and seeks through forM_ on Right', async () => {
  const directory = await project(`module Main where
class FromMisoString t where
  fromMisoStringEither :: String -> Either String t
instance FromMisoString Double where
  fromMisoStringEither string = Right 99
main = case fromMisoStringEither "12.5" of
  Right x -> x
  Left _ -> 0
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /registerInstance/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?from-miso-string-double`);
    assert.equal(main(), 99);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('executes the boot map interface through the generic JavaScript FFI boundary', async () => {
  const directory = await project('module Main where\nimport Data.Map\nmain = null (fromList [])\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?boot-map`);
    assert.equal(main(), true);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('instantiates a polymorphic boot foreign primitive independently at each call site', async () => {
  const directory = await project('module Main where\nimport qualified GHCJS.Marshal as Marshal\nfirst = Marshal.toJSVal True\nsecond = Marshal.toJSVal 2\nmain = 42\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?polymorphic-foreign`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('the unchanged counter reaches typechecking through real reachable Miso sources', async () => {
  const directory = join(process.cwd(), 'test/fixtures/miso-counter');
  const result = await compileProject({ project: directory, emit: false });
  const misoOrigins = Object.entries(result.moduleOrigins ?? {}).filter(([name]) => name === 'Miso' || name.startsWith('Miso.'));
  assert.ok(misoOrigins.length > 0);
  assert.ok(misoOrigins.every(([, file]) => file.includes('/references/miso/')));
  assert.ok(misoOrigins.every(([, file]) => !file.startsWith('<ghcts:boot/')));
  assert.equal(result.diagnostics.filter(diagnostic => diagnostic.code === 'E_PARSE').length, 0);
  assert.equal(result.diagnostics.filter(diagnostic => diagnostic.code === 'E_IMPORT').length, 0);
  assert.deepEqual(result.diagnostics, []);
});

test('ToJSVal record-wildcard instances bind fields instead of taking a fake extra argument', async () => {
  const directory = await project(`module Main where
class ToJSVal a where
  toJSVal :: a -> Int
data Rec = Rec { recN :: Int, recM :: Int }
instance ToJSVal Rec where
  toJSVal Rec {..} = recN + recM
main = toJSVal (Rec 40 2)
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /registerInstance\("ToJSVal","Rec"/);
    assert.match(generated, /fromJSValAs\("Rec"/);
    assert.match(generated, /field\([^,]+,"recN"\)/);
    assert.doesNotMatch(generated, /__dict_ToJSVal_Rec_\d+_0_toJSVal = lazy\(\(\) => \(arg0: any\) => \(arg1: any\) =>/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?tojsval-record`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('ToJSVal instance dispatch does not use Array.prototype.at', async () => {
  const runtime = await readFile(join(process.cwd(), 'dist/runtime.js'), 'utf8');
  assert.doesNotMatch(runtime, /\.at\(/);
  const directory = await project('module Main where\nimport GHCJS.Marshal (toJSVal)\ndata Kind = Alpha | Beta | Gamma\ninstance ToJSVal Kind\nmain = toJSVal Beta\n');
  const arrayAt = Array.prototype.at;
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    delete Array.prototype.at;
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?tojsval-no-at`);
    assert.equal(main(), 1);
  } finally {
    Array.prototype.at = arrayAt;
    await rm(directory, { recursive: true, force: true });
  }
});

test('marshals nullary ToJSVal constructors as their declaration-order indexes', async () => {
  const directory = await project('module Main where\nimport GHCJS.Marshal (toJSVal)\ndata Kind = Alpha | Beta | Gamma\ninstance ToJSVal Kind\nmain = toJSVal Beta\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /registerEnum\("Alpha",0/);
    assert.match(generated, /registerEnum\("Beta",1/);
    assert.match(generated, /registerEnum\("Gamma",2/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?tojsval-enum`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('the generated real Miso browser bootstrap starts without a runtime exception', async () => {
  const directory = join(process.cwd(), 'test/fixtures/miso-counter');
  const result = await compileProject({ project: directory });
  assert.deepEqual(result.diagnostics, []);
  const bootstrap = join(directory, 'dist/browser/bootstrap.js');
  const script = `import(${JSON.stringify(bootstrap)}).then(() => {
  const error = globalThis.document?.getElementById?.('ghcts-startup-error')?.textContent;
  if (error) throw new Error(error);
  const text = String(globalThis.document?.body?.textContent ?? '');
  if (!text.includes('+') || !text.includes('-') || !text.includes('0'))
    throw new Error('counter did not render, body=' + JSON.stringify(text));
  process.stdout.write('started');
})`;
  const output = execFileSync(process.execPath, ['-e', script], { encoding: 'utf8' });
  assert.equal(output, 'started');
  const index = await readFile(join(directory, 'dist/browser/index.html'), 'utf8');
  assert.doesNotMatch(index, /(?:src|href)=["'][^"']*miso\.js["']/);
  const linked = await readFile(join(directory, 'dist/browser/main.js'), 'utf8');
  assert.match(linked, /function onMTS/);
});

test('the generated real Miso counter updates when plus and minus are clicked', async () => {
  const directory = join(process.cwd(), 'test/fixtures/miso-counter');
  const result = await compileProject({ project: directory });
  assert.deepEqual(result.diagnostics, []);
  const bootstrap = join(directory, 'dist/browser/bootstrap.js');
  const script = `import(${JSON.stringify(bootstrap)}).then(async () => {
  const error = globalThis.document?.getElementById?.('ghcts-startup-error')?.textContent;
  if (error) throw new Error(error);
  const buttons = [];
  const visit = node => {
    if (node?.tagName === 'BUTTON') buttons.push(node);
    for (const child of node?.childNodes ?? []) visit(child);
  };
  visit(globalThis.document.body);
  const plus = buttons.find(button => String(button.textContent ?? '').includes('+'));
  const minus = buttons.find(button => String(button.textContent ?? '').includes('-'));
  if (!plus || !minus) throw new Error('missing buttons, body=' + JSON.stringify(globalThis.document.body.textContent));
  plus.click();
  await new Promise(resolve => setTimeout(resolve, 50));
  const afterPlus = String(globalThis.document.body.textContent ?? '');
  if (!afterPlus.includes('1')) throw new Error('plus did not increment, body=' + JSON.stringify(afterPlus));
  minus.click();
  await new Promise(resolve => setTimeout(resolve, 50));
  const afterMinus = String(globalThis.document.body.textContent ?? '');
  if (!afterMinus.includes('0') || afterMinus.includes('1'))
    throw new Error('minus did not decrement, body=' + JSON.stringify(afterMinus));
  process.stdout.write('clicked');
})`;
  const output = execFileSync(process.execPath, ['-e', script], { encoding: 'utf8' });
  assert.equal(output, 'clicked');
});

test('applies extra CPP symbols from ghcts.json', async () => {
  const directory = await project('module Main where\n#ifdef NATIVE\nmain = 1\n#else\nmain = 2\n#endif\n');
  try {
    await writeFile(join(directory, 'ghcts.json'), JSON.stringify({
      version: 1, sourceRoots: ['.'], entry: { module: 'Main', export: 'main' },
      targets: ['node'], outDir: 'dist', cpp: ['NATIVE'],
    }));
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?cpp-native`);
    assert.equal(main(), 1);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('unqualified fmap is Prelude fmap unless the module defines fmap', async () => {
  const directory = await project('module Main where\nmain = case fmap succ (Just 41) of\n  Just n -> n\n  Nothing -> 0\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /prelude\.fmap/);
    assert.doesNotMatch(generated, /v_Main_2e_fmap/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?prelude-fmap`);
    assert.equal(main(), 42);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('module bindings win over short builtin names', async () => {
  const directory = await project('module Main where\nweb = 7\nmain = web\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?web-binding`);
    assert.equal(main(), 7);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('static pointers dereference and expose a stable key', () => {
  const boxed = force(apply(prelude.staticPtr, lazy(() => 42)));
  assert.equal(boxed.tag, 'StaticPtr');
  assert.equal(force(apply(prelude.deRefStaticPtr, lazy(() => boxed))), 42);
  const key = force(apply(prelude.staticKey, lazy(() => boxed)));
  assert.equal(key.tag, 'Fingerprint');
  assert.match(String(force(key.fields[0])), /^[0-9a-f]{32}$/);
});

test('Fingerprint crosses the JS boundary as the GHCJS hex string', () => {
  const fingerprint = { tag: 'Fingerprint', fields: [lazy(() => '0123456789abcdef0123456789abcdef')] };
  assert.equal(force(apply(prelude.toJSVal, lazy(() => fingerprint))), '0123456789abcdef0123456789abcdef');
});

test('Maybe ToJSVal unwraps Just and maps Nothing to JavaScript null', () => {
  assert.equal(force(apply(prelude.toJSVal, lazy(() => prelude.nothing))), null);
  assert.equal(force(apply(prelude.toJSVal, lazy(() => apply(prelude.just, lazy(() => 'x'))))), 'x');
});

test('compiler emits GHCJS-shaped keys for source static sites', async () => {
  const directory = await project('module Main where\nmain = static 1\n');
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /staticPtrStable,lazy\(\(function\(\) \{return "[0-9a-f]{32}";\n\}\)\)/);
    assert.match(generated, /h\$hs_spt_insert\(\d+,\d+,\d+,\d+,lazy\(\(function\(\)/);
    assert.doesNotMatch(generated, /ghcts-static:/);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('compiles nested case in a record update and case pattern guards', async () => {
  const directory = await project(`module Main where
data R = R { picked :: Maybe Int }
onEnter m = m { picked = case picked m of
  Nothing -> Just 1
  p -> p }
pick x = case x of
  Just pv | Just n <- Just pv -> n
  _ -> 0
main = pick (Just 3)
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?case-pattern-guard`);
    assert.equal(main(), 3);
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('deriving ToJSON encodes nullary constructors as strings', async () => {
  const directory = await project(`module Main where
data Action = AddOne | SubtractOne deriving (ToJSON, FromJSON)
main = AddOne
`);
  try {
    const result = await compileProject({ project: directory });
    assert.deepEqual(result.diagnostics, []);
    const generated = await readFile(join(directory, 'dist/node/main.ts'), 'utf8');
    assert.match(generated, /registerDerivedJSON/);
    const { main } = await import(`${join(directory, 'dist/node/main.js')}?derived-json`);
    const runtime = await import(join(directory, 'dist/node/runtime.js'));
    const encoded = runtime.force(runtime.apply(runtime.prelude.toJSON, runtime.lazy(() => main())));
    assert.equal(encoded.tag, 'String');
    assert.equal(runtime.force(encoded.fields[0]), 'AddOne');
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('fmap over a JS string treats it as a MisoString scalar, not a [Char]', () => {
  // Miso's `instance FromJSVal COMPONENT` runs `fmap fromMisoString <$> msk`
  // over a hex StaticKey that arrives as a plain JS string. Splitting it into
  // characters produced a 32-element list, so `case ... of Nothing/Just` saw a
  // cons cell and raised "Non-exhaustive patterns in case: :" on device.
  // GHC resolves Functor from the type; a JS string here is a MisoString.
  const upper = (value) => String(force(value)).toUpperCase();
  const result = force(prelude.fmap(lazy(() => upper))(lazy(() => 'bbed18e3')));
  assert.equal(result, 'BBED18E3');
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
