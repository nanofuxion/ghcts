#!/usr/bin/env node
/**
 * Compile real Haskell source all the way to JavaScript and run it.
 *
 * parse -> elaborate -> desugar -> Core -> STG -> stgToJS -> renderRts, then
 * evaluate under the same trampoline `scripts/stg-run.mjs` uses. That script
 * proves codegen against hand-built STG; this one proves the frontend that
 * now produces that STG.
 *
 *   node scripts/hs-run.mjs                 # run the built-in programs
 *   node scripts/hs-run.mjs --print         # also show the generated JS
 *   node scripts/hs-run.mjs file.hs         # compile and run one file
 *
 * The language is Haskell with typeclasses: `src/elaborate.ts` prepends the
 * minimal Prelude of `src/prelude.ts` and turns classes, instances and
 * constrained call sites into explicit dictionary passing before desugaring.
 * `main` is entered as a thunk and whatever lands in R1 is reported. `Int`,
 * `Char` and `Bool` land unboxed, exactly as GHC's JS backend represents a
 * one-constructor type over a primitive field; a `[Char]` is walked into a JS
 * string, which is the one thing `putStrLn` would otherwise be for.
 */
import { readFileSync, statSync } from "node:fs";
import { resolve } from "node:path";
import { walk } from "../dist/compiler.js";
import { renderRts } from "../dist/stg-js/rts.js";
import { renderStaticRts } from "../dist/stg-js/rts-static.js";
import { stgToJS, renderModule } from "../dist/stg-js/codegen.js";
import { defaultStgToJSConfig } from "../dist/stg-js/types.js";
import { parseModule } from "../dist/parser.js";
import { elaborateProgram, USER_MAIN } from "../dist/elaborate.js";
import { desugarModule } from "../dist/desugar.js";
import { coreToStg } from "../dist/core-to-stg.js";
import { formatDiagnostic } from "../dist/diagnostics.js";

const show = process.argv.includes("--print");
const forceThreaded = process.argv.includes("--threaded");
const config = defaultStgToJSConfig;
const rts = renderRts(config) + "\n" + renderStaticRts(config);

/** Test-only scaffolding: a stack, a trampoline and a stop frame that
 * captures R1 so a program's value can be read back. GHC's own h$main
 * supplies the equivalent. Everything else comes from the real RTS. */
const bootstrap = `
h$stack = new Array(10000);
h$sp = 0;
function h$rs() { return h$stack[h$sp]; }
var h$testResult;
function h$stopFrame() { h$testResult = h$r1; return null; }
h$stopFrame.f = h$stopFrame;
h$o(h$stopFrame, -1, 0, 0, 0, null);
/** Enter a closure and return its value. Entering an already-evaluated
 * constructor returns it unchanged, so this works for a thunk and for a value.
 */
function h$forceClosure(c) {
  return h$runEntry(function(){ h$r1 = c; return c.f; });
}
function h$runEntry(c) {
  h$sp = 0;
  h$stack[0] = h$stopFrame;
  h$testResult = undefined;
  while (c !== null) c = c();
  return h$testResult;
}
/** The runMainIO wrapper leaves a closure of GHC's own shape behind: entering
 * it yields the IO action, which h$main then applies to one void argument with
 * h$ap_1_0. These two frames are that, exactly as h$main and h$forkThread
 * stack it - h$return loads the closure into R1 and hands control to h$ap_1_0.
 * A program with no IO main has no wrapper and is entered directly. */
function h$runWrapped(c) {
  h$sp = 3;
  h$stack[0] = h$stopFrame;
  h$stack[1] = h$ap_1_0;
  h$stack[2] = c;
  h$stack[3] = h$return;
  h$testResult = undefined;
  for (var f = h$stack[h$sp]; f !== null; ) f = f();
  // IOResult is an unboxed tuple, and matching one binds the result slot
  // without entering it, so an action's result arrives as a thunk. GHC drops
  // it - main is IO () - but a test wants to read it, so force it here.
  var r = h$testResult;
  return r !== null && typeof r === "object" ? h$forceClosure(r) : r;
}
/** A program that forks, blocks or delays needs the RTS's own scheduler, not
 * the bare trampoline above: only a real h$Thread can be put on an MVar's
 * wait queue and woken again. h$forkThread + h$mainLoop is exactly what
 * h$main does, minus base's top handler and stdout flush - neither of which
 * exists here. The thread constructor names ghc-internal's reportError
 * closure; src/build.ts emits that seat, but this harness links one module
 * rather than a bundle, so it is stubbed. */
var h$ghczminternalZCGHCziInternalziConcziSynczireportError = null;
function h$runThreaded(c) {
  var t = new h$Thread();
  t.stack[4] = h$ap_1_0;
  t.stack[5] = c;
  t.stack[6] = h$return;
  t.sp = 6;
  h$wakeupThread(t);
  h$mainLoop();
  // The scheduler re-arms itself on a timer forever; without this the process
  // never exits once every thread has finished.
  h$clearScheduleMainLoop();
}
`;

/** parse -> ... -> JS. Returns the emitted module and `main`'s symbol.
 *
 * `sources` is a list of `{ file, source }`; the module named `Main` is the
 * root, and the rest are reachable only through its imports, exactly as
 * `src/modules.ts` resolves them. */
function compile(sources, file) {
  const modules = new Map();
  for (const unit of sources) {
    const parsed = parseModule(unit.source, unit.file);
    if (parsed.diagnostics.some((d) => d.severity === "error")) {
      throw new Error(parsed.diagnostics.map(formatDiagnostic).join("\n"));
    }
    modules.set(parsed.module.ast.name, parsed.module.ast);
  }
  if (!modules.has("Main")) throw new Error(`${file}: no \`Main\` module`);
  const elaborated = elaborateProgram(modules, "Main", file);
  if (elaborated.diagnostics.some((d) => d.severity === "error")) {
    throw new Error(elaborated.diagnostics.map(formatDiagnostic).join("\n"));
  }
  const desugared = desugarModule(elaborated.module, file);
  const stg = coreToStg(desugared.program);
  const units = stgToJS(config, { unitId: "main", moduleName: "Main" }, stg.bindings);
  const emitted = renderModule(config, units);
  const mainBinder = stg.bindings
    .flatMap((b) => (b.tag === "StgNonRec" ? [b.binder] : b.pairs.map(([x]) => x)))
    .find((b) => b.name === "main");
  if (!mainBinder) throw new Error(`${file}: no \`main\``);
  const unit = units.find((u) => u.luIdExports.some((b) => b === mainBinder));
  return {
    emitted,
    symbol: unit.luObjBlock.oiSymbols[0],
    // An IO main is wrapped, and the wrapper is applied rather than entered.
    wrapped: stg.bindings.some((b) => b.tag === "StgNonRec" && b.binder.name === USER_MAIN),
    diagnostics: [...elaborated.diagnostics, ...desugared.diagnostics],
  };
}

/** Native `BigInt` syntax in the emitted module.
 *
 * The target engine is PrimJS, which has no BigInt at all: it refuses to
 * decode a packed bundle that contains a `32n` literal ("RangeError: BigInt is
 * too large to allocate"), and miso's own JS installs JSBI as
 * `globalThis.BigInt`, whose objects throw the moment they meet one. GHC emits
 * no BigInt either - `Integer` is ghc-bignum over 32-bit limbs.
 *
 * This is checked on every program because it is invisible in an answer: a
 * `BigInt` carrier gives the RIGHT answer under node and cannot be loaded at
 * all on the device, which is how it got in the first time. Only the emitted
 * module is scanned; the RTS is GHC's own `rts/js/arith.js`, byte for byte,
 * and its 64-bit quot/rem helpers are BigInt in GHC's linked output too. */
const nativeBigInt = (js) => js.match(/\bBigInt\b|(?<![\w$.])\d[\d_]*n\b/);

/** `probe` is a JS expression read *after* the program has run, which is the
 * only way to observe an `IO ()`: its value carries nothing, so the proof that
 * it ran has to come from the effect it had. Property order in the object
 * literal is what sequences the two. */
function run(emitted, symbol, probe, threaded, wrapped) {
  const enter = threaded
    ? `h$runThreaded(${symbol})`
    : wrapped
      ? `h$runWrapped(${symbol})`
      : `h$runEntry(function(){ h$r1 = ${symbol}; return h$r1.f; })`;
  // Indirect eval so the RTS's top-level `var h$...` land on globalThis.
  const entry = (0, eval)(
    `${rts}\n${bootstrap}\n${emitted}\n(function(){ h$initStatic.forEach(function(f){f();}); h$initStatic.length = 0;` +
      ` return { value: ${enter}, probed: ${probe ?? "undefined"},` +
      ` force: h$forceClosure }; })`,
  );
  const { value, probed, force } = entry();
  if (probe !== undefined) return probed;
  // `Int`, `Char` and `Bool` arrive as plain JS values: the backend unboxes a
  // one-constructor, one-primitive-field type (`isUnboxableCon`), and `Bool`
  // is a JS boolean. Only a list is still a closure, so an object result is a
  // `[Char]` to spell out; `[]` is allocated with null fields.
  if (value === null || typeof value !== "object") return value;
  let text = "";
  for (let cell = value; cell.d2 !== null && cell.d2 !== undefined; cell = force(cell.d2)) {
    const head = cell.d1;
    text += String.fromCharCode(typeof head === "number" ? head : force(head));
  }
  return text;
}

const programs = [
  { name: "arithmetic", source: "module Main where\nmain = 2 + 3\n", expect: 5 },
  {
    name: "nested arithmetic",
    source: "module Main where\nmain = 2 + 3 * 4 - 1\n",
    expect: 13,
  },
  {
    name: "top-level function",
    source: "module Main where\ndouble x = x + x\nmain = double 21\n",
    expect: 42,
  },
  {
    name: "let and where",
    source: "module Main where\nmain = a * seven\n  where\n    a = 6\n    seven = 3 + 4\n",
    expect: 42,
  },
  {
    name: "if / comparison",
    source: "module Main where\nmain = if 3 < 4 then 10 else 20\n",
    expect: 10,
  },
  {
    name: "guards",
    source: "module Main where\nclassify n\n  | n < 0 = 0\n  | n == 0 = 1\n  | otherwise = 2\nmain = classify 7\n",
    expect: 2,
  },
  {
    name: "literal pattern equations",
    source: "module Main where\nf 0 = 100\nf 1 = 200\nf n = n\nmain = f 1\n",
    expect: 200,
  },
  {
    name: "recursion",
    source: "module Main where\nfact n = if n == 0 then 1 else n * fact (n - 1)\nmain = fact 5\n",
    expect: 120,
  },
  {
    name: "data type and case",
    source:
      "module Main where\ndata Shape = Circle Int | Square Int\narea s = case s of\n  Circle r -> 3 * r * r\n  Square w -> w * w\nmain = area (Square 6)\n",
    expect: 36,
  },
  {
    name: "constructor patterns in equations",
    source:
      "module Main where\ndata Pair = Pair Int Int\nfst2 (Pair a b) = a + b\nmain = fst2 (Pair 20 22)\n",
    expect: 42,
  },
  {
    // GHC 9.12 requires the import string to be a JS expression denoting a
    // function, not a GHCJS `$r = ...` pattern.
    name: "foreign import javascript",
    // The JS FFI is unlifted: it takes machine values, so its signature is
    // written over `IntPrim` rather than the boxed `Int`.
    source:
      'module Main where\nforeign import javascript unsafe "((x,y) => x + y)" jsAdd :: IntPrim -> IntPrim -> IntPrim\nmain = jsAdd 19 23\n',
    expect: 42,
  },
  {
    name: "lambda",
    source: "module Main where\napply f x = f x\nmain = apply (\\y -> y * 3) 14\n",
    expect: 42,
  },
  // Everything below needs dictionaries: without instance selection there is
  // no `show`, no user-defined `==`, no default method and no superclass.
  {
    name: "show through the Num and Show dictionaries",
    source: "module Main where\nmain = show (1 + 2)\n",
    expect: "3",
  },
  {
    name: "show a negative Int",
    source: "module Main where\nmain = show (negate 407)\n",
    expect: "-407",
  },
  {
    name: "user-defined Eq instance",
    source:
      "module Main where\ndata Colour = Red | Green\neqColour a b = case a of\n  Red -> isRed b\n  Green -> not (isRed b)\nisRed c = case c of\n  Red -> True\n  Green -> False\ninstance Eq Colour where\n  (==) a b = eqColour a b\nmain = show (Red == Green)\n",
    expect: "False",
  },
  {
    name: "class default method (/= comes from Eq)",
    source:
      "module Main where\ndata Colour = Red | Green\nisRed c = case c of\n  Red -> True\n  Green -> False\ninstance Eq Colour where\n  (==) a b = eqBool (isRed a) (isRed b)\nmain = show (Red /= Green)\n",
    expect: "True",
  },
  {
    name: "superclass: Eq reached through an Ord dictionary",
    source:
      "module Main where\neqViaOrd :: Ord a => a -> a -> Bool\neqViaOrd x y = x == y\nmain = show (eqViaOrd 3 3)\n",
    expect: "True",
  },
  {
    name: "user class with a default method calling another method",
    source:
      "module Main where\ndata Colour = Red | Green\nclass Describe a where\n  label :: a -> [Char]\n  describe :: a -> [Char]\n  describe x = label x\ninstance Describe Colour where\n  label c = colourName c\ncolourName c = case c of\n  Red -> \"red\"\n  Green -> \"green\"\nmain = describe Green\n",
    expect: "green",
  },
  {
    name: "dictionary passed into a polymorphic function",
    source:
      "module Main where\ntriple x = x + x + x\nmain = show (triple 14)\n",
    expect: "42",
  },
  // Instance contexts: `Eq a => Eq [a]` / `Eq a => Eq (Maybe a)` make an
  // instance a function from dictionaries to a dictionary.
  {
    name: "instance context: Eq on a list",
    source: "module Main where\nmain = show ([1, 2, 3] == [1, 2, 3])\n",
    expect: "True",
  },
  {
    name: "instance context: a difference is found",
    source: "module Main where\nmain = show ([1, 2] == [1, 3])\n",
    expect: "False",
  },
  {
    name: "instance context: nested, Eq [[Int]]",
    source: "module Main where\nmain = show ([[1], [2]] == [[1], [2]])\n",
    expect: "True",
  },
  {
    name: "instance context: Eq (Maybe Int)",
    source: "module Main where\nmain = show (Just 3 == Just 4)\n",
    expect: "False",
  },
  {
    name: "user instance with a context",
    source:
      "module Main where\ndata Box a = Box a\nunbox (Box x) = x\ninstance Eq a => Eq (Box a) where\n  (==) p q = unbox p == unbox q\nmain = show (Box 7 == Box 7)\n",
    expect: "True",
  },
  // Functor / Applicative / Monad and `do`.
  {
    name: "fmap through the Functor dictionary",
    source: "module Main where\nmain = show (fmap (\\x -> x + 1) (Just 41) == Just 42)\n",
    expect: "True",
  },
  {
    name: "Applicative: pure and <*>",
    source: "module Main where\nmain = show (fmap (\\x -> x + 1) (pure 41) == Just 42)\n",
    expect: "True",
  },
  {
    name: "do notation over Maybe",
    source:
      "module Main where\nsum3 :: Maybe Int\nsum3 = do\n  x <- Just 1\n  y <- Just 2\n  z <- Just 39\n  pure (x + y + z)\nmain = show (sum3 == Just 42)\n",
    expect: "True",
  },
  {
    name: "do notation short-circuits on Nothing",
    source:
      "module Main where\nfailing :: Maybe Int\nfailing = do\n  x <- Just 1\n  y <- Nothing\n  pure (x + y)\nmain = show (failing == Nothing)\n",
    expect: "True",
  },
  {
    name: "do notation with >> and a let statement",
    source:
      "module Main where\nrun :: Maybe Int\nrun = do\n  Just 1\n  let k = 20\n  x <- Just 22\n  pure (k + x)\nmain = show (run == Just 42)\n",
    expect: "True",
  },
  {
    name: "do notation with a constructor binder",
    source:
      "module Main where\nunwrap :: Maybe Int\nunwrap = do\n  I n <- Just 42\n  pure (I n)\nmain = show (unwrap == Just 42)\n",
    expect: "True",
  },
  // Records.
  {
    name: "record construction and a field selector",
    source:
      "module Main where\ndata Person = Person { name :: [Char], age :: Int }\nmain = show (age (Person { name = \"ada\", age = 42 }))\n",
    expect: "42",
  },
  {
    name: "record update",
    source:
      "module Main where\ndata Person = Person { name :: [Char], age :: Int }\nolder p = p { age = age p + 1 }\nmain = show (age (older (Person { name = \"ada\", age = 41 })))\n",
    expect: "42",
  },
  {
    name: "record selector on a newtype, and a record pattern",
    source:
      "module Main where\nnewtype Model = Model { value :: Int }\nbump (Model { value = v }) = Model { value = v + 1 }\nmain = show (value (bump (Model 41)))\n",
    expect: "42",
  },
  {
    name: "record wildcard pattern",
    source:
      "module Main where\ndata Point = Point { px :: Int, py :: Int }\nsumP (Point {..}) = px + py\nmain = show (sumP (Point 20 22))\n",
    expect: "42",
  },
  // deriving.
  {
    name: "deriving Eq on an enumeration",
    source:
      "module Main where\ndata Colour = Red | Green | Blue deriving Eq\nmain = show (Green == Green)\n",
    expect: "True",
  },
  {
    name: "deriving Eq distinguishes constructors",
    source:
      "module Main where\ndata Colour = Red | Green | Blue deriving Eq\nmain = show (Green == Blue)\n",
    expect: "False",
  },
  {
    name: "deriving Eq with fields and a context",
    source:
      "module Main where\ndata Pair a = Pair a a deriving Eq\nmain = show (Pair 1 2 == Pair 1 3)\n",
    expect: "False",
  },
  {
    name: "deriving Eq reaches through the derived list instance",
    source:
      "module Main where\ndata Colour = Red | Green deriving Eq\nmain = show ([Red, Green] == [Red, Green])\n",
    expect: "True",
  },
  {
    name: "record type deriving Eq",
    source:
      "module Main where\ndata Point = Point { px :: Int, py :: Int } deriving Eq\nmain = show (Point 1 2 == Point 1 2)\n",
    expect: "True",
  },
  {
    name: "multi-equation instance method",
    source:
      "module Main where\ndata Colour = Red | Green\ninstance Show Colour where\n  show Red = \"red\"\n  show Green = \"green\"\nmain = show Green\n",
    expect: "green",
  },
  {
    name: "Prelude operators: $, &&, ++ and Eq Char",
    source: 'module Main where\nmain = show $ "ab" ++ "c" == "abc" && not False\n',
    expect: "True",
  },
  {
    // `Bool` is an unboxable type, so a nullary `False` passed as an argument
    // must reach the callee as the static value, not a fresh (truthy) closure.
    name: "a Bool constructor passed as an argument",
    source: "module Main where\nf x = if x then 1 else 2\nmain = f False\n",
    expect: 2,
  },
  {
    // 1. a plain import: a name defined elsewhere, brought in bare.
    name: "modules: plain import",
    sources: {
      Arith: "module Arith where\ntriple :: Int -> Int\ntriple x = x + x + x\n",
      Main: "module Main where\nimport Arith\nmain = triple 14\n",
    },
    expect: 42,
  },
  {
    // 2. `qualified ... as`: the bare name must NOT be in scope, only `A.`.
    name: "modules: qualified as",
    sources: {
      Arith: "module Arith where\ntriple :: Int -> Int\ntriple x = x + x + x\n",
      Main: "module Main where\nimport qualified Arith as A\nmain = A.triple 5\n",
    },
    expect: 15,
  },
  {
    // 3. an explicit import list lets `keep` through and leaves `drop` out.
    name: "modules: explicit import list",
    sources: {
      Pair: "module Pair where\nkeep :: Int -> Int\nkeep x = x + 1\ndrop2 :: Int -> Int\ndrop2 x = x - 1\n",
      Main: "module Main where\nimport Pair (keep)\nmain = keep 9\n",
    },
    expect: 10,
  },
  {
    // 4. `hiding`: the module's other name is still bare-visible.
    name: "modules: hiding",
    sources: {
      Pair: "module Pair where\nkeep :: Int -> Int\nkeep x = x + 1\ndrop2 :: Int -> Int\ndrop2 x = x - 1\n",
      Main: "module Main where\nimport Pair hiding (drop2)\nmain = keep 9\n",
    },
    expect: 10,
  },
  {
    // 5. two levels: Main sees `base` only because Mid re-exports it.
    name: "modules: two levels of import",
    sources: {
      Base: "module Base where\nbase :: Int\nbase = 6\n",
      Mid: "module Mid (base, scale) where\nimport Base\nscale :: Int -> Int\nscale x = x * base\n",
      Main: "module Main where\nimport Mid\nmain = scale base\n",
    },
    expect: 36,
  },
  {
    // 6. instances are global: `Show Colour` is used here although nothing
    // from `Paint` was imported by name.
    name: "modules: instance from a module whose names are not imported",
    sources: {
      Paint:
        "module Paint (Colour(..)) where\ndata Colour = Red | Green\ninstance Show Colour where\n  show Red = \"red\"\n  show Green = \"green\"\nsecret :: Int\nsecret = 1\n",
      Main: "module Main where\nimport Paint (Colour(..))\nmain = show Green\n",
    },
    expect: "green",
  },
  {
    // A local binder must beat the imported name of the same spelling.
    name: "modules: local shadows an import",
    sources: {
      Arith: "module Arith where\ntriple :: Int -> Int\ntriple x = x + x + x\n",
      Main: "module Main where\nimport Arith\nmain = let triple y = y in triple 7\n",
    },
    expect: 7,
  },
  {
    // Same top-level name in two modules: renaming keeps them apart.
    name: "modules: same name in two modules",
    sources: {
      One: "module One where\nvalue :: Int\nvalue = 10\n",
      Two: "module Two where\nvalue :: Int\nvalue = 20\n",
      Main:
        "module Main where\nimport qualified One as O\nimport qualified Two as T\nmain = O.value + T.value\n",
    },
    expect: 30,
  },
  // `error` and the laziness that makes it usable as a fallback.
  {
    name: "error is not forced when its branch is not taken",
    source: 'module Main where\nmain = if True then 42 else error "boom"\n',
    expect: 42,
  },
  {
    name: "error raises",
    source: 'module Main where\nmain = error "boom"\n',
    throws: "Prelude.error",
  },
  {
    name: "head of an empty list raises through error",
    source: "module Main where\nmain = head []\n",
    throws: "Prelude.error",
  },
  // Either.
  {
    name: "Either: Left is taken",
    source:
      "module Main where\npick :: Either Int Int -> Int\npick e = either (\\x -> x) (\\y -> y + 1) e\nmain = pick (Left 42)\n",
    expect: 42,
  },
  {
    name: "Either: Right is taken",
    source:
      "module Main where\npick :: Either Int Int -> Int\npick e = either (\\x -> x) (\\y -> y + 1) e\nmain = pick (Right 41)\n",
    expect: 42,
  },
  {
    name: "Either as a Monad short-circuits on Left",
    source:
      'module Main where\nrun :: Either [Char] Int\nrun = do\n  x <- Right 1\n  y <- Left "no"\n  pure (x + y)\nmain = show (isLeft run)\n',
    expect: "True",
  },
  {
    name: "Either as a Monad threads a Right",
    source:
      'module Main where\nrun :: Either [Char] Int\nrun = do\n  x <- Right 20\n  y <- Right 22\n  pure (x + y)\nmain = show (run == Right 42)\n',
    expect: "True",
  },
  // Prelude breadth.
  {
    name: "list functions: map, filter, sum",
    source: "module Main where\nmain = sum (map (\\x -> x * 2) (filter (\\x -> x > 2) [1, 2, 3, 4]))\n",
    expect: 14,
  },
  {
    name: "Semigroup and Monoid on lists",
    source: 'module Main where\nmain = mconcat ["a", "b"] ++ ("c" <> "de")\n',
    expect: "abcde",
  },
  {
    name: "compare, Ordering and the Ord defaults",
    source: "module Main where\nmain = show (compare 3 4 == LT && max 3 4 == 4 && min 3 4 == 3)\n",
    expect: "True",
  },
  {
    name: "tuples: a tuple pattern, fst and snd",
    source: "module Main where\nswap2 p = (snd p, fst p)\nmain = fst (swap2 (20, 42))\n",
    expect: 42,
  },
  {
    name: "Eq on a pair",
    source: "module Main where\nmain = show ((1, 2) == (1, 2) && (1, 2) /= (1, 3))\n",
    expect: "True",
  },
  {
    name: "maybe, fromMaybe and <$>",
    source: "module Main where\nmain = fromMaybe 0 ((\\x -> x + 1) <$> Just 41)\n",
    expect: 42,
  },
  {
    name: "flip and a section-free operator argument",
    source: "module Main where\nmain = flip (-) 1 43\n",
    expect: 42,
  },
  {
    name: "mapM over a list in the Maybe monad",
    source:
      "module Main where\nmain = show (mapM (\\x -> if x > 0 then Just x else Nothing) [1, 2, 3] == Just [1, 2, 3])\n",
    expect: "True",
  },
  {
    name: "mapM short-circuits",
    source:
      "module Main where\nmain = show (mapM (\\x -> if x > 1 then Just x else Nothing) [1, 2] == Nothing)\n",
    expect: "True",
  },
  {
    name: "Foldable: length at Maybe, elem and any at a list",
    source:
      "module Main where\nmain = show (length (Just 1) == 1 && elem 3 [1, 2, 3] && any (\\x -> x > 2) [1, 2, 3])\n",
    expect: "True",
  },
  {
    name: "Alternative on Maybe, and guard",
    source: "module Main where\nmain = show ((Nothing <|> Just 42) == Just 42 && isNothing (guard False))\n",
    expect: "True",
  },
  // IO. `IO (\\s -> ...)` is how a primitive action is built: an action is a
  // function of the state token, so the FFI call inside the lambda runs when
  // the action runs, not when it is constructed. The `case` around the call is
  // GHC's own shape (`case emit n of v -> (# s, I v #)`) and is what makes the
  // effect happen at all: without it the result is a thunk nobody forces.
  {
    name: "IO: pure and fmap, entered through the runMainIO wrapper",
    source: "module Main where\nmain :: IO Int\nmain = fmap (\\x -> x + 1) (pure 41)\n",
    expect: 42,
  },
  {
    name: "IO: a do block binds and returns",
    source: "module Main where\nmain :: IO Int\nmain = do\n  x <- pure 20\n  y <- pure 22\n  pure (x + y)\n",
    expect: 42,
  },
  {
    name: "type synonyms, with and without parameters",
    source:
      "module Main where\ntype Count = Int\ntype Both a = (a, a)\ntotal :: Both Count -> Count\ntotal p = fst p + snd p\nmain = total (20, 22)\n",
    expect: 42,
  },
  {
    name: "a () pattern, in an equation and as a do binder",
    source:
      "module Main where\nf :: () -> Int\nf () = 42\ng :: IO Int\ng = do\n  () <- pure ()\n  pure (f ())\nmain = unsafePerformIO g\n",
    expect: 42,
  },
  {
    name: "unsafePerformIO runs an action",
    source: "module Main where\nmain = unsafePerformIO (pure 42)\n",
    expect: 42,
  },
  {
    name: "IO: a do block runs its effects, in order",
    source: [
      "module Main where",
      'foreign import javascript unsafe "((x) => { globalThis.$hsOrder = (globalThis.$hsOrder || 0) * 10 + x; return x; })" emit :: IntPrim -> IntPrim',
      'foreign import javascript unsafe "((x) => globalThis.$hsOrder)" readOrder :: IntPrim -> IntPrim',
      "stepAt :: RealWorld -> IntPrim -> IOResult Int",
      "stepAt s n = case emit n of",
      "  v -> IOResult s (I v)",
      "readAt :: RealWorld -> IOResult Int",
      "readAt s = case readOrder 0 of",
      "  v -> IOResult s (I v)",
      "step :: IntPrim -> IO Int",
      "step n = IO (\\s -> stepAt s n)",
      "readOrderIO :: IO Int",
      "readOrderIO = IO (\\s -> readAt s)",
      "main :: IO Int",
      "main = do",
      "  step 1",
      "  step 2",
      "  step 3",
      "  readOrderIO",
      "",
    ].join("\n"),
    expect: 123,
  },
  {
    name: "main :: IO () runs and has its effect",
    source: [
      "module Main where",
      'foreign import javascript unsafe "((x) => { globalThis.$hsProbe = x; return x; })" emit :: IntPrim -> IntPrim',
      "stepAt :: RealWorld -> IntPrim -> IOResult Int",
      "stepAt s n = case emit n of",
      "  v -> IOResult s (I v)",
      "step :: IntPrim -> IO Int",
      "step n = IO (\\s -> stepAt s n)",
      "main :: IO ()",
      "main = do",
      "  step 42",
      "  pure ()",
      "",
    ].join("\n"),
    probe: "globalThis.$hsProbe",
    expect: 42,
  },
  {
    // Every import above is written in the unlifted vocabulary the backend
    // speaks (`IntPrim -> IntPrim`) and wrapped into `IO` by hand. Real
    // libraries do not: miso writes `IO`-returning imports over the BOXED
    // `Int`/`JSVal`/`JSString`, and the desugarer has to marshal both ends
    // (GHC's `dsFCall`). An unwrapped `IO` result is not an `IO` action at
    // all, so `>>=` takes `.d1` of a plain JavaScript number - which is how
    // this fails without the wrapper.
    name: "foreign import returning IO: an action, run once per use",
    source: [
      "module Main where",
      'foreign import javascript unsafe "((n) => { globalThis.$hsFfiIO = (globalThis.$hsFfiIO || 0) * 10 + n; return globalThis.$hsFfiIO; })" bump :: Int -> IO Int',
      "main :: IO Int",
      "main = do",
      "  bump 1",
      "  bump 2",
      "  bump 3",
      "",
    ].join("\n"),
    expect: 123,
  },
  {
    // `JSVal` and `JSString` are one-field boxes the BACKEND does not unbox
    // (only Int/Char/Double are `isUnboxableCon`), so an unmarshalled import
    // hands JavaScript the heap object: `o[k]` with a closure for `k` is
    // `undefined`. The `case u of ()` pins the other half of `boxResult` - an
    // `IO ()` import must yield the unit, not whatever JavaScript returned.
    name: "foreign import over JSVal/JSString: both ends marshalled",
    source: [
      "module Main where",
      "import GHC.JS.Prim",
      "import qualified Data.JSString as J",
      'foreign import javascript unsafe "(() => ({}))" newObj :: IO JSVal',
      'foreign import javascript unsafe "((k,v,o) => { o[k] = v + 1; })" setProp :: J.JSString -> Int -> JSVal -> IO ()',
      'foreign import javascript unsafe "((k,o) => o[k])" getProp :: J.JSString -> JSVal -> IO Int',
      "main :: IO Int",
      "main = do",
      "  o <- newObj",
      '  u <- setProp (J.pack "n") 41 o',
      '  n <- getProp (J.pack "n") o',
      "  pure (case u of () -> n)",
      "",
    ].join("\n"),
    expect: 42,
  },
  // Library modules (src/library.ts). Each of these is here because a wrong
  // implementation would fail silently rather than fail to compile.
  {
    name: "IORef: write, modify and read back",
    source: [
      "module Main where",
      "import Data.IORef",
      "main :: IO Int",
      "main = do",
      "  r <- newIORef (10 :: Int)",
      "  writeIORef r 32",
      "  modifyIORef r (\\x -> x + 10)",
      "  v <- readIORef r",
      "  n <- atomicModifyIORef' r (\\x -> (x * 2, x + 1))",
      "  w <- readIORef r",
      "  pure (v + n + w)",
      "",
    ].join("\n"),
    expect: 169,
  },
  {
    // `newIORef` stores the closure it is given and `readIORef` hands it back
    // untouched, exactly as `newMutVar#`/`readMutVar#` do. If either forced,
    // this would raise instead of returning 42.
    name: "IORef holds an unforced thunk",
    source: [
      "module Main where",
      "import Data.IORef",
      "main :: IO Int",
      "main = do",
      '  r <- newIORef (error "IORef forced its contents")',
      "  writeIORef r (42 :: Int)",
      "  readIORef r",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    name: "MVar: put then take, and isEmptyMVar either side",
    source: [
      "module Main where",
      "import Control.Concurrent.MVar",
      "main :: IO Int",
      "main = do",
      "  v <- newEmptyMVar",
      "  before <- isEmptyMVar v",
      "  putMVar v (40 :: Int)",
      "  x <- takeMVar v",
      "  after <- isEmptyMVar v",
      "  pure (x + (if before then 1 else 0) + (if after then 1 else 0))",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // The point of the RTS primops. The forked thread reaches `takeMVar v`
    // while `v` is empty and must BLOCK - a non-blocking read would hand it a
    // hole and the recorded value would not be 42. The main thread then blocks
    // in turn on `done` until the child has finished, so both directions of
    // block-and-resume are exercised.
    name: "MVar: a take on an empty MVar blocks, and a put resumes it",
    threaded: true,
    source: [
      "module Main where",
      "import Control.Concurrent",
      'foreign import javascript unsafe "((x) => { globalThis.$hsMVar = x; return x; })" record :: IntPrim -> IntPrim',
      "recordStep :: RealWorld -> IntPrim -> IOResult Int",
      "recordStep s n = case record n of",
      "  v -> IOResult s (I v)",
      "say :: Int -> IO Int",
      "say (I n) = IO (\\s -> recordStep s n)",
      "child :: MVar Int -> MVar () -> IO ()",
      "child v done = do",
      "  x <- takeMVar v",
      "  say x",
      "  putMVar done ()",
      "main :: IO ()",
      "main = do",
      "  v <- newEmptyMVar",
      "  done <- newEmptyMVar",
      "  forkIO (child v done)",
      "  putMVar v (42 :: Int)",
      "  takeMVar done",
      "  pure ()",
      "",
    ].join("\n"),
    probe: "globalThis.$hsMVar",
    expect: 42,
  },
  {
    name: "Double: arithmetic and division",
    source: "module Main where\nmain :: Double\nmain = (1.5 + 2.25) * 2.0 / 3.0\n",
    expect: 2.5,
  },
  {
    // GHC's `round` is round-half-to-EVEN. 2.5 and 3.5 both round to an even
    // number, in opposite directions; half-up would give 3 and 4.
    name: "Double: round is half-to-even, and floor/ceiling/truncate",
    source: [
      "module Main where",
      "main :: Int",
      "main = round (2.5 :: Double) * 1000",
      "     + round (3.5 :: Double) * 100",
      "     + floor (0 - 1.5 :: Double) * 10",
      "     + ceiling (1.2 :: Double)",
      "",
    ].join("\n"),
    expect: 2000 + 400 - 20 + 2,
  },
  {
    name: "Double: realToFrac and fromIntegral cross Int and Double",
    source: [
      "module Main where",
      "main :: Double",
      "main = realToFrac (3 :: Int) + fromIntegral (4 :: Int) + realToFrac (0.5 :: Double)",
      "",
    ].join("\n"),
    expect: 7.5,
  },
  {
    // The ordering `Data.Map` guarantees is the reason it is a balanced search
    // tree rather than a JS `Map`: the keys go in scrambled and come back
    // ascending, and a delete and a re-insert do not disturb that.
    name: "Data.Map: toList is ascending by key, through insert and delete",
    source: [
      "module Main where",
      "import qualified Data.Map as M",
      "main :: [Char]",
      "main = show (M.toList (M.insert 1 10 (M.delete 3 (M.fromList [(3,30),(1,1),(2,20),(5,50),(4,40)])))",
      "          == [(1,10),(2,20),(4,40),(5,50)])",
      "",
    ].join("\n"),
    expect: "True",
  },
  {
    name: "Data.Map: lookup, size, elems, keys and findWithDefault",
    source: [
      "module Main where",
      "import qualified Data.Map as M",
      "main :: [Char]",
      "main = show (M.lookup 2 m == Just 20)",
      "    ++ show (M.lookup 9 m == Nothing)",
      "    ++ show (M.size m == 3)",
      "    ++ show (M.elems m == [1,20,30])",
      "    ++ show (M.keys m == [1,2,3])",
      "    ++ show (M.findWithDefault 0 9 m == 0)",
      "    ++ show (M.toDescList m == [(3,30),(2,20),(1,1)])",
      "m = M.fromList [(3,30),(1,1),(2,20)]",
      "",
    ].join("\n"),
    expect: "TrueTrueTrueTrueTrueTrueTrue",
  },
  {
    // A tree that is not rebalanced degenerates into a list on sorted input:
    // 64 ascending inserts would then be 64 deep. This bound passes for a
    // balanced tree and fails for a list.
    name: "Data.Map: sorted inserts stay balanced",
    source: [
      "module Main where",
      "import qualified Data.Map as M",
      "depth :: M.Map Int Int -> Int",
      "depth M.Tip = 0",
      "depth (M.Bin _ _ _ l r) = 1 + max (depth l) (depth r)",
      "main :: Int",
      "main = depth (M.fromList (map (\\k -> (k, k)) (enumTo 64)))",
      "enumTo :: Int -> [Int]",
      "enumTo n = if n <= 0 then [] else enumTo (n - 1) ++ [n]",
      "",
    ].join("\n"),
    // 64 keys in a perfectly balanced tree are 7 levels deep; an unbalanced
    // one would be 64.
    expect: 7,
  },
  {
    name: "Data.Set and Data.IntMap ride on the same tree",
    source: [
      "module Main where",
      "import qualified Data.Set as S",
      "import qualified Data.IntMap.Strict as IM",
      "main :: [Char]",
      "main = show (S.toList (S.insert 0 (S.fromList [3,1,2,1])) == [0,1,2,3])",
      "    ++ show (S.member 2 (S.fromList [1,2]))",
      "    ++ show (IM.lookup 2 (IM.fromList [(1,10),(2,20)]) == Just 20)",
      "    ++ show (IM.elems (IM.insertWith (+) 1 5 (IM.fromList [(1,10)])) == [15])",
      "",
    ].join("\n"),
    expect: "TrueTrueTrueTrue",
  },
  {
    // A MisoString is a JavaScript string: `==`, `<>` and `intercalate` are
    // the JavaScript operations, not a fold over [Char].
    name: "Data.JSString: pack/unpack round trip and the FFI-backed operations",
    source: [
      "module Main where",
      "import qualified Data.JSString as J",
      "main :: [Char]",
      'main = J.unpack (J.intercalate (J.pack ", ") [J.pack "ab", J.toUpper (J.pack "cd"), J.replicate 2 (J.pack "x")])',
      '    ++ show (J.pack "ab" == J.pack "ab")',
      '    ++ show (J.pack "ab" < J.pack "b")',
      '    ++ J.unpack (J.pack "hi" <> J.pack "!")',
      '    ++ concatMap J.unpack (J.splitOn (J.pack ",") (J.pack "a,b,c"))',
      '    ++ show (J.length (J.pack "abc") == 3)',
      "",
    ].join("\n"),
    expect: "ab, CD, xxTrueTruehi!abcTrue",
  },
  {
    // A Char is a code point, so an astral character must survive as ONE Char
    // even though JavaScript stores it as two UTF-16 code units.
    name: "Data.JSString: unpack yields code points, not UTF-16 units",
    source: [
      "module Main where",
      "import qualified Data.JSString as J",
      "main :: [Char]",
      'main = show (length (J.unpack (J.pack "a\\120163b")) == 3)',
      '    ++ show (J.unpack (J.pack (J.unpack (J.pack "a\\120163b"))) == "a\\120163b")',
      "",
    ].join("\n"),
    expect: "TrueTrue",
  },
  {
    name: "Data.Char classification and Data.List sort/foldl'",
    source: [
      "module Main where",
      "import qualified Data.Char as C",
      "import qualified Data.List as L",
      "main :: [Char]",
      "main = show (C.isUpper (chr 65) && C.isLower (chr 97) && C.isSpace (chr 32))",
      "    ++ show (C.toLower (chr 81) == chr 113 && C.digitToInt (chr 55) == 7)",
      "    ++ show (L.sort [3,1,2] == [1,2,3] && L.sortOn negate [1,3,2] == [3,2,1])",
      "    ++ show (L.foldl' (+) 0 [1,2,3] == 6 && L.nub [1,2,1] == [1,2])",
      "",
    ].join("\n"),
    expect: "TrueTrueTrueTrue",
  },
  {
    name: "list comprehensions, including a refutable generator",
    source: [
      "module Main where",
      "main :: [Char]",
      'main = [ c | (n, c) <- zip [1,2,3,4,5] "abcde", n > 2, Just d <- [Just c] ]',
      "",
    ].join("\n"),
    expect: "cde",
  },
  {
    // A callback is a JavaScript function that starts a Haskell thread. The
    // proof is that JavaScript calls it with a value and the Haskell action
    // runs with that value: `c(77)` in, 77 out.
    name: "asyncCallback1: JavaScript calls in and the Haskell action runs",
    threaded: true,
    source: [
      "module Main where",
      "import GHC.JS.Prim",
      "import GHC.JS.Foreign.Callback",
      'foreign import javascript unsafe "((x) => { globalThis.$hsCb = x; return 0; })" record :: JSValPrim -> IntPrim',
      'foreign import javascript unsafe "((c) => { c(77); return 0; })" invoke :: CallbackPrim -> IntPrim',
      "recordIO :: JSVal -> IO ()",
      "recordIO (JSVal x) = IO (\\s -> recordStep s x)",
      "recordStep :: RealWorld -> JSValPrim -> IOResult ()",
      "recordStep s x = case record x of",
      "  _ -> IOResult s ()",
      "fire :: Callback a -> IO ()",
      "fire (Callback c) = IO (\\s -> fireStep s c)",
      "fireStep :: RealWorld -> CallbackPrim -> IOResult ()",
      "fireStep s c = case invoke c of",
      "  _ -> IOResult s ()",
      "main :: IO ()",
      "main = do",
      "  cb <- asyncCallback1 recordIO",
      "  fire cb",
      "  pure ()",
      "",
    ].join("\n"),
    probe: "globalThis.$hsCb",
    expect: 77,
  },
  {
    // `Ord` is defined by mutual defaults - `compare` from `(<=)` and `(<=)`
    // from `compare` - so an instance that supplies neither loops forever
    // rather than failing to compile. These are the ones that supply one.
    name: "Ord on lists, strings and Maybe is lexicographic",
    source: [
      "module Main where",
      "main :: [Char]",
      'main = show (compare [1,2] [1,3] == LT && compare "ab" "a" == GT',
      '          && compare "a" "b" == LT && Just 1 < Just 2 && max "a" "b" == "b" && () == ())',
      "",
    ].join("\n"),
    expect: "True",
  },
  {
    // `seq` here is a `case` on an application, which is the only shape this
    // frontend evaluates. If it did not evaluate, this would return 1.
    name: "seq forces its first argument",
    source: 'module Main where\nmain :: Int\nmain = seq (error "forced") 1\n',
    throws: "Prelude.error",
  },
  {
    // An action built but never run must have no effect: that is the whole
    // point of representing `IO` as a function rather than as a value.
    name: "an unrun IO action has no effect",
    source: [
      "module Main where",
      'foreign import javascript unsafe "((x) => { globalThis.$hsUnrun = x; return x; })" emit :: IntPrim -> IntPrim',
      "stepAt :: RealWorld -> IntPrim -> IOResult Int",
      "stepAt s n = case emit n of",
      "  v -> IOResult s (I v)",
      "step :: IntPrim -> IO Int",
      "step n = IO (\\s -> stepAt s n)",
      "main :: IO Int",
      "main = pure (unused (step 7))",
      "unused :: IO Int -> Int",
      "unused m = 42",
      "",
    ].join("\n"),
    probe: "globalThis.$hsUnrun === undefined ? 0 : globalThis.$hsUnrun",
    expect: 0,
  },
  {
    // 5 -> modify (+1) -> 6 -> put (6*2). A `State` that did not thread would
    // return 5, 6 or 10 instead of 12.
    name: "Control.Monad.State: execState threads the state through a do block",
    source: [
      "module Main where",
      "import Control.Monad.State",
      "bump :: State Int ()",
      "bump = do",
      "  modify (\\n -> n + 1)",
      "  n <- get",
      "  put (n * 2)",
      "main :: Int",
      "main = execState bump 5",
      "",
    ].join("\n"),
    expect: 12,
  },
  {
    // `local` must apply only to the action it wraps: the outer `ask` still
    // sees 10, so 10 + (10*2 + 1) = 31. A `local` that leaked would give 42.
    name: "Control.Monad.Reader: ask reads the environment and local rescopes it",
    source: [
      "module Main where",
      "import Control.Monad.Reader",
      "prog :: Reader Int Int",
      "prog = do",
      "  n <- ask",
      "  m <- local (\\x -> x * 2) (asks (\\x -> x + 1))",
      "  pure (n + m)",
      "main :: Int",
      "main = runReader prog 10",
      "",
    ].join("\n"),
    expect: 31,
  },
  {
    // Accumulation *in order*: the digits come out "123", not "321", which is
    // what a `mappend` on the wrong side of `>>=` would produce.
    name: "Control.Monad.Writer: tell accumulates in the order the actions ran",
    source: [
      "module Main where",
      "import Control.Monad.Writer",
      "prog :: Writer [Char] Int",
      'prog = tell "1" >> tell "2" >> tell "3" >> pure 9',
      "main :: [Char]",
      "main = execWriter prog",
      "",
    ].join("\n"),
    expect: "123",
  },
  {
    // Reader, Writer and State at once, which is what miso's `Effect` is:
    // state 4 + env 3 = 7, then doubled to 14; the log is [3, 7], summing 10.
    name: "Control.Monad.RWS: execRWS returns the final state and the log",
    source: [
      "module Main where",
      "import Control.Monad.RWS",
      "prog :: RWS Int [Int] Int ()",
      "prog = do",
      "  r <- ask",
      "  tell [r]",
      "  modify (\\s -> s + r)",
      "  s <- get",
      "  tell [s]",
      "  put (s * 2)",
      "main :: [Char]",
      'main = show (fst (execRWS prog 3 4)) ++ "/" ++ show (total (snd (execRWS prog 3 4)))',
      "total :: [Int] -> Int",
      "total xs = case xs of",
      "  [] -> 0",
      "  (y : ys) -> y + total ys",
      "",
    ].join("\n"),
    expect: "14/10",
  },
  {
    // The short circuit, observed rather than typechecked: the second step
    // yields `Nothing`, so the third must never run. The counter says how many
    // steps executed - 2, not 3.
    name: "MaybeT: a Nothing stops the actions after it from running",
    source: [
      "module Main where",
      "import Control.Monad.Trans.Maybe",
      "import Data.IORef",
      "step :: IORef Int -> Int -> MaybeT IO Int",
      "step r n = MaybeT (modifyIORef r (\\x -> x + 1) >> pure (if n > 2 then Nothing else Just n))",
      "main :: IO Int",
      "main = do",
      "  r <- newIORef 0",
      "  out <- runMaybeT (step r 1 >>= (\\a -> step r 5 >>= (\\b -> step r 7 >>= (\\c -> pure (a + b + c)))))",
      "  hits <- readIORef r",
      "  pure (case out of",
      "          Nothing -> hits",
      "          Just v -> 100 + v)",
      "",
    ].join("\n"),
    expect: 2,
  },
  {
    // `<|>` takes the second branch only when the first produced `Nothing`,
    // and `fail` (which a failed pattern bind calls) is that same `Nothing`.
    name: "MaybeT: Alternative recovers and a failed pattern bind is Nothing",
    source: [
      "module Main where",
      "import Control.Monad.Trans.Maybe",
      "recovered :: MaybeT IO Int",
      "recovered = MaybeT (pure Nothing) <|> pure 7",
      "refused :: MaybeT IO Int",
      "refused = do",
      "  Just x <- pure (Nothing :: Maybe Int)",
      "  pure x",
      "main :: IO Int",
      "main = do",
      "  a <- runMaybeT recovered",
      "  b <- runMaybeT refused",
      "  pure (case a of",
      "          Nothing -> 0",
      "          Just v -> case b of",
      "            Nothing -> v",
      "            Just w -> v + w)",
      "",
    ].join("\n"),
    expect: 7,
  },
  {
    // `liftIO` must run the base action where the `do` block reaches it, so
    // the writes land in order: 1 then 2, leaving 12.
    name: "MonadIO: liftIO inside a ReaderT runs in the base monad's order",
    source: [
      "module Main where",
      "import Control.Monad.Reader",
      "import Data.IORef",
      "prog :: IORef Int -> ReaderT Int IO Int",
      "prog r = do",
      "  n <- ask",
      "  liftIO (modifyIORef r (\\x -> x * 10 + 1))",
      "  liftIO (modifyIORef r (\\x -> x * 10 + 2))",
      "  pure n",
      "main :: IO Int",
      "main = do",
      "  r <- newIORef 0",
      "  n <- runReaderT (prog r) 5",
      "  seen <- readIORef r",
      "  pure (n + seen)",
      "",
    ].join("\n"),
    expect: 17,
  },
  {
    // A round trip through JavaScript: 7 goes out as a JS number and comes
    // back as an `Int`, and the list becomes a real JS array (its `.length` is
    // read by JavaScript, not by Haskell) before coming back as `[Int]`.
    name: "GHCJS.Marshal: toJSVal / fromJSValUnchecked round trip an Int and a list",
    source: [
      "module Main where",
      "import qualified GHCJS.Marshal as Marshal",
      "import GHC.JS.Prim",
      'foreign import javascript unsafe "((a) => a.length)" jsLength :: JSValPrim -> IntPrim',
      "main :: IO Int",
      "main = do",
      "  v <- Marshal.toJSVal (7 :: Int)",
      "  n <- Marshal.fromJSValUnchecked v",
      "  xs <- Marshal.toJSVal [1, 2, 3 :: Int]",
      "  ys <- Marshal.fromJSValUnchecked xs",
      "  pure (n + total ys + width xs)",
      "width :: JSVal -> Int",
      "width (JSVal a) = I (jsLength a)",
      "total :: [Int] -> Int",
      "total zs = case zs of",
      "  [] -> 0",
      "  (y : rest) -> y + total rest",
      "",
    ].join("\n"),
    expect: 16,
  },
  {
    // Every marshalled list has to be its OWN JS array. The array is built by a
    // nullary `newArray`, so if that is left as a CAF it is evaluated once and
    // every list appends to the same array: the two lists below would then both
    // come out as one 5-element array. 32 = 3 elements, then 2, and distinct.
    name: "GHCJS.Marshal: each marshalled list is a fresh JS array",
    source: [
      "module Main where",
      "import qualified GHCJS.Marshal as Marshal",
      "import GHC.JS.Prim",
      'foreign import javascript unsafe "((a) => a.length)" jsLength :: JSValPrim -> IntPrim',
      'foreign import javascript unsafe "((a,b) => a === b ? 1 : 0)" jsSame :: JSValPrim -> JSValPrim -> IntPrim',
      "main :: IO Int",
      "main = do",
      "  a <- Marshal.toJSVal [1, 2, 3 :: Int]",
      "  b <- Marshal.toJSVal [4, 5 :: Int]",
      "  pure (width a * 10 + width b + same a b)",
      "width :: JSVal -> Int",
      "width (JSVal a) = I (jsLength a)",
      "same :: JSVal -> JSVal -> Int",
      "same (JSVal a) (JSVal b) = I (jsSame a b)",
      "",
    ].join("\n"),
    expect: 32,
  },
  {
    // `fromJSVal` is the *checked* direction, so asking a JS boolean for an
    // `Int` has to be `Nothing` rather than a coerced 0 or 1. `Nothing`
    // marshals to `null` and decodes back as `Just Nothing`.
    name: "GHCJS.Marshal: fromJSVal rejects a wrong type and round trips Maybe",
    source: [
      "module Main where",
      "import qualified GHCJS.Marshal as Marshal",
      "import GHC.JS.Prim",
      "absent :: Maybe Int",
      "absent = Nothing",
      "main :: IO Int",
      "main = do",
      "  b <- Marshal.toJSVal True",
      "  asBool <- Marshal.fromJSVal b",
      "  asInt <- Marshal.fromJSVal b",
      "  m <- Marshal.toJSVal absent",
      "  back <- Marshal.fromJSVal m",
      "  pure (flag asBool + notInt asInt + none back)",
      "flag :: Maybe Bool -> Int",
      "flag m = case m of",
      "  Just True -> 1",
      "  Just False -> 2",
      "  Nothing -> 3",
      "notInt :: Maybe Int -> Int",
      "notInt m = case m of",
      "  Nothing -> 10",
      "  Just _ -> 20",
      "none :: Maybe (Maybe Int) -> Int",
      "none m = case m of",
      "  Just Nothing -> 100",
      "  Just (Just _) -> 200",
      "  Nothing -> 300",
      "",
    ].join("\n"),
    expect: 111,
  },
  {
    // A `JSString` marshals to the JavaScript string it already is - the proof
    // is that JavaScript uppercases it - and `jsval` is the same value again.
    name: "GHCJS.Marshal / GHCJS.Types: a JSString crosses as a JS string",
    source: [
      "module Main where",
      "import qualified GHCJS.Marshal as Marshal",
      "import qualified Data.JSString as J",
      "import Data.JSString (JSString)",
      "import GHCJS.Types",
      "import GHC.JS.Prim",
      'foreign import javascript unsafe "((s) => s.toUpperCase())" shout :: JSValPrim -> JSValPrim',
      "label :: JSString",
      'label = J.pack "hi"',
      "louder :: JSVal -> JSVal",
      "louder (JSVal x) = case shout x of",
      "  y -> JSVal y",
      "main :: [Char]",
      "main = unsafePerformIO (do",
      "  v <- Marshal.toJSVal label",
      "  s <- Marshal.fromJSValUnchecked (louder v)",
      '  pure (J.unpack s ++ (if isNull (jsval label) then "!" else ".")))',
      "",
    ].join("\n"),
    expect: "HI.",
  },
  {
    // A character literal is a `Char`, not the one-element `[Char]` it used to
    // parse as - in an expression, in a pattern, and after an escape. If it
    // were still a list, `isUpper 'A'` would not typecheck at all.
    name: "character literals are Char, in expressions and in patterns",
    source: [
      "module Main where",
      "import Data.Char",
      "grade :: Char -> Int",
      "grade 'a' = 1",
      "grade 'z' = 2",
      "grade c = if isUpper c then 3 else 4",
      "main :: [Char]",
      "main = show (grade 'a') ++ show (grade 'z') ++ show (grade 'Q') ++ show (grade 'm')",
      "     ++ show (toUpper 'q' == 'Q') ++ show ('\\n' == head \"\\nx\") ++ (toLower 'B' : [])",
      "",
    ].join("\n"),
    expect: "1234TrueTrueb",
  },
  {
    // Two parameters, and the *pair* selects: `convert True` and `convert flag`
    // are the same method at two different instances, distinguished only by
    // their second argument. A single-parameter dispatch could not tell them
    // apart, and picking the wrong one would print "True" rather than "1".
    name: "multi-parameter class: the instance is chosen by both arguments",
    source: [
      "module Main where",
      "class Convert a b where",
      "  convert :: a -> b",
      "instance Convert Bool Int where",
      "  convert b = if b then 1 else 0",
      "instance Convert Int [Char] where",
      "  convert n = show n",
      "instance Convert Bool [Char] where",
      "  convert b = if b then \"yes\" else \"no\"",
      "flag :: Int",
      "flag = convert True",
      "digits :: [Char]",
      "digits = convert flag",
      "words_ :: [Char]",
      "words_ = convert True",
      "main :: [Char]",
      "main = digits ++ words_",
      "",
    ].join("\n"),
    expect: "1yes",
  },
  {
    // The fundep is load-bearing here and nowhere else: `n` is passed straight
    // back to `put`, so nothing in the program says what type it has. Only
    // `m -> s` can, by reading it off `State Int`. Without improvement this
    // does not compile at all ("no instance for MonadState t? (StateT Int
    // Identity)"), and a fundep that improved to the wrong type would make
    // `label` write into the counter.
    name: "functional dependency: `m -> s` supplies the type nothing else does",
    source: [
      "module Main where",
      "import Control.Monad.State",
      "counter :: State Int ()",
      "counter = get >>= put",
      "label :: State [Char] ()",
      "label = get >>= (\\s -> put (s ++ \"!\"))",
      "main :: [Char]",
      "main = show (execState counter 7) ++ execState label \"a\"",
      "",
    ].join("\n"),
    expect: "7a!",
  },
  {
    // One `bump`, two monads: the dictionary is a parameter, so this is the
    // whole point of the class rather than of the concrete transformer. The
    // `n + 1` inside it is only well typed because the *given* `MonadState Int
    // m` improves `get`'s state type to `Int`.
    name: "MonadState: one polymorphic action runs at both State and RWS",
    source: [
      "module Main where",
      "import Control.Monad.State",
      "import Control.Monad.RWS",
      "bump :: MonadState Int m => m ()",
      "bump = get >>= (\\n -> put (n + 1))",
      "twice :: MonadState Int m => m ()",
      "twice = bump >> bump",
      "logged :: RWS Int [Int] Int ()",
      "logged = do",
      "  twice",
      "  n <- get",
      "  tell [n]",
      "main :: [Char]",
      "main = show (execState twice 1) ++ \"/\" ++ show (fst (execRWS logged 0 10))",
      "",
    ].join("\n"),
    expect: "3/12",
  },
  {
    // Through a stack: `ask` is the reader's, `get`/`put` are the state's one
    // layer down, reached through the lifting instance's own context. 4*3 = 12
    // and 4+3 = 7. In `copy` nothing but the two fundeps can say what `ask`
    // read or what `put` wrote, so it is the stack's improvement, on its own.
    name: "MonadReader/MonadState: ask and get under a ReaderT over State",
    source: [
      "module Main where",
      "import Control.Monad.Reader",
      "import Control.Monad.State",
      "prog :: ReaderT Int (State Int) Int",
      "prog = do",
      "  r <- ask",
      "  n <- get",
      "  put (n + r)",
      "  pure (n * r)",
      "copy :: ReaderT Int (State Int) ()",
      "copy = ask >>= put",
      "main :: Int",
      "main = case runState (runReaderT prog 3) 4 of",
      "  (a, s) -> case runState (runReaderT copy 9) 0 of",
      "    (b, t) -> a * 100 + s * 10 + t",
      "",
    ].join("\n"),
    expect: 1279,
  },
  {
    // miso's counter in miniature: `Miso.Lens`'s operators are constrained by
    // `MonadState record m` alone, and miso's `Effect` is an `RWS`, so this is
    // the exact shape that a single-parameter class could not express. `use`
    // additionally needs the fundep - nothing but `m -> record` says what
    // `gets` read. Model 5 + 1 = 6, told into the log: 6*10 + 6.
    name: "Miso.Lens shape: `value += 1` at an RWS Effect",
    source: [
      "module Main where",
      "import Control.Monad.State",
      "import Control.Monad.RWS",
      "data Lens record field = Lens (record -> field) (record -> field -> record)",
      "lensGet :: Lens record field -> record -> field",
      "lensGet l r = case l of",
      "  Lens g s -> g r",
      "lensSet :: Lens record field -> record -> field -> record",
      "lensSet l r v = case l of",
      "  Lens g s -> s r v",
      "(%=) :: MonadState record m => Lens record field -> (field -> field) -> m ()",
      "(%=) l f = modify (\\r -> lensSet l r (f (lensGet l r)))",
      "(+=) :: (MonadState record m, Num field) => Lens record field -> field -> m ()",
      "(+=) l x = (%=) l (\\v -> v + x)",
      "use :: MonadState record m => Lens record field -> m field",
      "use l = gets (\\r -> lensGet l r)",
      "newtype Model = Model Int",
      "value :: Lens Model Int",
      "value = Lens (\\m -> case m of Model n -> n) (\\m v -> Model v)",
      "type Effect model = RWS Int [Int] model ()",
      "update :: Effect Model",
      "update = value += 1",
      "report :: Effect Model",
      "report = do",
      "  n <- use value",
      "  tell [n]",
      "main :: Int",
      "main = case execRWS (update >> report) 0 (Model 5) of",
      "  (m, w) -> case m of",
      "    Model n -> case w of",
      "      (x : xs) -> n * 10 + x",
      "      [] -> 0",
      "",
    ].join("\n"),
    expect: 66,
  },
  {
    // `static` is a *source position*, not an allocation: the expected string
    // is GHC's own `mkStaticPtrFingerprint 0` for this unit and module -
    // `fingerprintString "main:Main:0"`, MD5 over four-byte big-endian chars.
    // Anything derived at run time would not reproduce it, and two JS contexts
    // would not agree on it.
    // The two instances differ only in `M1`'s *tag* argument, `D` against `C`,
    // so both have `M1` as their head constructor. An instance table keyed by
    // the head alone gives them one dictionary and one of the two answers
    // twice; this must be "RedGreen".
    name: "generics: instances differing below the head constructor",
    source: [
      "module Main where",
      "import GHC.Generics",
      "data MetaT = MetaT",
      "data MetaK = MetaK",
      "instance Constructor MetaK where",
      "  conName x = \"inner\"",
      "class GN f where",
      "  gn :: f p -> [Char]",
      "instance GN f => GN (M1 D c f) where",
      "  gn (M1 x) = \"Red\" ++ gn x",
      "instance GN (M1 C MetaK f) where",
      "  gn m = \"Green\"",
      "sample :: M1 D MetaT (M1 C MetaK U1) ()",
      "sample = M1 (M1 U1)",
      "main :: [Char]",
      "main = gn sample",
      "",
    ].join("\n"),
    expect: "RedGreen",
  },
  {
    // GHC's overlap rule: of two matching instances the more specific wins,
    // whichever order they were declared in. Written general-first here, which
    // is the order miso's `GToFields` pair has.
    name: "generics: the more specific overlapping instance wins",
    source: [
      "module Main where",
      "import GHC.Generics",
      "class GN f where",
      "  gn :: f p -> [Char]",
      "instance GN (K1 i c) where",
      "  gn x = \"any\"",
      "instance GN (K1 i (Maybe c)) where",
      "  gn x = \"maybe\"",
      "general :: K1 R Int ()",
      "general = K1 3",
      "special :: K1 R (Maybe Int) ()",
      "special = K1 Nothing",
      "main :: [Char]",
      "main = gn general ++ gn special",
      "",
    ].join("\n"),
    expect: "anymaybe",
  },
  {
    // `Rep a` is GHC's associated type family. There are none here, so it is
    // read as the `rep` of `class Generic a rep | a -> rep`: `gname (from x)`
    // typechecks only because the fundep says which representation `from x`
    // produced, and `to (from x)` must come back as the same constructor.
    name: "generics: Rep in a context, resolved by the Generic fundep",
    source: [
      "module Main where",
      "import GHC.Generics",
      "data MetaColour = MetaColour",
      "data MetaRed = MetaRed",
      "data MetaGreen = MetaGreen",
      "instance Constructor MetaRed where",
      "  conName x = \"Red\"",
      "instance Constructor MetaGreen where",
      "  conName x = \"Green\"",
      "data Colour = Red | Green",
      "instance Generic Colour (M1 D MetaColour (M1 C MetaRed U1 :+: M1 C MetaGreen U1)) where",
      "  from c = case c of",
      "    Red -> M1 (L1 (M1 U1))",
      "    Green -> M1 (R1 (M1 U1))",
      "  to r = case r of",
      "    M1 s -> case s of",
      "      L1 l -> Red",
      "      R1 g -> Green",
      "class GName f where",
      "  gname :: f p -> [Char]",
      "instance GName f => GName (M1 D c f) where",
      "  gname (M1 x) = gname x",
      "instance (GName f, GName g) => GName (f :+: g) where",
      "  gname v = case v of",
      "    L1 a -> gname a",
      "    R1 b -> gname b",
      "instance Constructor c => GName (M1 C c f) where",
      "  gname m = conName m",
      "nameOf :: (Generic a, GName (Rep a)) => a -> [Char]",
      "nameOf x = gname (from x)",
      "roundTrip :: Generic a rep => a -> a",
      "roundTrip x = to (from x)",
      "main :: [Char]",
      "main = nameOf Red ++ (nameOf Green ++ nameOf (roundTrip Green))",
      "",
    ].join("\n"),
    expect: "RedGreenGreen",
  },
  {
    // A product, matched infix, through a `(:*:)` instance head - the shape an
    // instance whose head is a type *operator* has.
    name: "generics: a product representation, matched infix",
    source: [
      "module Main where",
      "import GHC.Generics",
      "class GSum f where",
      "  gsum :: f p -> Int",
      "instance GSum (K1 i Int) where",
      "  gsum (K1 n) = n",
      "instance (GSum f, GSum g) => GSum (f :*: g) where",
      "  gsum (a :*: b) = gsum a + gsum b",
      "instance GSum f => GSum (M1 i c f) where",
      "  gsum (M1 x) = gsum x",
      "sample :: M1 C MetaP (K1 R Int :*: (K1 R Int :*: K1 R Int)) ()",
      "sample = M1 (K1 4 :*: (K1 5 :*: K1 6))",
      "data MetaP = MetaP",
      "main :: Int",
      "main = gsum sample",
      "",
    ].join("\n"),
    expect: 15,
  },
  {
    // `deriving Generic` with nothing written by hand: the `Rep` and its
    // metadata come from the shape of the two declarations. The sum's three
    // constructors must come back with their own names (so the balanced
    // `L1`/`R1` tree agrees with itself), the round trip must give the same
    // constructor, and the record's `selName`s must be its field names in
    // declaration order.
    name: "generics: deriving Generic, names and round trip",
    source: [
      "module Main where",
      "import GHC.Generics",
      "data Colour = Red | Green | Blue",
      "  deriving (Generic)",
      "data Point = Point { px :: Int, py :: Int }",
      "  deriving (Generic)",
      "class GName f where",
      "  gname :: f p -> [Char]",
      "instance GName f => GName (M1 D c f) where",
      "  gname (M1 x) = gname x",
      "instance (GName f, GName g) => GName (f :+: g) where",
      "  gname v = case v of",
      "    L1 a -> gname a",
      "    R1 b -> gname b",
      "instance Constructor c => GName (M1 C c f) where",
      "  gname m = conName m",
      "class GFields f where",
      "  gfields :: f p -> [Char]",
      "instance GFields f => GFields (M1 D c f) where",
      "  gfields (M1 x) = gfields x",
      "instance GFields f => GFields (M1 C c f) where",
      "  gfields (M1 x) = gfields x",
      "instance (GFields f, GFields g) => GFields (f :*: g) where",
      "  gfields (a :*: b) = gfields a ++ (\",\" ++ gfields b)",
      "instance (Selector s, Show a) => GFields (M1 S s (K1 R a)) where",
      "  gfields m = selName m ++ (\"=\" ++ showField m)",
      "showField :: Show a => M1 S s (K1 R a) p -> [Char]",
      "showField (M1 (K1 v)) = show v",
      "nameOf :: (Generic a, GName (Rep a)) => a -> [Char]",
      "nameOf x = gname (from x)",
      "fieldsOf :: (Generic a, GFields (Rep a)) => a -> [Char]",
      "fieldsOf x = gfields (from x)",
      "roundTrip :: Generic a rep => a -> a",
      "roundTrip x = to (from x)",
      "main :: [Char]",
      "main = nameOf Red ++ (nameOf Green ++ (nameOf Blue ++ (nameOf (roundTrip Blue) ++ fieldsOf (Point 3 4))))",
      "",
    ].join("\n"),
    expect: "RedGreenBlueBluepx=3,py=4",
  },
  {
    // GHC's DefaultSignatures. `instance Label Colour` writes no method at all,
    // so the class default runs - and it can only run because the *instance*
    // supplies the `Generic Colour rep` and `GName rep` dictionaries that the
    // `default label ::` signature asks for on top of `Label a`.
    name: "generics: a default signature's own constraints, at the instance",
    source: [
      "module Main where",
      "import GHC.Generics",
      "data Colour = Red | Green deriving (Generic)",
      "class GName f where",
      "  gname :: f p -> [Char]",
      "instance GName f => GName (M1 D c f) where",
      "  gname (M1 x) = gname x",
      "instance (GName f, GName g) => GName (f :+: g) where",
      "  gname v = case v of",
      "    L1 a -> gname a",
      "    R1 b -> gname b",
      "instance Constructor c => GName (M1 C c f) where",
      "  gname m = conName m",
      "class Label a where",
      "  label :: a -> [Char]",
      "  default label :: (Generic a, GName (Rep a)) => a -> [Char]",
      "  label x = gname (from x)",
      "instance Label Colour",
      "instance Label Int where",
      "  label n = \"int\"",
      "main :: [Char]",
      "main = label Red ++ (label Green ++ label (1 :: Int))",
      "",
    ].join("\n"),
    expect: "RedGreenint",
  },
  {
    // The ascription is the only thing choosing an instance here: `2` on its
    // own is an ambiguous `Num` wanted and defaults to `Int`. Delete the
    // `:: Double` and this program still compiles - and answers "intint",
    // which is what makes the case worth having.
    name: "ascription: `:: Double` selects an instance defaulting would not",
    source: [
      "module Main where",
      "class Which a where",
      "  which :: a -> [Char]",
      "instance Which Int where",
      "  which n = \"int\"",
      "instance Which Double where",
      "  which n = \"double\"",
      "main :: [Char]",
      "main = which (2 :: Double) ++ which 2",
      "",
    ].join("\n"),
    expect: "doubleint",
  },
  {
    // A string literal whose type is written out goes through `fromString` at
    // that type, which for a `JSString` means a real JavaScript string rather
    // than the `[Char]` the literal starts as. `toUpper` is the JS one, so it
    // could not have run on a list. This is the form miso spells everywhere as
    // `"button" :: MisoString`; inference-driven OverloadedStrings is not here.
    name: "ascription: a string literal at JSString is fromString at JSString",
    source: [
      "module Main where",
      "import Data.JSString",
      "main :: [Char]",
      "main = unpack (toUpper (\"hi\" :: JSString))",
      "",
    ].join("\n"),
    expect: "HI",
  },
  {
    // `Miso.JSON`'s shape exactly: the method ignores its argument and reads
    // the field name off a phantom whose type is written out. The `s` in the
    // ascription is the *instance head's* `s`, so `Selector s` comes from the
    // instance context - which is the only reason `selName` has a dictionary
    // at all. Nothing forces the `undefined`.
    name: "ascription: a phantom's type selects the Selector dictionary",
    source: [
      "module Main where",
      "import GHC.Generics",
      "data Point = Point { px :: Int, py :: Int }",
      "  deriving (Generic)",
      "class GNames f where",
      "  gnames :: f p -> [Char]",
      "instance GNames f => GNames (M1 D c f) where",
      "  gnames (M1 x) = gnames x",
      "instance GNames f => GNames (M1 C c f) where",
      "  gnames (M1 x) = gnames x",
      "instance (GNames f, GNames g) => GNames (f :*: g) where",
      "  gnames (a :*: b) = gnames a ++ (\",\" ++ gnames b)",
      "instance Selector s => GNames (M1 S s (K1 R a)) where",
      "  gnames m = selName (M1 undefined :: S1 s (K1 R a) ())",
      "names :: (Generic a, GNames (Rep a)) => a -> [Char]",
      "names x = gnames (from x)",
      "main :: [Char]",
      "main = names (Point 3 4)",
      "",
    ].join("\n"),
    expect: "px,py",
  },
  {
    // `deriving anyclass` writes the *empty* instance, so `label Red` can only
    // work by running the class's own `default label ::` implementation over
    // the derived `Generic`. The counter's `Model` derives its `ToJSON` this
    // way, down to the separate `stock`/`anyclass` clauses.
    name: "deriving anyclass: the empty instance runs the class default",
    source: [
      "module Main where",
      "import GHC.Generics",
      "class GName f where",
      "  gname :: f p -> [Char]",
      "instance GName f => GName (M1 D c f) where",
      "  gname (M1 x) = gname x",
      "instance (GName f, GName g) => GName (f :+: g) where",
      "  gname v = case v of",
      "    L1 a -> gname a",
      "    R1 b -> gname b",
      "instance Constructor c => GName (M1 C c f) where",
      "  gname m = conName m",
      "class Label a where",
      "  label :: a -> [Char]",
      "  default label :: (Generic a, GName (Rep a)) => a -> [Char]",
      "  label x = gname (from x)",
      "data Colour = Red | Green",
      "  deriving stock (Generic)",
      "  deriving anyclass (Label)",
      // Two anyclass derivations of one default: each needs its *own* `Rep`,
      // and the `Generic` fundep improves each independently.
      "data Shade = Dark | Light",
      "  deriving stock (Generic)",
      "  deriving anyclass (Label)",
      "instance Label Int where",
      "  label n = \"int\"",
      "main :: [Char]",
      "main = label Red ++ (label Green ++ (label Dark ++ label (1 :: Int)))",
      "",
    ].join("\n"),
    expect: "RedGreenDarkint",
  },
  {
    // `deriving newtype` must reach the *wrapped* type's instance in both
    // directions: `tag` takes the newtype apart to call `Tag Int`'s method,
    // and `base` - which mentions `a` only in its result - builds a `Count`
    // out of `Tag Int`'s `41`. If either end picked `Count`'s own instance the
    // derivation would be circular and this would not terminate.
    name: "deriving newtype: the wrapped type's instance, both directions",
    source: [
      "module Main where",
      "class Tag a where",
      "  tag :: a -> [Char]",
      "  base :: a",
      "instance Tag Int where",
      "  tag n = \"int:\" ++ show n",
      "  base = 41",
      "newtype Count = Count Int",
      "  deriving newtype (Tag)",
      "bump :: Count -> Count",
      "bump (Count n) = Count (n + 1)",
      "main :: [Char]",
      "main = tag (bump base)",
      "",
    ].join("\n"),
    expect: "int:42",
  },
  {
    // A string literal is not punctuation: `(","` is an open parenthesis and a
    // string, and `","` inside a list or a case alternative is a value.
    name: "a string literal whose text is punctuation",
    source: [
      "module Main where",
      "sep :: [Char]",
      "sep = \"a\" ++ (\",\" ++ \"b\")",
      "pick :: [Char] -> Int",
      "pick s = case s of",
      "  \")\" -> 1",
      "  _ -> 2",
      "main :: [Char]",
      "main = sep ++ (concat [\",\", \"|\"] ++ showInt (pick \")\"))",
      "",
    ].join("\n"),
    expect: "a,b,|1",
  },
  {
    name: "staticptr: key is GHC's fingerprint of unit:module:index",
    source: [
      "module Main where",
      "answer :: Int",
      "answer = 42",
      "ptr :: StaticPtr Int",
      "ptr = static answer",
      "main :: [Char]",
      "main = show (staticKey ptr)",
      "",
    ].join("\n"),
    expect: "3e1241819ab6d1a7f6669a9e78ccf059",
  },
  {
    // Two *uses* of one `static` form are one pointer with one key; the second
    // `static` in the module is a different form and must differ.
    name: "staticptr: key is stable per form, distinct between forms",
    source: [
      "module Main where",
      "answer :: Int",
      "answer = 42",
      "ptr :: StaticPtr Int",
      "ptr = static answer",
      "other :: StaticPtr Int",
      "other = static answer",
      "main :: Bool",
      "main = staticKey ptr == staticKey ptr && staticKey ptr /= staticKey other",
      "",
    ].join("\n"),
    expect: true,
  },
  {
    name: "staticptr: deRefStaticPtr recovers the value",
    source: [
      "module Main where",
      "answer :: Int",
      "answer = 42",
      "main :: Int",
      "main = deRefStaticPtr (static answer)",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // The registration must have happened before `main` ran, and the lookup
    // must be *by key*: `ptr2` is the second form, so returning the first
    // would give 42.
    name: "staticptr: unsafeLookupStaticPtr finds the entry by key",
    source: [
      "module Main where",
      "answer :: Int",
      "answer = 42",
      "other :: Int",
      "other = 7",
      "ptr :: StaticPtr Int",
      "ptr = static answer",
      "ptr2 :: StaticPtr Int",
      "ptr2 = static other",
      "main :: IO Int",
      "main = unsafeLookupStaticPtr (staticKey ptr2) >>= (\\m -> case m of",
      "  Nothing -> pure 0",
      "  Just p -> pure (deRefStaticPtr p))",
      "",
    ].join("\n"),
    expect: 7,
  },
  {
    // A key nothing registered is a miss, not the nearest entry.
    name: "staticptr: a key with no entry is Nothing",
    source: [
      "module Main where",
      "answer :: Int",
      "answer = 42",
      "ptr :: StaticPtr Int",
      "ptr = static answer",
      "main :: IO Int",
      "main = unsafeLookupStaticPtr (Fingerprint 1 2) >>= (\\m -> case m of",
      "  Nothing -> pure 1",
      "  Just p -> pure (deRefStaticPtr p))",
      "",
    ].join("\n"),
    expect: 1,
  },
  {
    // A `static` in an imported module keeps that module's scope (`hidden` is
    // not in `Main`'s), and its fingerprint names *that* module.
    name: "staticptr: a form in another module",
    sources: {
      Box: [
        "module Box (boxed) where",
        "hidden :: Int",
        "hidden = 11",
        "boxed :: StaticPtr Int",
        "boxed = static hidden",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Box",
        "main :: IO Int",
        "main = unsafeLookupStaticPtr (staticKey boxed) >>= (\\m -> case m of",
        "  Nothing -> pure 0",
        "  Just p -> pure (deRefStaticPtr p))",
        "",
      ].join("\n"),
    },
    expect: 11,
  },
  {
    // `gAllNullary`'s exact shape, from `references/miso/src/Miso/JSON.hs`:
    // the class variable appears nowhere in the method's arguments or result,
    // so `@f` is the only thing that can pick the instance. Erase the `@`s and
    // the recursive instances have no way to name their own constraint.
    name: "visible type application selects an instance the method's type cannot",
    source: [
      "module Main where",
      "data U1 = MkU1",
      "data K1 = MkK1",
      "data C1 f = MkC1 f",
      "data Sum f g = MkSum f g",
      "class GAllNullary f where",
      "  gAllNullary :: Bool",
      "instance GAllNullary U1 where",
      "  gAllNullary = True",
      "instance GAllNullary K1 where",
      "  gAllNullary = False",
      "instance GAllNullary f => GAllNullary (C1 f) where",
      "  gAllNullary = gAllNullary @f",
      "instance (GAllNullary f, GAllNullary g) => GAllNullary (Sum f g) where",
      "  gAllNullary = gAllNullary @f && gAllNullary @g",
      "digit :: Bool -> Int",
      "digit b = if b then 1 else 0",
      "main :: IO Int",
      "main = pure (digit (gAllNullary @(Sum (C1 U1) U1)) * 10 + digit (gAllNullary @(Sum (C1 K1) U1)))",
      "",
    ].join("\n"),
    expect: 10,
  },
  {
    // Two parameters, two overlapping-by-shape instances: only the *order* of
    // the type arguments tells them apart, which is what fixes `@` filling the
    // `forall`'s variables left to right.
    name: "visible type applications fill the forall left to right",
    source: [
      "module Main where",
      "class Which a b where",
      "  which :: Int",
      "instance Which Int Bool where",
      "  which = 1",
      "instance Which Bool Int where",
      "  which = 2",
      "main :: IO Int",
      "main = pure (which @Int @Bool * 10 + which @Bool @Int)",
      "",
    ].join("\n"),
    expect: 12,
  },
  {
    // The parser now keeps `@` in an expression instead of skipping it; in a
    // *pattern* it still binds a name.
    name: "an as-pattern is not a visible type application",
    source: [
      "module Main where",
      "total :: [Int] -> Int",
      "total [] = 0",
      "total (z : zs) = z + total zs",
      "dup :: [Int] -> Int",
      "dup [] = 0",
      "dup xs@(y : ys) = y * 100 + total xs + total ys",
      "main :: IO Int",
      "main = pure (dup [1, 2, 3])",
      "",
    ].join("\n"),
    expect: 111,
  },
  {
    // `forall f a.` was read as the *class* `forall` applied to four types, so
    // the constraint that follows it was silently lost and `@f` had no given.
    name: "an explicit forall does not eat the context that follows it",
    source: [
      "module Main where",
      "class Tagged f where",
      "  tag :: f Int -> Int",
      "instance Tagged Maybe where",
      "  tag m = case m of",
      "    Just n -> n",
      "    Nothing -> 0",
      "both :: forall f . Tagged f => f Int -> f Int -> Int",
      "both a b = tag a + tag b",
      "main :: IO Int",
      "main = pure (both (Just 20) (Just 22))",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // Type names are one global namespace, so a `type Wrap a b` in one place
    // and a `newtype Wrap a` in another are the same name. A synonym has to be
    // saturated to be expanded, which is what keeps the two apart.
    name: "an under-applied synonym is not the synonym",
    sources: {
      Other: [
        "module Other where",
        "type Wrap token a = [(token, a)]",
        "pairs :: Wrap Int Int -> Int",
        "pairs xs = case xs of",
        "  ((k, v) : _) -> k + v",
        "  [] -> 0",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Other",
        "newtype Wrap a = Wrap a",
        "unwrap :: Wrap a -> a",
        "unwrap (Wrap x) = x",
        "main :: IO Int",
        "main = pure (unwrap (Wrap 1) + pairs [(2, 3)])",
        "",
      ].join("\n"),
    },
    expect: 6,
  },
  {
    // OverloadedStrings: a literal is `fromString` at whatever type inference
    // finds, `[Char]` when it finds nothing, and `[Char]` is reached by
    // improvement when only the *element* is open (`"a" ++ "b"`).
    name: "a string literal takes the type its use gives it",
    source: [
      "module Main where",
      "data Tag = Tag [Char]",
      "instance IsString Tag where",
      "  fromString cs = Tag cs",
      "name :: Tag -> [Char]",
      "name (Tag cs) = cs",
      "main :: IO [Char]",
      'main = pure (name "mi" ++ "so")',
      "",
    ].join("\n"),
    expect: "miso",
  },
  {
    // GeneralizedNewtypeDeriving at kind `* -> *`: the instance is at the
    // newtype's *head*, and every method moves the constructor through one
    // application - including `>>=`, whose second argument returns one.
    name: "deriving newtype: Functor, Applicative and Monad on a wrapper",
    source: [
      "module Main where",
      "newtype P a = P { unP :: Either [Char] a } deriving (Functor, Applicative, Monad)",
      "step :: Int -> P Int",
      "step n = if n > 3 then P (Left \"too big\") else pure (n * 2)",
      "run :: Int -> P Int",
      "run k = do",
      "  x <- step k",
      "  y <- step 1",
      "  pure (x + y)",
      "value :: P Int -> Int",
      "value p = case unP (fmap (\\n -> n + 1) p) of",
      "  Right v -> v",
      "  Left _ -> 0",
      "main :: IO Int",
      "main = pure (value (run 2) * 100 + value (run 9))",
      "",
    ].join("\n"),
    expect: 700,
  },
  {
    // `0xDBFF` used to lex as `0` followed by the identifier `xDBFF`.
    name: "hexadecimal, octal and binary literals",
    source: [
      "module Main where",
      "main :: IO Int",
      "main = pure (0xff + 0o17 + 0b101)",
      "",
    ].join("\n"),
    expect: 275,
  },
  {
    // miso's `(mts, bts, web) = unsafePerformIO FFI.getThreads`: a top-level
    // pattern binding names three values from one right-hand side, and each is
    // its own lazy selector. Parsed as a function of the pattern, none of the
    // three was in scope at all.
    name: "a top-level tuple pattern binding names each of its parts",
    source: [
      "module Main where",
      "threads :: (Int, Int, Int)",
      "threads = (1, 20, 300)",
      "(one, twenty, threeHundred) = threads",
      "main :: IO Int",
      "main = pure (one + twenty + threeHundred)",
      "",
    ].join("\n"),
    expect: 321,
  },
  {
    // A pattern binding is irrefutable: nothing is matched until a selector is
    // demanded, so the unmatched half of a diverging pair costs nothing.
    name: "a pattern binding does not force what is never demanded",
    source: [
      "module Main where",
      "loop :: Int",
      "loop = loop",
      "main :: IO Int",
      "main = pure (let (a, _) = (7, loop) in a)",
      "",
    ].join("\n"),
    expect: 7,
  },
  {
    // `let (_, remaining) = S.spanl ...` in Miso.Runtime: the bound names have
    // to reach the body, and a wildcard must not become one of them.
    name: "a let pattern binding binds through a constructor",
    source: [
      "module Main where",
      "split :: [Int] -> (Int, [Int])",
      "split (z : zs) = (z, zs)",
      "split [] = (0, [])",
      "total :: [Int] -> Int",
      "total [] = 0",
      "total (z : zs) = z + total zs",
      "main :: IO Int",
      "main = pure (let (_, rest) = split [1, 2, 3] in total rest)",
      "",
    ].join("\n"),
    expect: 5,
  },
  {
    // `deltaX, deltaY :: Double` in miso's `ScrollEvent`: one signature, two
    // fields. Read as one field with an empty type, every selector after it
    // was off by one.
    name: "record fields may share one type signature",
    source: [
      "module Main where",
      "data P = P { tag :: Int, lo, hi :: Int, extra :: Int }",
      "main :: IO Int",
      "main = pure (let p = P 1 2 3 4 in tag p + lo p * 10 + hi p * 100 + extra p * 1000)",
      "",
    ].join("\n"),
    expect: 4321,
  },
  {
    // `IndexToken {}` in miso's Router: an empty record pattern tests the
    // constructor and binds nothing, whether or not it was declared with
    // record syntax.
    name: "an empty record pattern matches a constructor with no fields",
    source: [
      "module Main where",
      "data T = A Int Int | B",
      "which :: T -> Int",
      "which A {} = 1",
      "which B {} = 2",
      "main :: IO Int",
      "main = pure (which (A 9 9) * 10 + which B)",
      "",
    ].join("\n"),
    expect: 12,
  },
  {
    // `let !new = S.insert key keys` in miso's Keyboard subscription parsed as
    // a binding *named* `!` taking `new` as a parameter, so `new` was unbound
    // at every use. The bang must also still force, at the `in`.
    name: "a bang pattern in a let binds its name and forces it",
    source: [
      "module Main where",
      "import Data.IORef",
      "main :: IO Int",
      "main = do",
      "  r <- newIORef (0 :: Int)",
      "  let !doubled = 21 * 2",
      "  writeIORef r doubled",
      "  readIORef r",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // `Empty` and `(:<|)` are pattern synonyms upstream; here they are the
    // sequence's real constructors, which is what lets Miso.Runtime's queue
    // code be compiled unchanged.
    name: "Data.Sequence: enqueue at the back, match at the front",
    source: [
      "module Main where",
      "import qualified Data.Sequence as S",
      "import Data.Sequence (Seq)",
      "front :: Seq Int -> Int",
      "front s = case s of",
      "  S.Empty -> 0",
      "  (x S.:<| _) -> x",
      "main :: IO Int",
      "main = pure (let q = (S.singleton 1 S.|> 2) S.|> 3",
      "             in case S.spanl (< 3) q of",
      "                  (before, after) -> front after * 100 + length before * 10 + front q)",
      "",
    ].join("\n"),
    expect: 321,
  },
  {
    name: "Numeric.readHex and showHex round-trip",
    source: [
      "module Main where",
      "import Numeric (readHex, showHex)",
      "main :: IO [Char]",
      'main = pure (case readHex "ff!" of',
      '  ((v, rest) : _) -> showHex (v + 1) rest',
      '  [] -> "no")',
      "",
    ].join("\n"),
    expect: "100!",
  },
  {
    // miso's `class At at where type Index at; type IxValue at` - an
    // associated type is the extra class parameter its own parameter
    // determines, so `Index at` in a method's type is solved, not computed.
    name: "associated types are class parameters a fundep determines",
    source: [
      "module Main where",
      "data Box a = Box a",
      "class Keyed c where",
      "  type family Index c :: Type",
      "  type family Elem c :: Type",
      "  lookupAt :: Index c -> c -> Elem c",
      "instance Keyed (Box a) where",
      "  type Index (Box a) = Int",
      "  type Elem (Box a) = a",
      "  lookupAt n b = case b of",
      "    Box x -> x",
      "instance Keyed [a] where",
      "  type Index [a] = Int",
      "  type Elem [a] = a",
      "  lookupAt n xs = case xs of",
      "    [] -> lookupAt n xs",
      "    (y : ys) -> if n <= 0 then y else lookupAt (n - 1) ys",
      "main :: IO Int",
      "main = pure (lookupAt 0 (Box 40) + lookupAt 1 [1, 2 :: Int])",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // miso declares `MTS`, `Options`, `ScrollEvent` and `errorCode` in more
    // than one module. With constructors and record fields global, the second
    // declaration silently replaced the first and every use of the loser was
    // an arity or type error.
    name: "two modules may declare the same constructor and record field",
    sources: {
      Left: [
        "module Left (P(..)) where",
        "data P = Dup { size :: Int }",
        "",
      ].join("\n"),
      Right: [
        "module Right (Q(..)) where",
        "data Q = Dup Int Int | Other { size :: Int }",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import qualified Left as L",
        "import qualified Right as R",
        "wide :: R.Q -> Int",
        "wide q = case q of",
        "  R.Dup a b -> a * b",
        "  R.Other n -> R.size (R.Other n)",
        "main :: IO Int",
        "main = pure (L.size (L.Dup 7) * 100 + wide (R.Dup 2 3) * 10 + wide (R.Other 1))",
        "",
      ].join("\n"),
    },
    expect: 761,
  },
  {
    // GeneralizedNewtypeDeriving moves the constructor through a list argument
    // with `map`, which is exactly the coercion GHC's `coerce` walks past.
    // miso's `newtype Key = Key MisoString deriving newtype (Show, ToJSON)`
    // needs it: `showList`'s argument is `[a]`, and without this the whole
    // derivation was rejected over that one method.
    name: "deriving newtype through a list argument",
    source: [
      "module Main where",
      "newtype Tag = Tag [Char] deriving newtype Show",
      "main = concat [show (Tag \"hi\"), \"|\", showList [Tag \"a\", Tag \"b\"] \"\"]",
      "",
    ].join("\n"),
    expect: '"hi"|["a","b"]',
  },
  {
    // GHC's `showFloat`: fixed notation from 0.1 up to 10^7 and scientific
    // outside it, always with a digit either side of the point, over the
    // shortest digits that read back as the same value. A `Float`'s shortest
    // digits are shorter than the double holding it would suggest.
    name: "Show Double and Show Float, formatted as GHC formats them",
    source: [
      "module Main where",
      "main = concat",
      '  [ show (1 :: Double)',
      '  , "|", show (0.1 :: Double)',
      '  , "|", show (0.01 :: Double)',
      '  , "|", show (1234567 :: Double)',
      '  , "|", show (12345678 :: Double)',
      '  , "|", show (0 :: Double)',
      '  , "|", show (12345.678 :: Double)',
      '  , "|", show (0.1 :: Float)',
      '  , "|", showsPrec 7 (negate 1.5 :: Double) ""',
      '  , "|", show (Just (negate 1.5 :: Double))',
      "  ]",
      "",
    ].join("\n"),
    expect: "1.0|0.1|1.0e-2|1234567.0|1.2345678e7|0.0|12345.678|0.1|(-1.5)|Just (-1.5)",
  },
  {
    // `deriving Show` in GHC's own shape: a nullary constructor bare, a prefix
    // one parenthesised at precedence 11 with each field at 11, a record one
    // as `C {f = v, g = w}` with its *surface* field names - miso's `URI` and
    // `ParseError` both derive it, and both live in modules whose names are
    // now part of the constructor's renamed spelling.
    name: "deriving Show: prefix, record, nullary and nested",
    sources: {
      Shapes: [
        "module Shapes (Wrap(..), Point(..), Flag(..)) where",
        "data Wrap a = Wrap a | Pair a Int deriving Show",
        "data Point = Point { px :: Int, py :: Int } deriving Show",
        "data Flag = On | Off deriving Show",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Shapes",
        "main = concat",
        '  [ show (Wrap (3 :: Int))',
        '  , "|", show (Wrap (Pair (1 :: Int) 2))',
        '  , "|", show (Point 1 (negate 2))',
        '  , "|", show [On, Off]',
        '  , "|", showsPrec 11 (Wrap (5 :: Int)) ""',
        '  , "|", show (Wrap (negate 5 :: Int))',
        "  ]",
        "",
      ].join("\n"),
    },
    expect:
      "Wrap 3" +
      "|Wrap (Pair 1 2)" +
      "|Point {px = 1, py = -2}" +
      "|[On,Off]" +
      "|(Wrap 5)" +
      "|Wrap (-5)",
  },
  {
    // GHC.Show's escaping table, ported case for case. The two `\&` cases are
    // the whole reason it has to be exact: `['\1234','5']` must not print as
    // `"\12345"`, and `['\SO','H']` must not print as `"\SOH"`, because either
    // would read back as a different string.
    name: "Show for Char, String and tuples, escaped as GHC escapes",
    source: [
      "module Main where",
      "main = concat",
      '  [ show "a\\tb\\\\c"',
      "  , \"|\", show '\\''",
      "  , \"|\", show [chr 1234, '5']",
      "  , \"|\", show [chr 14, 'H']",
      "  , \"|\", show (chr 127)",
      '  , "|", show (1 :: Int, 2 :: Int)',
      '  , "|", show [1, 2 :: Int]',
      '  , "|", show (negate 1 :: Int)',
      "  ]",
      "",
    ].join("\n"),
    expect:
      '"a\\tb\\\\c"' +
      "|'\\''" +
      '|"\\1234\\&5"' +
      '|"\\SO\\&H"' +
      "|'\\DEL'" +
      "|(1,2)" +
      "|[1,2]" +
      "|-1",
  },
  {
    // A JSON number is a `Double`, so miso writes `\case 1 -> ...` at that
    // type seven times over. An integer literal pattern at `Double` matches
    // the box's field against the double of that whole number; matching it as
    // an `Int` instead never fires, and reporting it unsupported stopped
    // `Miso.Native.Element.List.Event` and `Miso.JSON` dead.
    name: "an integer literal pattern at Double, and a fractional one",
    source: [
      "module Main where",
      "grade :: Double -> Int",
      "grade 0 = 10",
      "grade 1 = 20",
      "grade 2.5 = 30",
      "grade _ = 40",
      "pick :: Float -> Int",
      "pick 3 = 7",
      "pick _ = 8",
      "main :: IO Int",
      "main = pure (grade 0 * 100000 + grade 1 * 10000 + grade 2.5 * 100 + grade 9 * 10 + pick 3)",
      "",
    ].join("\n"),
    expect: 1000000 + 200000 + 3000 + 400 + 7,
  },
  {
    // `Miso.JSON.decode` chains two of them - `Right x <- p s, Success v <-
    // fromJSON x` - so the second qualifier reads the first's binding, and a
    // guard whose match fails falls through to the next guard, not to the
    // pattern-match failure. `Miso.Runtime` writes one in a case alternative.
    name: "pattern guards: a chain, its bindings, and its fall-through",
    source: [
      "module Main where",
      "data R a = Ok a | Bad",
      "step :: Int -> R Int",
      "step n = if n > 0 then Ok (n + 1) else Bad",
      "pick :: Int -> Int",
      "pick n",
      "  | Ok x <- step n, Ok y <- step x, y > 3 = x * 10 + y",
      "  | Ok x <- step n = x",
      "  | otherwise = 7",
      "alt :: Int -> Int",
      "alt n = case step n of",
      "  Ok x | Ok y <- step x -> y",
      "  _ -> 0",
      "main :: IO Int",
      "main = pure (pick 5 * 10000 + pick 1 * 100 + pick 0 + alt 2)",
      "",
    ].join("\n"),
    expect: 670211,
  },
  {
    // Type *names* are module-scoped too. miso's `Miso.JSON.Types` declares
    // `type Object = Map MisoString Value` while `Miso.DSL` declares an
    // unrelated `newtype Object`; with one global type namespace the declared
    // type won and every signature written at the synonym became the newtype.
    // Arity cannot tell a nullary synonym from a data type, so nothing short
    // of scoping the name separates these two.
    name: "a type synonym and a data type of the same name in two modules",
    sources: {
      Alias: [
        "module Alias (Obj, mk) where",
        "type Obj = [Int]",
        "mk :: Int -> Obj",
        "mk n = [n, n]",
        "",
      ].join("\n"),
      Wrap: [
        "module Wrap (Obj(..)) where",
        "newtype Obj = Obj Int",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Alias (Obj, mk)",
        "import qualified Wrap as W",
        "total :: Obj -> Int",
        "total xs = sum xs",
        "unwrap :: W.Obj -> Int",
        "unwrap w = case w of W.Obj n -> n",
        "main :: IO Int",
        "main = pure (total (mk 5) * 10 + unwrap (W.Obj 3))",
        "",
      ].join("\n"),
    },
    expect: 103,
  },
  {
    // Pointer identity, which `Miso.Runtime.dirtyCheck` asks for before it
    // falls back to `Eq`: two stable names of the same heap object compare
    // equal.
    name: "System.Mem.StableName is object identity",
    source: [
      "module Main where",
      "import System.Mem.StableName (makeStableName)",
      "main :: IO Int",
      "main = do",
      "  let xs = [1, 2, 3 :: Int]",
      "  a <- makeStableName xs",
      "  b <- makeStableName xs",
      "  pure (if a == b then 42 else 0)",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // `foreign import ccall "sym"` is a call to `h$sym` on GHC's JS backend;
    // miso's `Miso.Reload` declares four of them and every use of their names
    // was an unresolved name.
    name: "a ccall foreign import calls its h$-prefixed symbol",
    source: [
      "module Main where",
      'foreign import javascript unsafe "((n) => { globalThis[String.fromCharCode(104,36)+\'ghcts_twice\'] = (x) => x * 2; return n; })" install :: IntPrim -> IntPrim',
      'foreign import ccall unsafe "ghcts_twice" twice :: IntPrim -> IntPrim',
      "main :: IO Int",
      "main = pure (case install 0 of",
      "  _ -> case twice 21 of",
      "    n -> I n)",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // `Control.Category` declares `id` and `(.)` as methods, and miso writes
    // `import Prelude hiding ((.))` beside `import Control.Category ((.))` so
    // that `.` composes lenses. With class methods global, the method would
    // have captured every `.` in the program; scoped, a module that does not
    // import the class keeps the Prelude's.
    name: "Control.Category: `.` is the class method only where it is imported",
    sources: {
      Pair: [
        "module Pair (L(..), get, comp) where",
        "import Control.Category (Category(..))",
        "import Prelude hiding ((.))",
        "data L b a = L (a -> b)",
        "instance Category L where",
        "  id = L (\\x -> x)",
        "  (.) (L f) (L g) = L (\\x -> g (f x))",
        "get :: L b a -> a -> b",
        "get (L f) = f",
        "comp :: L Int Int",
        "comp = L (\\x -> x + 1) . L (\\x -> x * 3)",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Pair (L(..), get, comp)",
        // No `Control.Category` import here: `.` is still the Prelude's.
        "plus :: Int -> Int",
        "plus = (+ 1) . (* 3)",
        "main :: IO Int",
        "main = pure (get comp 2 * 100 + plus 2)",
        "",
      ].join("\n"),
    },
    expect: 907,
  },
  {
    // `import M (T)` names the type and nothing else; only `T(..)` carries its
    // constructors. miso's `Miso.CSS` imports `Miso.Types (Attribute)` next to
    // its own `Styles`, and the wildcard reading made `Miso.Types`' `Styles`
    // shadow it.
    name: "an import list without `(..)` does not bring the constructors",
    sources: {
      Theirs: [
        "module Theirs (T(..)) where",
        "data T = Same Int Int",
        "",
      ].join("\n"),
      Ours: [
        "module Ours (S(..)) where",
        "data S = Same Int",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Ours (S(..))",
        // Later than the one that really exports `Same`: whichever import
        // let it through last wins the scope, so a `Same` leaking out of
        // `Theirs (T)` here would be the two-field one.
        "import Theirs (T)",
        "size :: S -> Int",
        "size (Same n) = n",
        "main :: IO Int",
        "main = pure (size (Same 42))",
        "",
      ].join("\n"),
    },
    expect: 42,
  },
  {
    // `C {..}` fills each unwritten field from the variable of that name in
    // scope. Record fields are module-scoped, so the field's label and the
    // variable it reads are spelled differently by the time `src/sugar.ts`
    // sees them: filling from the label picks up the record *selector*, which
    // type-checks nowhere miso writes one - `Miso.Event.Decoder` builds every
    // decoder this way.
    name: "a record wildcard reads the local variable, not the selector",
    sources: {
      Shape: [
        "module Shape (D(..), make) where",
        "data D = D { wide :: Int, tall :: Int }",
        "make :: Int -> Int -> D",
        // `wide` is written out and `tall` comes from the parameter of that
        // name, which shadows the selector.
        "make wide tall = D { wide = wide * 10, .. }",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Shape (D(..), make)",
        "area :: D -> Int",
        "area D {..} = wide + tall",
        "main :: IO Int",
        "main = pure (area (make 4 2))",
        "",
      ].join("\n"),
    },
    expect: 42,
  },
  {
    // `Miso.Reload` stores the whole runtime behind a `StablePtr`, hands it to
    // JavaScript, and reads it back after the reload. The pointer is the JS
    // backend's own slot index, so what comes back has to be the very closure
    // that went in - unforced, since `deRefStablePtr` is not a `seq`.
    name: "Foreign.StablePtr round-trips a closure through JavaScript",
    source: [
      "module Main where",
      "import Foreign.StablePtr (newStablePtr, deRefStablePtr, freeStablePtr)",
      "main :: IO Int",
      "main = do",
      "  p <- newStablePtr (20 + 22 :: Int)",
      "  q <- newStablePtr (1 :: Int)",
      "  freeStablePtr q",
      "  n <- deRefStablePtr p",
      "  pure n",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // The sized integers wrap, which is the whole of what makes them different
    // from `Int`: `Miso.JSON` writes a `ToJSON`/`FromJSON` pair for each, and
    // one that silently widened would round-trip values GHC does not.
    // 200 :: Word8 stays 200, but 100 + 200 is 44; 100 + 100 :: Int8 is -56;
    // and 2^31 - 1 + 1 :: Int32 is the same overflow `Int` itself has.
    name: "Data.Int and Data.Word wrap at their own widths",
    source: [
      "module Main where",
      "import Data.Int (Int8, Int32)",
      "import Data.Word (Word8, Word)",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if (100 + 200 :: Word8) == 44 then 1 else 0",
      "  , if (100 + 100 :: Int8) == negate 56 then 2 else 0",
      "  , if (2147483647 + 1 :: Int32) == negate 2147483648 then 4 else 0",
      "  , if (0 - 1 :: Word) > 2147483647 then 8 else 0",
      "  , if (65536 * 65536 :: Word) == 0 then 16 else 0",
      "  , if (200 :: Word8) > 100 then 32 else 0",
      "  ])",
      "",
    ].join("\n"),
    expect: 63,
  },
  {
    // `Integer` is GHC's arbitrary-precision integer, and here it is a bignum
    // in Haskell - sign plus base-2^15 limbs - because the target engine has no
    // `BigInt` and GHC emits none either. What that buys is exactness at every
    // width: 2^60 + 1 is a value a JS *number* cannot hold, and 2^200 is one no
    // 64-bit carrier could. `round`/`truncate` land here too, since
    // they now decide on a `Double` and convert once at the end instead of
    // truncating through a 32-bit `Int` on the way out.
    name: "Integer is arbitrary precision, not a JS number",
    source: [
      "module Main where",
      "import Data.Int (Int64)",
      "",
      "twoTo :: Int -> Integer",
      "twoTo n = if n == 0 then 1 else 2 * twoTo (n - 1)",
      "",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if twoTo 60 + 1 - twoTo 60 == 1 then 1 else 0",
      "  , if length (show (twoTo 60 + 1)) == 19 then 2 else 0",
      "  , if twoTo 100 * twoTo 100 == twoTo 200 then 4 else 0",
      "  , if twoTo 200 > twoTo 199 then 8 else 0",
      "  , if round (1152921504606846976.0 :: Double) == twoTo 60 then 16 else 0",
      "  , if truncate (1152921504606846976.0 :: Double) == twoTo 60 then 32 else 0",
      "  , if fromIntegral (4611686018427387904 :: Int64) == twoTo 62 then 64 else 0",
      "  , if show (negate (twoTo 64)) == \"-18446744073709551616\" then 128 else 0",
      "  ])",
      "",
    ].join("\n"),
    expect: 255,
  },
  {
    // `Int64`/`Word64` ride the same bignum carrier and differ only in the
    // wrap after every operation - signed or unsigned, at 64 bits. So
    // they hold every value GHC's do and overflow where GHC's do: maxBound + 1
    // is minBound, 2^64 as a `Word64` is 0, and 2^62 + 1 - 2^62 is 1 rather
    // than 0, which is what a JS number would have made it.
    name: "Int64 and Word64 wrap at 64 bits, and are exact below it",
    source: [
      "module Main where",
      "import Data.Int (Int64)",
      "import Data.Word (Word64)",
      "",
      "pow2i :: Int -> Int64",
      "pow2i n = if n == 0 then 1 else 2 * pow2i (n - 1)",
      "",
      "pow2w :: Int -> Word64",
      "pow2w n = if n == 0 then 1 else 2 * pow2w (n - 1)",
      "",
      "maxI64 :: Int64",
      "maxI64 = pow2i 62 - 1 + pow2i 62",
      "",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if maxI64 + 1 == negate maxI64 - 1 then 1 else 0",
      "  , if pow2i 63 == negate (pow2i 62) - pow2i 62 then 2 else 0",
      "  , if pow2w 64 == 0 then 4 else 0",
      "  , if (0 - 1 :: Word64) > pow2w 63 then 8 else 0",
      "  , if show (pow2w 63) == \"9223372036854775808\" then 16 else 0",
      "  , if show maxI64 == \"9223372036854775807\" then 32 else 0",
      "  , if pow2i 62 + 1 - pow2i 62 == 1 then 64 else 0",
      "  , if show (maxI64 + 1) == \"-9223372036854775808\" then 128 else 0",
      "  ])",
      "",
    ].join("\n"),
    expect: 255,
  },
  {
    // GHC's `Fingerprint` is two `Word64` halves, and so is this one now that
    // there is a `Word64`. `Show` is sixteen zero-padded hex digits each, and
    // `Numeric.readHex` reads a half back at `Word64` - which is what miso's
    // `FromMisoString Fingerprint` writes, and what a `readHex` fixed at `Int`
    // could not have done.
    name: "Fingerprint is GHC's two Word64 halves",
    source: [
      "module Main where",
      "import GHC.Fingerprint (Fingerprint(Fingerprint), fingerprint0)",
      "import Data.Word (Word64)",
      "import Numeric (readHex)",
      "",
      "parseHex :: [Char] -> Word64",
      "parseHex h = case readHex h of",
      "  [] -> 0",
      "  ((w, rest) : more) -> w",
      "",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if show fingerprint0 == \"00000000000000000000000000000000\" then 1 else 0",
      "  , if show (Fingerprint 1 1) == \"00000000000000010000000000000001\" then 2 else 0",
      "  , if parseHex \"deadbeefcafebabe\" == parseHex \"DEADBEEFCAFEBABE\" then 4 else 0",
      "  , if show (Fingerprint (parseHex \"deadbeefcafebabe\") (parseHex \"0123456789abcdef\")) == \"deadbeefcafebabe0123456789abcdef\" then 8 else 0",
      "  , if fingerprint0 == Fingerprint 0 0 then 16 else 0",
      "  , if fingerprint0 == Fingerprint 0 1 then 0 else 32",
      "  ])",
      "",
    ].join("\n"),
    expect: 63,
  },
  {
    // `Natural` shares `Integer`'s carrier and stays a distinct type, because
    // the two hold different value sets - the same test `Data.ByteString` uses
    // to justify sharing one type for strict and lazy bytes.
    name: "Natural converts to and from Integer",
    source: [
      "module Main where",
      "import GHC.Natural (Natural, naturalToInteger, naturalFromInteger)",
      "",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if naturalToInteger (naturalFromInteger 7) == 7 then 1 else 0",
      "  , if show (naturalFromInteger 12345) == \"12345\" then 2 else 0",
      "  , if naturalFromInteger 3 < naturalFromInteger 4 then 4 else 0",
      "  ])",
      "",
    ].join("\n"),
    expect: 7,
  },
  {
    // The carrier, not the answers. Every case above proves the arithmetic and
    // would have kept passing on a `BigInt` carrier - which is exactly how one
    // reached a device that cannot load it. `nativeBigInt` scans the emitted
    // JS of every program in this file, and this one is the program that names
    // all four types that ever held a `BigInt`, so the scan has them to see.
    //
    // Only powers of two appear as literals: a source literal is a JS number
    // by the time the lexer is done with it, so 2^62 is exact and
    // 9223372036854775807 would not have been.
    name: "Integer, Int64, Word64 and Fingerprint emit no native BigInt",
    source: [
      "module Main where",
      "import Data.Int (Int64)",
      "import Data.Word (Word64)",
      "import GHC.Natural (naturalFromInteger)",
      "import GHC.Fingerprint (Fingerprint(Fingerprint))",
      "",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if show (2 * 4611686018427387904 :: Integer) == \"9223372036854775808\" then 1 else 0",
      "  , if show (2 * 4611686018427387904 :: Int64) == \"-9223372036854775808\" then 2 else 0",
      "  , if show (2 * 4611686018427387904 :: Word64) == \"9223372036854775808\" then 4 else 0",
      "  , if (4 * 4611686018427387904 :: Word64) == 0 then 8 else 0",
      "  , if show (naturalFromInteger 4611686018427387904) == \"4611686018427387904\" then 16 else 0",
      "  , if show (Fingerprint 255 4294967296) == \"00000000000000ff0000000100000000\" then 32 else 0",
      "  ])",
      "",
    ].join("\n"),
    expect: 63,
  },
  {
    // `Data.Char` classifies through the RTS's own Unicode tables
    // (`rts/js/unicode.js`), which are GHC's. Nothing else in this file calls
    // one, and the regexes they replaced - `/\p{Lu}/u` and six siblings - were
    // right under node and a SyntaxError in the bundler, so a gate that never
    // packs cannot tell the two apart by any answer. This one at least proves
    // the tables are linked, reached, and say what GHC says.
    //
    // `isPunctuation '+'` is False on purpose: the old `\p{P}|\p{S}` called
    // every symbol punctuation too, and GHC keeps those apart.
    name: "Data.Char classifies by GHC's Unicode tables, not a regex",
    source: [
      "module Main where",
      "import Data.Char (isUpper, isLower, isAlpha, isAlphaNum, isSpace, isPunctuation, isControl, toLower, toUpper)",
      "",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if isAlpha '\\233' && isLower '\\233' then 1 else 0",
      "  , if isUpper '\\201' && not (isLower '\\201') then 2 else 0",
      "  , if toLower '\\201' == '\\233' && toUpper '\\233' == '\\201' then 4 else 0",
      "  , if isAlphaNum '\\1635' && not (isAlpha '\\1635') then 8 else 0",
      "  , if isPunctuation '-' && not (isPunctuation '+') then 16 else 0",
      "  , if isSpace '\\8195' && not (isSpace 'a') then 32 else 0",
      "  , if isControl '\\7' && not (isControl 'a') then 64 else 0",
      "  ])",
      "",
    ].join("\n"),
    expect: 127,
  },
  {
    // A rank-2 argument, which is miso's `Miso.Lens.fromVL`. `VL` is used at
    // TWO functors in one body - `Const` to read and `Identity` to write - so
    // its `Functor f` cannot be hoisted to one `f` for the whole signature.
    // The half that matters at run time is the elaboration: `toVL` takes its
    // dictionary as a parameter, so `fromVL (toVL l)` has to hand over a
    // dictionary-TAKING function rather than one already applied to a
    // dictionary. Getting the typing right and that wrong would typecheck and
    // mis-run; 39 is what says it did not.
    name: "a rank-2 argument used at two functors in one body",
    source: [
      "module Main where",
      "",
      "data Const a b = Const a",
      "data Identity a = Identity a",
      "data Lens s a = Lens (s -> a) (a -> s -> s)",
      "data P = P Int Int",
      "",
      "getConst :: Const a b -> a",
      "getConst (Const a) = a",
      "",
      "runIdentity :: Identity a -> a",
      "runIdentity (Identity a) = a",
      "",
      "instance Functor (Const a) where",
      "  fmap f (Const x) = Const x",
      "",
      "instance Functor Identity where",
      "  fmap f (Identity a) = Identity (f a)",
      "",
      "type VL s a = forall f. Functor f => (a -> f a) -> s -> f s",
      "",
      "toVL :: Lens s a -> VL s a",
      "toVL (Lens g st) = \\f s -> fmap (\\a -> st a s) (f (g s))",
      "",
      "fromVL :: VL s a -> Lens s a",
      "fromVL l = Lens (\\s -> getConst (l Const s)) (\\a s -> runIdentity (l (\\_ -> Identity a) s))",
      "",
      "fstL :: Lens P Int",
      "fstL = Lens (\\p -> case p of P a b -> a) (\\x p -> case p of P a b -> P x b)",
      "",
      "main :: IO Int",
      "main = case fromVL (toVL fstL) of",
      "  Lens g st -> case st 30 (P 1 2) of",
      "    P a b -> pure (g (P 7 0) + a + b)",
      "",
    ].join("\n"),
    expect: 39,
  },
  {
    // `Float` is single precision, and the only thing that says so on a backend
    // where every number is a JS double is the `Math.fround` each `Float*Op`
    // ends with. 0.1 + 0.2 at single precision is exactly the float nearest
    // 0.30000001192092896, which is NOT the double 0.1 + 0.2; and 16777216 + 1
    // does not fit a float's 24-bit significand, so it stays 16777216.
    name: "Float is single precision, not Double under another name",
    source: [
      "module Main where",
      "big :: Float",
      "big = 16777216",
      "main :: IO Int",
      "main = pure (sum",
      "  [ if big + 1 == big then 1 else 0",
      "  , if (16777216 + 1 :: Double) /= 16777216 then 2 else 0",
      "  , if realToFrac (0.1 + 0.2 :: Float) /= (0.1 + 0.2 :: Double) then 4 else 0",
      "  , if realToFrac (1.5 :: Float) == (1.5 :: Double) then 8 else 0",
      "  , if (1 / 4 :: Float) == 0.25 then 16 else 0",
      "  ])",
      "",
    ].join("\n"),
    expect: 31,
  },
  {
    // `[x ..]`, `[x .. y]`, `[x, y ..]` and `[x, y .. z]` reach the elaborator
    // as `enumFrom` and friends, and none of the four had a definition -
    // `Miso.Lens`'s `at` for lists indexes with `zip [0 ..] xs`, which needs
    // the first one to be lazy in its tail.
    name: "the enumFrom family, and [x ..] is lazy in its tail",
    source: [
      "module Main where",
      "main :: IO Int",
      "main = pure (sum",
      "  [ sum [1 .. 4]",
      "  , sum (map fst (zip [10, 20 ..] \"abc\"))",
      "  , sum [9, 7 .. 1]",
      "  , length [1 .. 0]",
      "  , sum (map fst (zip [1 ..] \"xy\"))",
      "  ])",
      "",
    ].join("\n"),
    // 10 + (10+20+30) + (9+7+5+3+1) + 0 + (1+2)
    expect: 98,
  },
  {
    // The reader instances for `(->) r`. `Miso.Lens`'s `preview`, `preuse` and
    // `(^?)` are all `asks . preview`, which instantiates the inner call at
    // `m ~ (->) r`; without `Functor`/`Applicative`/`Monad`/`MonadReader` for
    // the function type every one of them was an unsolved wanted.
    name: "(->) r is a Functor, an Applicative, a Monad and a MonadReader",
    source: [
      "module Main where",
      "import Control.Monad.Reader (ask, asks)",
      "main :: IO Int",
      "main = pure (sum",
      "  [ fmap (+ 1) (* 2) 5",
      "  , ((+) <$> (* 3) <*> (+ 10)) 1",
      "  , ((* 2) >>= (\\d r -> d + r)) 4",
      "  , ask 7",
      "  , asks (+ 1) 100",
      "  ])",
      "",
    ].join("\n"),
    // 11 + (3 + 11) + (8 + 4) + 7 + 101
    expect: 145,
  },
  {
    // `type Lens' s a = forall f. Functor f => ...`: expanding the synonym
    // stopped at the `=>` and handed back the *constraint* as the type, so
    // `Miso.Lens.toVL`'s result was `Functor f`. The context belongs to
    // whatever signature mentioned the synonym.
    name: "a type synonym whose body carries a forall and a context",
    source: [
      "module Main where",
      "import Data.Kind (Type)",
      "import Data.Functor.Identity (Identity(..), runIdentity)",
      "",
      "type Lens' s a = forall (f :: Type -> Type). Functor f => (a -> f a) -> s -> f s",
      "",
      "_fst :: Lens' (Int, Int) Int",
      "_fst f (a, b) = fmap (\\a' -> (a', b)) (f a)",
      "",
      "main :: IO Int",
      "main = pure (fst (runIdentity (_fst (\\x -> Identity (x + 1)) (7, 9))))",
      "",
    ].join("\n"),
    expect: 8,
  },
  {
    // `(,)` is the pair *constructor*, the way `[]` is the list one. Read as an
    // ordinary parenthesised type it became a type named `,`, so the head of
    // base's `instance Bifunctor (,)` and the `(a, c)` in its own method body
    // were two different types.
    name: "(,) names the pair type constructor in an instance head",
    source: [
      "module Main where",
      "import Data.Bifunctor (bimap, first, second)",
      "main :: IO Int",
      "main = pure (fst (bimap (+ 1) (* 2) (3, 4)) + snd (bimap (+ 1) (* 2) (3, 4))",
      "  + fst (first (+ 5) (1, 2)) + snd (second (* 3) (1, 2)))",
      "",
    ].join("\n"),
    // (4 + 8) + 6 + 6
    expect: 24,
  },
  {
    // A pattern binding is split into one selector per name it binds, and for
    // `C {..}` those names come from C's declaration - which may sit *below*
    // the binding in the file, as miso's `data ComponentState` does. Reading
    // the fields only from what had been parsed so far bound nothing, and every
    // use fell through to the top-level selector of the same name.
    name: "RecordWildCards in a pattern binding, record declared later",
    source: [
      "{-# LANGUAGE RecordWildCards #-}",
      "module Main where",
      "use :: R -> Int",
      "use r = go",
      "  where",
      "    R {..} = r",
      "    go = _f _a",
      "",
      "data R = R { _a :: Int, _f :: Int -> Int }",
      "",
      "main :: IO Int",
      "main = pure (use (R 20 (+ 2)))",
      "",
    ].join("\n"),
    expect: 22,
  },
  {
    // `Data.JSString` is the text-shaped API: `concatMap` walks the characters
    // of a JSString, as `Data.Text.concatMap` does. Typed over a list instead,
    // every caller inferred a `String` argument.
    name: "Data.JSString.concatMap walks a JSString, not a list",
    source: [
      "module Main where",
      "import qualified Data.JSString as J",
      "main :: IO Int",
      "main = pure (J.length (J.concatMap (\\c -> if c == 'a' then J.pack \"xy\" else J.singleton c) (J.pack \"banana\")))",
      "",
    ].join("\n"),
    // b a n a n a -> b xy n xy n xy
    expect: 9,
  },
  {
    // OverloadedStrings in *pattern* position: GHC reads `"LT"` as an
    // overloaded literal and desugars it to `x == fromString "LT"`. Expanded
    // into the list of characters it denotes, the scrutinee was pinned to
    // `String`, so every `case s of "LT" -> ...` over a `MisoString` - miso
    // writes a dozen - was a type error. A `String` scrutinee still works, and
    // a nested literal is lifted the same way as a top-level one.
    name: "a string literal pattern matches a MisoString, not only a String",
    source: [
      "module Main where",
      "import qualified Data.JSString as J",
      "",
      "classify :: J.JSString -> Int",
      "classify \"LT\" = 1",
      "classify \"GT\" = 2",
      "classify _    = 3",
      "",
      "nested :: Maybe J.JSString -> Int",
      "nested (Just \"ab\") = 10",
      "nested _           = 20",
      "",
      "main :: IO Int",
      "main = pure (classify (J.pack \"GT\") + nested (Just (J.pack \"ab\")) + classify (J.pack \"zz\")",
      "  + (case J.pack \"LT\" of { \"LT\" -> 100; _ -> 0 })",
      "  + (case \"hi\" of { \"ho\" -> 0; \"hi\" -> 1000; _ -> 1 }))",
      "",
    ].join("\n"),
    // 2 + 10 + 3 + 100 + 1000
    expect: 1115,
  },
  {
    // An instance's method binder is resolved against the *class*, not the
    // value namespace: `import Miso.String (ToMisoString)` brings in the class
    // without `toMisoString`, and the instance below is still legal Haskell.
    // Read as an ordinary binding the name was unknown, so the instance came
    // out with no method at all. `r@R { .. }` is the second half: `@` is an
    // as-pattern, and reading it as the operator being defined made
    // `fmap f r@R { body = b } = ...` a definition of `@`.
    name: "an instance binds a method it did not import, through an as-pattern",
    sources: {
      Lib: [
        "module Lib (Boxed(..), Widen) where",
        "class Widen a where",
        "  widen :: a -> Int",
        "data Boxed a = Boxed { tag :: Int, body :: a }",
        "",
      ].join("\n"),
      Instances: [
        // The class is imported by name only, so `widen` is *not* in scope here.
        "module Instances () where",
        "import Lib (Boxed(..), Widen)",
        "",
        "instance Widen (Boxed Int) where",
        "  widen b@Boxed { body = x } = tag b + x",
        "",
        "instance Functor Boxed where",
        "  fmap f r@Boxed { body } = r { body = f body }",
        "",
      ].join("\n"),
      Main: [
        "module Main where",
        "import Lib (Boxed(..), Widen(..))",
        "import Instances ()",
        "",
        "main :: IO Int",
        "main = pure (widen (fmap (+ 1) (Boxed 10 31)))",
        "",
      ].join("\n"),
    },
    expect: 42,
  },
  {
    // `<|>` is `infixl 3` in base. Left to the parser's fallback fixity it tied
    // with `.:`, so miso's `o .: "keyCode" <|> o .: "which"` associated as
    // `((o .: "keyCode") <|> o) .: "which"`.
    name: "<|> binds looser than an undeclared operator",
    source: [
      "module Main where",
      "import Control.Applicative ((<|>))",
      "",
      "(.!) :: [(Int, Int)] -> Int -> Maybe Int",
      "kvs .! k = lookup k kvs",
      "",
      "main :: IO Int",
      "main = pure (maybe 0 id (table .! 9 <|> table .! 2 <|> table .! 1))",
      "  where table = [(1, 100), (2, 42)]",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // `properFraction` splits into the integer part towards zero and the signed
    // remainder; miso's `ToMisoString Value` prints a whole `Number` as an
    // `Int` by pattern-matching `(i, 0.0) <- properFraction n`.
    name: "properFraction keeps the sign of the remainder",
    source: [
      "module Main where",
      "main :: IO Int",
      "main = pure (sum",
      "  [ case properFraction (3.75 :: Double) of (i, f) -> i * 10 + round (f * 100)",
      "  , case properFraction (negate 3.75 :: Double) of (i, f) -> i * 10 + round (f * 100)",
      "  , case properFraction (7.0 :: Double) of (i, f) -> if f == 0.0 then i else 0",
      "  ])",
      "",
    ].join("\n"),
    // (30 + 75) + (-30 + -75) + 7
    expect: 7,
  },
  {
    // Two names GHCJS has that this library did not. `mkJSException` wraps a
    // rejected promise's value - miso's `await` throws its result - and with no
    // `Exception` class here the throwable shape is `SomeException`, which is
    // already the JavaScript value that was thrown. `GHC.Fingerprint`'s
    // `Fingerprint` is this compiler's `StaticKey`: GHC's own two `Word64`
    // halves, and the same 32-hex-digit `Show` as GHC's - zero padded, so a
    // half that needs one digit still prints sixteen.
    name: "mkJSException builds a SomeException, and Fingerprint is StaticKey",
    source: [
      "module Main where",
      "import GHC.JS.Prim (jsNull, mkJSException)",
      "import GHC.Fingerprint (Fingerprint(Fingerprint))",
      "import GHC.StaticPtr (StaticKey)",
      "import Control.Exception (SomeException)",
      "",
      "wrapped :: SomeException -> Int",
      "wrapped _ = 1",
      "",
      "same :: Fingerprint -> StaticKey",
      "same k = k",
      "",
      "main :: IO Int",
      "main = do",
      "  e <- mkJSException jsNull",
      "  pure (wrapped e + length (show (same (Fingerprint 1 2))) + length (show e))",
      "",
    ].join("\n"),
    // 1 + 32 hex digits + `null`
    expect: 37,
  },
  {
    // A *kinded* binder is still a binder. `newtype Path (path :: Symbol)`
    // counted zero parameters, so the type an instance was declared at and the
    // type a signature wrote were different arities - which surfaced a phase
    // later as "guarded bodies have different types" in miso's `Miso.Router`.
    name: "a kinded type-variable binder is a parameter",
    source: [
      "module Main where",
      "import GHC.TypeLits (Symbol)",
      "",
      "newtype Tagged (tag :: Symbol) = Tagged Int",
      "",
      "class Sized a where size :: a -> Int",
      "instance Sized (Tagged t) where size (Tagged n) = n",
      "",
      "main :: IO Int",
      "main = pure (size (Tagged 42 :: Tagged Bool))",
      "",
    ].join("\n"),
    expect: 42,
  },
  {
    // `KnownSymbol` has no instance declarations anywhere: the dictionary is
    // built from the literal the constraint is solved *at*. All three spellings
    // miso's `Miso.Router` uses have to reach the same literal - `Proxy @s`
    // under an instance head, `Proxy @p` and `Proxy :: Proxy p` under a
    // `forall` in a signature, the last of which is ScopedTypeVariables.
    name: "symbolVal reads a type-level string literal",
    source: [
      "module Main where",
      "import Data.Proxy",
      "import GHC.TypeLits",
      "",
      "newtype Path (path :: Symbol) = Path Int",
      "",
      "class Named a where nameOf :: a -> String",
      "instance KnownSymbol s => Named (Path s) where",
      "  nameOf p = symbolVal (Proxy @s)",
      "",
      "viaAt :: forall p . KnownSymbol p => Path p -> String",
      "viaAt _ = symbolVal (Proxy @p)",
      "",
      "viaAnnot :: forall p . KnownSymbol p => Path p -> String",
      "viaAnnot _ = symbolVal (Proxy :: Proxy p)",
      "",
      "main :: IO Int",
      "main = pure (length (nameOf (Path 1 :: Path \"abc\")) * 100",
      "           + length (viaAt (Path 2 :: Path \"de\")) * 10",
      "           + length (viaAnnot (Path 3 :: Path \"f\")))",
      "",
    ].join("\n"),
    // The three literals are three, two and one character long.
    expect: 321,
  },
  {
    // The characters, not just the length: a literal that differs only in case
    // and content proves the dictionary carries *this* symbol and not the last
    // one solved for.
    name: "distinct symbol literals give distinct strings",
    source: [
      "module Main where",
      "import Data.Proxy",
      "import GHC.TypeLits",
      "",
      "name :: forall s . KnownSymbol s => Proxy s -> String",
      "name = symbolVal",
      "",
      "main :: IO Int",
      "main = pure (if name (Proxy @\"users\") ++ \"/\" ++ name (Proxy @\"Id\") == \"users/Id\" then 1 else 0)",
      "",
    ].join("\n"),
    expect: 1,
  },
  {
    // `Traversable` is a class now: `traverse` carries an `Applicative`
    // constraint over an `f` the class never mentions, which used to be
    // dropped on the floor - the instance body was then left wanting
    // `Applicative` at a rigid variable with no given to discharge it.
    name: "Traversable is a class whose method carries its own constraint",
    source: [
      "module Main where",
      "import qualified Data.Map as M",
      "",
      "data Pair a = Pair a a",
      "instance Functor Pair where fmap f (Pair a b) = Pair (f a) (f b)",
      "instance Foldable Pair where foldr f z (Pair a b) = f a (f b z)",
      "instance Traversable Pair where traverse f (Pair a b) = liftA2 Pair (f a) (f b)",
      "",
      "main :: IO Int",
      "main = do",
      "  Pair x y <- traverse (\\n -> pure (n * 2)) (Pair 3 4)",
      "  ns <- traverse (\\n -> pure (n + 1)) [1, 2, 3]",
      // A `Map` is traversed in key order, and the shape has to survive it.
      "  m <- traverse (\\n -> pure (n * 10)) (M.fromList [(1, 1), (2, 2), (3, 3)])",
      "  pure (x + y + sum ns + sum (M.elems m) + M.size m)",
      "",
    ].join("\n"),
    // (6 + 8) + (2 + 3 + 4) + (10 + 20 + 30) + 3
    expect: 86,
  },
  {
    // `Applicative`, not `Monad`: the effect below has no `>>=` at all, so the
    // constraint `traverse` carries has to be exactly the one it declared.
    name: "traverse works under an Applicative that is not a Monad",
    source: [
      "module Main where",
      "",
      "newtype Count a = Count Int",
      "instance Functor Count where fmap f (Count n) = Count n",
      "instance Applicative Count where",
      "  pure x = Count 0",
      "  (<*>) (Count a) (Count b) = Count (a + b)",
      "",
      "runCount :: Count [Int] -> Int",
      "runCount (Count n) = n",
      "",
      "main :: IO Int",
      "main = pure (runCount (traverse (\\n -> Count n) [1, 2, 3, 4]))",
      "",
    ].join("\n"),
    expect: 10,
  },
  {
    // GeneralizedNewtypeDeriving where the class variable is the *last
    // argument of the result*: `Either [Char] a`, miso's `Parser a`. GHC
    // coerces through it for free; a real one-field constructor has to `fmap`,
    // and the constructor's own field type is what reads the inner call at the
    // wrapped type without any ascription.
    name: "deriving newtype through a functor-shaped result",
    source: [
      "module Main where",
      "",
      "class Parse a where parseIt :: [Char] -> Either [Char] a",
      "instance Parse Int where parseIt s = Right (length s)",
      "",
      "newtype Code = Code Int deriving Parse",
      "",
      "unCode :: Code -> Int",
      "unCode (Code n) = n",
      "",
      "main :: IO Int",
      "main = pure (either (\\_ -> 0) unCode (parseIt \"abcd\"))",
      "",
    ].join("\n"),
    expect: 4,
  },
  {
    // `Enum` was in the stock-derivable list but nothing built the instance.
    // The bounds matter as much as the mapping: the class's own `enumFrom`
    // walks to `maxBound :: Int`, so `[Red ..]` on a three-constructor type
    // ran until `toEnum` errored.
    name: "deriving Enum, bounded by the last constructor",
    source: [
      "module Main where",
      "data Colour = Red | Green | Blue deriving (Show, Eq, Enum)",
      "main :: IO Int",
      "main = pure (fromEnum Blue * 100 + fromEnum (toEnum 1 :: Colour) * 10 + length [Red ..])",
      "",
    ].join("\n"),
    expect: 213,
  },
  {
    // An instance method is re-lexed from tokens whose layout punctuation has
    // already been printed as ordinary `{`/`;`/`}`. The scan that decides
    // whether a do-statement is a bind only recognised the *virtual* spelling,
    // so it ran past this statement's end and found the next statement's `<-`.
    // The method then failed to parse and was dropped in silence, and the
    // instance took the class default instead - which is how miso's
    // `instance FromJSVal Closed` came to want a `Generic` instance.
    name: "a non-bind do-statement inside an instance method",
    source: [
      "module Main where",
      "",
      "class Grab a where",
      "  grab :: Maybe Int -> Maybe a",
      "  grab m = Nothing",
      "",
      "newtype Boxed = Boxed Int",
      "",
      "unBox :: Maybe Boxed -> Int",
      "unBox Nothing = 0",
      "unBox (Just (Boxed n)) = n",
      "",
      "instance Grab Boxed where",
      "  grab o = do",
      "    n <- do pure =<< o",
      "    m <- Just 10",
      "    pure (Boxed (n + m))",
      "",
      "main :: IO Int",
      "main = pure (unBox (grab (Just 30)))",
      "",
    ].join("\n"),
    // 0 if the method were dropped and the class default used.
    expect: 40,
  },
  {
    // GHC's `IOException` is this frontend's one exception shape, so miso's
    // `instance ToMisoString IOException` has a `Show` to reach.
    name: "IOException is the exception shape there is",
    source: [
      "module Main where",
      "import Control.Exception (IOException)",
      "import GHC.JS.Prim (jsNull, mkJSException)",
      "",
      "shown :: IOException -> Int",
      "shown e = length (show e)",
      "",
      "main :: IO Int",
      "main = mkJSException jsNull >>= (\\e -> pure (shown e))",
      "",
    ].join("\n"),
    // `null`
    expect: 4,
  },
  {
    // A `ByteString` is a JavaScript Uint8Array and the UTF-8 codecs are the
    // platform's own, so a round trip through bytes has to survive a character
    // that is not one byte wide - which is the whole reason bytes are not
    // aliased to a string here.
    name: "encodeUtf8 and decodeUtf8 are the real codecs",
    source: [
      "module Main where",
      "import qualified Data.ByteString as B",
      "import qualified Data.ByteString.Builder as BB",
      "import qualified Data.Text.Lazy.Encoding as LT",
      "import Data.JSString (JSString, unpack)",
      "",
      "text :: JSString",
      "text = \"h\\955!\"",
      "",
      "main :: IO Int",
      "main = pure (B.length (LT.encodeUtf8 text) * 100",
      // The lambda is two UTF-8 bytes, so the encoded length is 4 and the
      // decoded one is 3.
      "           + length (unpack (LT.decodeUtf8 (LT.encodeUtf8 text))) * 10",
      "           + B.length (BB.toLazyByteString (BB.byteString (LT.encodeUtf8 text) <> BB.charUtf8 \'x\')))",
      "",
    ].join("\n"),
    // 4 bytes, 3 characters, 5 bytes once `x` is appended.
    expect: 435,
  },
  {
    // Let-polymorphism. A `where` group was inferred in written order and
    // monomorphically, so a helper used at two types was whichever type its
    // last use pinned. miso's `Miso.JSON.Lexer` has exactly one of these:
    // `escaped = (char '\\' *>)`, used at `Lexer Char` and at `Lexer Int`.
    name: "a where-bound helper used at two types",
    source: [
      "module Main where",
      "",
      "f :: Int",
      "f = a + length b",
      "  where",
      "    twice g x = g (g x)",
      "    a = twice (+ 1) 10",
      "    b = twice (\\ys -> ys ++ ys) \"ab\"",
      "",
      "main :: IO Int",
      "main = pure f",
      "",
    ].join("\n"),
    // 12, and "abababab".
    expect: 20,
  },
  {
    // A `let`/`where` type signature was parsed and thrown away, so a binding
    // whose type only its signature fixes was left with an unsolved
    // constraint on a free variable - which reached the backend as
    // `$dictionaryNotFound` and was reported by nobody.
    name: "a where-bound signature fixes an otherwise ambiguous type",
    source: [
      "module Main where",
      "",
      "class Def a where def :: Int -> a",
      "instance Def Int where def n = n",
      "instance Def Bool where def n = n > 0",
      "",
      "f :: Int",
      "f = length (show b)",
      "  where",
      "    b :: Bool",
      "    b = def 5",
      "",
      "main :: IO Int",
      "main = pure f",
      "",
    ].join("\n"),
    // `show True`
    expect: 4,
  },
  {
    // A local signature names types in the module's scope, so it has to be
    // renamed with everything else: unrenamed it says `Widget` where the
    // program says `Types_Widget`.
    name: "a where-bound signature naming another module's type",
    sources: {
      Types: ["module Types where", "data Widget = Widget Int", "unwrap :: Widget -> Int", "unwrap (Widget n) = n", ""].join("\n"),
      Main: [
        "module Main where",
        "import Types",
        "",
        "f :: Int",
        "f = unwrap w",
        "  where",
        "    w :: Widget",
        "    w = Widget 42",
        "",
        "main :: IO Int",
        "main = pure f",
        "",
      ].join("\n"),
    },
    expect: 42,
  },
  // Existential constructor contexts. The constraints are real fields, stored
  // ahead of the declared ones: building one stores the dictionary the
  // construction site solved, matching one binds it and makes it a given.
  {
    name: "existential: a class the body actually calls",
    source: [
      "module Main where",
      "data Showable = forall a . Show a => MkShowable a",
      "render :: Showable -> [Char]",
      "render (MkShowable x) = show x",
      "main = render (MkShowable True) ++ render (MkShowable (42 :: Int))",
      "",
    ].join("\n"),
    expect: "True42",
  },
  {
    name: "existential: two constraints from one constructor",
    source: [
      "module Main where",
      "data Keyed = forall a . (Eq a, Show a) => Keyed a a",
      "describe :: Keyed -> [Char]",
      "describe (Keyed x y) = show (x == y) ++ show x",
      "main = describe (Keyed (1 :: Int) 1) ++ describe (Keyed True False)",
      "",
    ].join("\n"),
    expect: "True1FalseTrue",
  },
  {
    // miso's own shape: `SomeComponent` lives inside `View`, so the dictionary
    // travels in the tree and is only unpacked where the node is matched.
    name: "existential: stored in a data structure and pulled back out",
    source: [
      "module Main where",
      "data Some = forall a . Show a => Some a",
      "data Tree = Node [Tree] | Leaf Some",
      "flatten :: Tree -> [Char]",
      "flatten (Leaf (Some x)) = show x",
      "flatten (Node kids) = concatMap flatten kids",
      "main = flatten (Node [Leaf (Some (1 :: Int)), Node [Leaf (Some True)], Leaf (Some 'z')])",
      "",
    ].join("\n"),
    expect: "1True'z'",
  },
  {
    // A pattern's dictionary is in scope for that pattern's body and nothing
    // else. Here the constraint is at `Int` on both sides, so a given that
    // outlived its alternative would be picked for the second `==` too - and
    // would name a binder that is not in scope there.
    name: "existential: a matched dictionary does not escape its alternative",
    source: [
      "module Main where",
      "data Boxed a = Eq a => MkBoxed a",
      "leak :: Boxed Int -> [Char]",
      "leak b = show (case b of MkBoxed x -> x == 3) ++ show ((1 :: Int) == 1)",
      "main = leak (MkBoxed 3)",
      "",
    ].join("\n"),
    expect: "TrueTrue",
  },
  {
    // `@T` picks a quantified variable by position, so the signature's variable
    // list has to be the one the *source* wrote. `Eq c => Box c p -> [Char]`
    // used to list `c` twice (once from the type, once from the context) and
    // `quantify` kept the last index, so `@Int` landed on a gen nothing used
    // and `Eq c` stayed on an unsolved variable. `c` is phantom here, so the
    // application is the only thing that can decide it: without the fix this
    // does not compile at all.
    name: "type application: `@T` binds the variable the context named",
    source: [
      "module Main where",
      "data Box c p = MkBox p",
      "onlyEq :: Eq c => Box c p -> [Char]",
      "onlyEq (MkBox _) = \"eq\"",
      "class Tag c where tag :: Box c p -> [Char]",
      "instance Tag Int where tag _ = \"int\"",
      "instance Tag Bool where tag _ = \"bool\"",
      "main = onlyEq @Int (MkBox 'x') ++ tag @Bool (MkBox 'x') ++ tag @Int (MkBox 'x')",
      "",
    ].join("\n"),
    expect: "eqboolint",
  },
  {
    // The parser emits one `LocalBinding` per equation, so a multi-clause
    // `where` function used to lose every clause but the last: `go Nothing`
    // was dead code and `f Nothing` fell into the `Just` clause's
    // pattern-match failure. Silent, and wrong-answer rather than an error.
    name: "local bindings: a `where` function keeps all its equations",
    source: [
      "module Main where",
      "f :: Maybe Char -> [Char]",
      "f m = go m",
      "  where",
      "    go Nothing = \"ab\"",
      "    go (Just c) = [c, c]",
      "main = f Nothing ++ f (Just 'z')",
      "",
    ].join("\n"),
    expect: "abzz",
  },
  {
    // ... and the clauses share one type, so an overloaded `pure` in the first
    // is resolved by the second pinning the list. Inferred per clause, the
    // first one's `Applicative` had nothing to solve it at.
    name: "local bindings: a `where` function's equations share one type",
    source: [
      "module Main where",
      "f :: Maybe Char -> [Char]",
      "f m = go m",
      "  where",
      "    go Nothing = pure 'a'",
      "    go (Just c) = [c, c]",
      "main = f Nothing ++ f (Just 'z')",
      "",
    ].join("\n"),
    expect: "azz",
  },
  {
    // `kidsViews` enters `go`'s scope as a bare variable and only becomes a
    // list once `reverse kidsViews` is inferred. Generalisation used to work
    // from a snapshot of the enclosing scope's *variables*, taken before that
    // happened, so `ordered` was generalised over its element type and
    // `consume (map snd ordered)` wanted `ToObj` at a variable that no later
    // use could pin down. miso's `setField "nextSibling"` is this exact shape.
    name: "local bindings: a `let` does not generalise the scope's own type",
    source: [
      "module Main where",
      "class ToObj a where toObj :: a -> [Char]",
      "instance ToObj Char where toObj c = [c]",
      "build :: [Char]",
      "build = go (foldl buildKid [] ['x', 'y'])",
      "  where",
      "    buildKid acc k = (k, 'z') : acc",
      "    go kidsViews =",
      "      let ordered = reverse kidsViews",
      "      in consume (map snd ordered)",
      "      where",
      "        consume xs = concatMap toObj xs",
      "main = build",
      "",
    ].join("\n"),
    expect: "zz",
  },
  {
    // The monomorphism restriction. `maxAttempts = 20` owes only `Num a`, and
    // that constraint arrives as a *literal* use, which the generalisation
    // filter did not look at - so `a` was quantified and `n < maxAttempts` and
    // `show maxAttempts` each got their own copy, leaving the `Show` at a
    // variable nothing pinned. miso's `sendReadyUntilAcked` is this verbatim.
    name: "local bindings: a numeric literal binding stays monomorphic",
    source: [
      "module Main where",
      "f :: [Char]",
      "f = go (0 :: Int)",
      "  where",
      "    maxAttempts = 20",
      "    go n = if n < maxAttempts then go (n + 1) else show maxAttempts",
      "main = f",
      "",
    ].join("\n"),
    expect: "20",
  },
  {
    // A pattern signature's variables scope over the alternative's body, so
    // `parse "x" :: m` names the `m` the pattern matched. The annotation used
    // to be parsed and thrown away, leaving `m` fresh and both classes wanted
    // at a variable nothing could solve - miso's `componentListener` decodes
    // its model through exactly this.
    name: "pattern signature: its type variables scope over the body",
    source: [
      "module Main where",
      "class Parse a where parse :: [Char] -> a",
      "class Render a where render :: a -> [Char]",
      "instance Parse Int where parse _ = 7",
      "instance Render Int where render n = show n",
      "data Comp m = MkComp m",
      "run :: Comp Int -> [Char]",
      "run c = case c of",
      "  (_ :: Comp m) -> render (parse \"x\" :: m)",
      "main = run (MkComp 1)",
      "",
    ].join("\n"),
    expect: "7",
  },
  {
    // A `Bool` has no tag word: `tagToEnum#` and a nullary `True`/`False` both
    // produce a raw JS boolean, so codegen may only compile a `Bool` case to a
    // truthiness test - never to a switch on `x.f.a`. It gets that right for
    // two DataAlts, which is all `if` and guards ever produce. A source-level
    // `case` with a wildcard reaches it as `[DEFAULT, True]` instead, and the
    // tag switch then read `.f` off `true`. GHC never gets there because
    // `refineDefaultAlt` turns that DEFAULT into `False` first; the desugarer
    // now does too. miso's `initialize` dies on exactly this shape:
    // `case (live, maybeKey) of (True, Just k) -> ...; _ -> ...`.
    name: "a wildcard Bool alternative is refined to the missing constructor",
    source: [
      "module Main where",
      "pick :: Bool -> Int",
      "pick b = case b of",
      "  True -> 1",
      "  _ -> 2",
      // The pair scrutinee is miso's own shape: the `Bool` reaches the inner
      // case as a constructor field, not as a freshly compared value.
      "both :: Bool -> Maybe Int -> Int",
      "both b m = case (b, m) of",
      "  (True, Just n) -> n",
      "  _ -> 0",
      "main = pick (3 < (4 :: Int)) + pick (5 < (4 :: Int)) + both True (Just 39) + both False (Just 9)",
      "",
    ].join("\n"),
    expect: 42,
  },
];

const file = process.argv.slice(2).find((a) => !a.startsWith("--"));
/** A *directory* on the command line is the multi-module program; a file is
 * only itself. Pulling in the named file's whole directory - what this used to
 * do - silently merged every scratch `module Main` sitting beside it into one
 * program, so three unrelated files each reported the same wrong answer. */
const fromDisk = file
  ? (statSync(resolve(file)).isDirectory() ? await walk(resolve(file)) : [resolve(file)]).map((path) => ({
      file: path,
      source: readFileSync(path, "utf8"),
    }))
  : [];
const cases = file
  ? [{ name: file, sources: fromDisk, expect: undefined }]
  : programs.map((program) => ({
      ...program,
      sources: program.sources
        ? Object.entries(program.sources).map(([name, source]) => ({
            file: `${name}.hs`,
            source,
          }))
        : [{ file: `${program.name}.hs`, source: program.source }],
    }));

let failures = 0;
for (const program of cases) {
  let compiled;
  try {
    compiled = compile(program.sources, file ?? `${program.name}.hs`);
  } catch (cause) {
    console.log(`  FAIL  ${program.name}: ${cause instanceof Error ? cause.message : cause}`);
    failures++;
    continue;
  }
  for (const d of compiled.diagnostics) console.log(`        ${formatDiagnostic(d)}`);
  if (show) console.log(`--- ${program.name} (${compiled.symbol}) ---\n${compiled.emitted}\n`);
  const bigint = nativeBigInt(compiled.emitted);
  if (bigint) {
    console.log(`  FAIL  ${program.name}: emitted native BigInt syntax \`${bigint[0]}\`, which the target engine cannot load`);
    failures++;
    continue;
  }
  try {
    const result = run(compiled.emitted, compiled.symbol, program.probe, program.threaded || forceThreaded, compiled.wrapped);
    if (program.throws !== undefined) {
      console.log(`  FAIL  ${program.name}: expected a \`${program.throws}\` exception, got ${JSON.stringify(result)}`);
      failures++;
    } else if (program.expect === undefined) {
      console.log(`  ${program.name} => ${JSON.stringify(result)}`);
    } else if (result === program.expect) {
      console.log(`  ok    ${program.name} => ${result}`);
    } else {
      console.log(`  FAIL  ${program.name}: expected ${program.expect}, got ${JSON.stringify(result)}`);
      failures++;
    }
  } catch (cause) {
    const message = cause instanceof Error ? `${cause.name}: ${cause.message}` : String(cause);
    if (program.throws !== undefined && message.includes(program.throws)) {
      console.log(`  ok    ${program.name} => ${message}`);
    } else {
      console.log(`  FAIL  ${program.name}: ${message}`);
      failures++;
    }
  }
}

console.log(`\n${cases.length - failures}/${cases.length} Haskell programs compiled and ran`);
process.exit(failures ? 1 : 0);
