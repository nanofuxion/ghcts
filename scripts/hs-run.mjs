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
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { walk } from "../dist/compiler.js";
import { renderRts } from "../dist/stg-js/rts.js";
import { renderStaticRts } from "../dist/stg-js/rts-static.js";
import { stgToJS, renderModule } from "../dist/stg-js/codegen.js";
import { defaultStgToJSConfig } from "../dist/stg-js/types.js";
import { parseModule } from "../dist/parser.js";
import { elaborateProgram } from "../dist/elaborate.js";
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
/** A program that forks, blocks or delays needs the RTS's own scheduler, not
 * the bare trampoline above: only a real h$Thread can be put on an MVar's
 * wait queue and woken again. h$forkThread + h$mainLoop is exactly what
 * h$main does, minus base's top handler and stdout flush - neither of which
 * exists here. The thread constructor names ghc-internal's reportError
 * closure, which a ghcts program does not link, so it is stubbed. */
var h$ghczminternalZCGHCziInternalziConcziSynczireportError = null;
/** h$forkThread starts a thread with h$ap_1_0, which applies its closure to
 * one void argument - right for GHC's main, whose type is State# -> (# #),
 * and wrong for this frontend's, which runMainIO has already reduced to a
 * plain thunk. So the start frame here simply ENTERS the closure. */
function h$enterFrame() {
  h$r1 = h$stack[h$sp - 1];
  h$sp -= 2;
  return h$r1.f;
}
h$enterFrame.f = h$enterFrame;
h$o(h$enterFrame, -1, 0, 0, 0, null);
function h$runThreaded(c) {
  var t = new h$Thread();
  t.stack[4] = c;
  t.stack[5] = h$enterFrame;
  t.sp = 5;
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
    diagnostics: [...elaborated.diagnostics, ...desugared.diagnostics],
  };
}

/** `probe` is a JS expression read *after* the program has run, which is the
 * only way to observe an `IO ()`: its value carries nothing, so the proof that
 * it ran has to come from the effect it had. Property order in the object
 * literal is what sequences the two. */
function run(emitted, symbol, probe, threaded) {
  const enter = threaded
    ? `h$runThreaded(${symbol})`
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
];

const file = process.argv.slice(2).find((a) => !a.startsWith("--"));
/** A file on the command line brings its whole directory with it, so a
 * multi-module program on disk compiles the same way the inline cases do. */
const fromDisk = file
  ? (await walk(dirname(resolve(file)))).map((path) => ({
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
  try {
    const result = run(compiled.emitted, compiled.symbol, program.probe, program.threaded || forceThreaded);
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
