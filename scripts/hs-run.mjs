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

function run(emitted, symbol) {
  // Indirect eval so the RTS's top-level `var h$...` land on globalThis.
  const entry = (0, eval)(
    `${rts}\n${bootstrap}\n${emitted}\n(function(){ h$initStatic.forEach(function(f){f();}); h$initStatic.length = 0;` +
      ` return { value: h$runEntry(function(){ h$r1 = ${symbol}; return h$r1.f; }), force: h$forceClosure }; })`,
  );
  const { value, force } = entry();
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
    const result = run(compiled.emitted, compiled.symbol);
    if (program.expect === undefined) {
      console.log(`  ${program.name} => ${JSON.stringify(result)}`);
    } else if (result === program.expect) {
      console.log(`  ok    ${program.name} => ${result}`);
    } else {
      console.log(`  FAIL  ${program.name}: expected ${program.expect}, got ${JSON.stringify(result)}`);
      failures++;
    }
  } catch (cause) {
    console.log(`  FAIL  ${program.name}: ${cause instanceof Error ? `${cause.name}: ${cause.message}` : cause}`);
    failures++;
  }
}

console.log(`\n${cases.length - failures}/${cases.length} Haskell programs compiled and ran`);
process.exit(failures ? 1 : 0);
