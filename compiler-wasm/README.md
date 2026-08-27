# npm compiler experiment

This directory is an isolated experiment for a distributable Haskell-to-JavaScript
compiler.

## Working hypothesis

Build the smallest GHC/GHCJS compiler driver that preserves GHCJS's generated
JavaScript conventions, compile that driver to `wasm32-wasi`, and optionally
lower the resulting compiler artifact with Binaryen's `wasm2js` for runtimes
where executing WebAssembly directly is not available.

The target distribution is an npm package. The package should eventually expose
an API that accepts Haskell source and returns the same class of JavaScript
artifacts expected by the existing `counter` and `misogram` fixtures.

The terms "JS compiler" and "WASI compiler" refer to different roles here:
the extracted compiler targets JavaScript for its users; WASI is only the host
target used to package/run that compiler inside npm.

## Important boundary

`wasm2js` is a deployment step for the compiler executable. It is not the
Haskell-to-TypeScript or Haskell-to-JavaScript backend. The GHCJS `Gen2` code
generator and linker remain responsible for the emitted JavaScript shape.

## Initial extraction boundary

Keep these areas together until a passing probe proves they can be removed:

- GHC's driver, parser, typechecker, Core/STG pipeline, and package handling;
- GHCJS `Compiler.GhcjsHooks` and `Compiler.GhcjsProgram`;
- GHCJS `Gen2.Generator`, `Gen2.Linker`, `Gen2.Printer`, runtime support, and
  foreign-export handling;
- the minimum boot libraries/runtime data required by the generated output.

Exclude from the first probe: `ghcjs-boot`, Haddock, package installation, the
optimizer, Template Haskell, profiling, threaded runtime support, and native
foreign libraries. Reintroduce each only after the minimal compiler can compile
the fixtures.

## Findings so far

- `references/ghcjs` is version 8.10.7 and its Cabal package builds a GHCJS
  library plus several executables; it is not a standalone JavaScript compiler
  module.
- The installed host GHC is 9.6.7, so a direct build will likely require the
  matching GHCJS-era toolchain or a port to the current GHC API.
- Binaryen's `wasm2js` should be evaluated as the canonical lowering tool. The
  npm package `thlorenz/wasm2js` is a CommonJS wrapper around a Wasm binary, not
  the Binaryen instruction-to-JavaScript compiler.
- The local Emscripten installation provides Binaryen's `wasm2js` at
  `/opt/homebrew/Cellar/emscripten/4.0.23/libexec/binaryen/bin/wasm2js`.
- A no-libc `wasm32-wasip1` probe converted successfully to JavaScript. A normal
  WASI link currently fails because the local Clang installation has no WASI
  sysroot (`crt1.o`, libc, and compiler builtins). This makes a libc-free first
  compiler probe a useful constraint, not evidence that the full compiler is
  already buildable.

## Validation order

1. Build and run a native minimal driver.
2. Compile the driver to WASI and run it under a TypeScript/Node WASI host.
3. Lower the same artifact with Binaryen `wasm2js` and run the generated JS.
4. Compare generated output and runtime behavior against the checked-in
   `counter` and `misogram` expectations.
