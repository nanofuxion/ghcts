# Building the compiler

`node build/build-compiler.mjs` turns a GHC JavaScript-target installation
into `dist/ghc.cjs` — GHC itself, as one JavaScript file — plus the trimmed
`dist/lib/` a compiled program needs.

It is a build-time step, run once per GHC version. Nothing at runtime needs
Haskell, nix, or a native toolchain.

## Inputs

A `javascript-unknown-ghcjs-ghc` installation whose package database contains
the `ghc` library. That is what makes this possible: GHC's own compiler
library, already compiled for the JavaScript target, so a driver written
against the GHC API links into a JavaScript bundle that *is* GHC.

It is found the way its own users install one: `GHCTS_GHC` if set, then
`PATH`, then ghcup. `--ghc <binary|bindir>` overrides all three. Whichever is
found is asked for its own `--print-libdir` and `--numeric-version`.

## Steps

1. Compile `Driver.hs` — GHC's driver, ~30 lines against the GHC API — with
   the JS-target compiler and `-ddisable-js-c-sources`.
2. Prepend `jsbi-shim.js`. GHC's RTS names a `JSBI` polyfill nothing defines,
   and `h$hs_remWord64` sits on the path of GHC's own `Unique` hashing, so the
   compiler cannot start without it. Node has BigInt, which is what JSBI
   wraps.
3. Copy the boot packages a compiled program needs into `dist/lib/`, leaving
   out `ghc`, `Cabal` and `haddock` (needed to build the compiler, never to
   run it) and the profiling and debug ways. 2.7 GB becomes ~140 MB.
   `ghc-heap` stays: `ghci` depends on it, and `ghci` is what runs a Template
   Haskell splice.

`dist/ghc.cjs` is always linked with a *native* GHC that already targets
JavaScript - never with itself. `findGhcJs()`/`ghcInstallAt()` only ever look
at `GHCTS_GHC`, `PATH` and ghcup, so there is nothing on that search path to
self-host with; a compiled bundle is `.cjs`, and the script refuses one.

`--lib-only` skips step 1 and reuses the existing `dist/ghc.cjs`, but still
resolves an install fresh for step 3 - a PATH or ghcup default can change
between two runs. `dist/.ghcts-compiler.json` records which install built
`ghc.cjs` last, and `--lib-only` refuses to pair its libraries with a
*different* one rather than silently mixing versions.

## Why -ddisable-js-c-sources

Without it GHC's linker shells out to `emcc` for a package's C sources. That
is a native toolchain, and on miso it fails outright (`wasm-ld: section too
large`). With it the link is pure JavaScript and complete.
