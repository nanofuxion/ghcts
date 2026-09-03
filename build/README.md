# Building the compiler

`node build/build-compiler.mjs` turns a GHC JavaScript-target installation
into `dist/ghc.js` — GHC itself, as one JavaScript file — plus the trimmed
`dist/lib/` a compiled program needs.

It is a build-time step, run once per GHC version. Nothing at runtime needs
Haskell, nix, or a native toolchain.

## Inputs

A `javascript-unknown-ghcjs-ghc` installation whose package database contains
the `ghc` library. That is what makes this possible: GHC's own compiler
library, already compiled for the JavaScript target, so a driver written
against the GHC API links into a JavaScript bundle that *is* GHC.

The script finds one in the nix store, or takes `--ghc <path-to-bin>`.

## Steps

1. Compile `Driver.hs` — GHC's driver, ~30 lines against the GHC API — with
   the JS-target compiler and `-ddisable-js-c-sources`.
2. Prepend `jsbi-shim.js`. GHC's RTS names a `JSBI` polyfill nothing defines,
   and `h$hs_remWord64` sits on the path of GHC's own `Unique` hashing, so the
   compiler cannot start without it. Node has BigInt, which is what JSBI
   wraps.
3. Copy the boot packages a compiled program needs into `dist/lib/`, leaving
   out `ghc`, `Cabal` and `haddock` (needed to build the compiler, never to
   run it) and the profiling and debug ways. 2.7 GB becomes ~130 MB.

## Why -ddisable-js-c-sources

Without it GHC's linker shells out to `emcc` for a package's C sources. That
is a native toolchain, and on miso it fails outright (`wasm-ld: section too
large`). With it the link is pure JavaScript and complete.
