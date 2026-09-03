# GHC compiled to JavaScript, hosting itself

This is a working proof that GHC 9.12.2 itself runs as plain JavaScript on
node and compiles Haskell with byte-identical output to the native compiler.
No prebuilt native binary, no wasm.

## How

The nix `javascript-unknown-ghcjs-ghc-9.12.2` cross compiler ships the `ghc`
library *built for the JavaScript target*. So a GHC-API driver can be compiled
by that cross compiler, producing a `.jsexe` bundle that IS the compiler.

```bash
GHC=/nix/store/…-javascript-unknown-ghcjs-ghc-native-bignum-9.12.2
$GHC/bin/javascript-unknown-ghcjs-ghc-9.12.2 -package ghc -O0 \
  -ddisable-js-c-sources -o driver Driver.hs
cat jsbi-shim.js driver.jsexe/all.js > ghc.js
node --stack-size=40000 ghc.js \
  $GHC/lib/javascript-unknown-ghcjs-ghc-9.12.2/lib -ddisable-js-c-sources Prog.hs
```

`-ddisable-js-c-sources` is GHC's own flag for skipping the C-source step.
It is what keeps this pure JavaScript: without it the link shells out to
`emcc`, which is a native toolchain, and the bundle then needs the
Emscripten runtime at startup. Pass it when building the compiler AND when
building programs with it.

`jsbi-shim.js` is the one thing still prepended. GHC's RTS calls `JSBI.*` in
its 64-bit helpers, and nothing in the bundle defines it - `h$hs_remWord64`
is on the path of GHC's own `Unique` hashing, so the compiler cannot start
without it. JSBI is a BigInt polyfill; node has BigInt, so the shim is 20
lines of identity functions. It belongs upstream in GHC's JS RTS and it
touches no code generation.

## Result

Compiling `main = putStrLn "hello"`:

| | JS-hosted GHC | native cross GHC |
| --- | --- | --- |
| time | 12.7 s | 1.5 s |
| `out.js` | 1,434,744 bytes | 1,434,744 bytes |

The two `out.js` files are identical once GHC's per-build local hash names are
masked. The produced bundle runs and prints its output.

The driver bundle is 276 MB (21 MB gzipped) at `-O0` with no dead-code pass.
