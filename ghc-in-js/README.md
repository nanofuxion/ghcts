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
$GHC/bin/javascript-unknown-ghcjs-ghc-9.12.2 -package ghc -O0 -o driver Driver.hs
node patch.mjs driver.jsexe/all.js driver-patched.js
node --stack-size=40000 driver-patched.js \
  $GHC/lib/javascript-unknown-ghcjs-ghc-9.12.2/lib Prog.hs
```

`patch.mjs` fixes two things the linked bundle needs on node:

1. The RTS reads `Module.HEAP8` for its Emscripten C shim; this Emscripten
   build does not put the heap views on `Module`.
2. The RTS's 64-bit helpers call `JSBI.*`, a polyfill nothing defines. Node
   has native BigInt, which is what JSBI wraps.

Both belong upstream in GHC's JS linker; neither touches code generation.

## Result

Compiling `main = putStrLn "hello"`:

| | JS-hosted GHC | native cross GHC |
| --- | --- | --- |
| time | 12.7 s | 1.5 s |
| `out.js` | 1,434,744 bytes | 1,434,744 bytes |

The two `out.js` files are identical once GHC's per-build local hash names are
masked. The produced bundle runs and prints its output.

The driver bundle is 276 MB (21 MB gzipped) at `-O0` with no dead-code pass.
