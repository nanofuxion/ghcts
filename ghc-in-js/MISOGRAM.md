# Compiling misogram with GHC-in-JavaScript

misogram is 1,632 lines of Haskell over miso, ghcjs-base and aeson — the
largest real program in this repo. GHC running as JavaScript compiles it,
and its output matches the native compiler's exactly.

## Result

| | GHC on node | native cross GHC |
| --- | --- | --- |
| time (misogram's own 6 modules) | 43.2 s | ~4 s |
| `out.js` | 11,085,834 bytes | 11,085,834 bytes |
| `lib.js`, `out.frefs.js` | identical | identical |
| `rts.js` | identical | identical |

`rts.js` matches once its fresh loop-variable names (`h$RTS_joHt` against
`h$RTS_j34J`) are normalised. `out.js` is identical once two per-build values
are normalised: GHC's
linker-local `h$$…` names, and the `StaticPtr` keys (a hash of the compiling
unit's ABI, different between any two separate builds of the same source).
20,700 functions and 260,454 lines either way.

Both compilers then fail the same way at the very end, in emscripten:
`wasm-ld: section too large`, linking `references/miso/cbits/foreign.c`.
That is the known miso-native C-stub failure `scripts/ghc-lynx-oracle.mjs`
already documents and works around; it happens after GHC has written the JS
it generates, and it is not specific to the JavaScript-hosted compiler.

## How

Dependencies (aeson, ghcjs-base, miso) are built once with the native cross
compiler, because cabal itself is not part of this experiment:

```bash
cd misogram-project        # misogram-cabal.project, adjusted for your paths
cabal build                # builds aeson, ghcjs-base, miso; misogram's own
                           # link then hits the emscripten failure above
```

Then compile misogram's own modules with GHC-in-JavaScript, against the
package databases cabal produced:

```bash
export GHC_PACKAGE_PATH=<dist-newstyle/packagedb/ghc-9.12.2>:<cabal store db>:<ghc lib package.conf.d>
node --stack-size=40000 driver-patched.js <ghc libdir> \
  -O0 -XHaskell2010 -this-unit-id miso-gram-0.1.0.0-inplace-miso-gram \
  -package-id base-4.21.0.0-6329 -package-id containers-0.7-f66e \
  -package-id miso-1.13.0.0-inplace -package-id mtl-2.3.1-a405 \
  -isrc -outputdir out -o out/miso-gram src/Main.hs
```

`-this-unit-id` must be the one cabal used, or every symbol carries a
different package prefix and nothing lines up.

Package databases have to arrive through `GHC_PACKAGE_PATH`; a `-package-db`
flag reached the JS-hosted driver with the rest of the command line glued
onto it.

## ghcjs-base needed one port fix

`GHCJS/Internal/Types.hs` does not build under GHC 9.12: `type Mutable =
Mutable_ ()` means the promoted unit, and the `Mutability` family's equations
must match on constructors now that its kind variable is generalised.

```haskell
type Mutable   = Mutable_ '()
type Immutable = Immutable_ '()

type family Mutability (a :: MutabilityType s) :: IsItMutable where
  Mutability (Immutable_ x) = IsImmutable
  Mutability (Mutable_ x)   = IsMutable
  Mutability (STMutable s)  = IsMutable
```

`cabal_macros.h` here supplies the `MIN_VERSION_*` macros ghcjs-base expects
for packages that are not in this build.
