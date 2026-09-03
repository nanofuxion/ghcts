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

## The emscripten link failure, and why it is gone

Without `-ddisable-js-c-sources` both compilers fail identically at the very
end: `wasm-ld: error: section too large`, linking miso's `cbits/foreign.c`
through emscripten. That is the failure `scripts/ghc-lynx-oracle.mjs` works
around by salvaging the four files GHC had already written.

With the flag there is nothing to salvage: GHC skips the C step, writes
`runmain.js` from its non-emcc branch and combines the whole bundle itself.
misogram links to a complete 12,252,685-byte `all.js` in 46 s, `out.js`
still byte-identical to the native build, and it runs: 778 elements in
`scripts/lynx-run.mjs`, and `--swipe 84` moves the carousel to 2/3.

The three symbols the C file provided - `miso_x_store`, `miso_x_get`,
`miso_x_clear` - are GHCi live-reload only (`references/miso/src/Miso/
Reload.hs`) and appear nowhere in the linked bundle.

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

## On the device

Packed with `scripts/pack-lynx.mjs` and served as `host-lynx`'s
`misogram-ghc` route, the bundle GHC-in-JavaScript produced runs on a Pixel
under Lynx Explorer with no errors in logcat: splash, feed, stories, the
photo carousel, and tab navigation.

Same gestures, GHC's bundle against ghcts's, measured as the gap between
`Miso.effects` and `Miso.patches` in logcat:

| | GHC-in-JS bundle | ghcts bundle |
| --- | --- | --- |
| swipe -> carousel 1/3 to 2/3 | 4.5 s | 2.0 s |
| tab tap -> explore grid | 0.55 s | 0.29 s |

ghcts is about twice as fast here, at `-O0` on both sides; GHC's own `-O`
was not measured.
