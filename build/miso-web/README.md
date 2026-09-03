# miso, for the browser

`node build/miso-web/build.mjs` builds [miso](https://github.com/dmjio/miso)
the way a page renders it — through the DOM, not through Lynx — and collects
it into a relocatable package database the playground can fetch.

```bash
node build/miso-web/build.mjs
node playground/pack-assets.mjs --miso
```

## Why this is a separate build

`references/miso`'s own `cabal.project` asks for `+native`: LynxJS, phones,
`scripts/build-lynx-bundles.mjs`. Listing it as a package here instead, with
no `flags:` line, gets the default build — the DOM backend, `js/miso.js`,
`ffi/js` — same source, different package. Only miso and ghcjs-base are
rebuilt; the cabal store already has aeson, vector and the rest of
ghcjs-base's dependencies from an earlier native build against the same
compiler, and this reuses them rather than rebuilding.

`ghcjs-base` at the revision miso pins does not build under GHC 9.12 —
`ghcjs-base-ghc912.patch` is the fix, recorded first in
`ghc-in-js/MISOGRAM.md`. `build.mjs` clones it fresh into a gitignored
`ghcjs-base/` and applies the patch; nothing is vendored.

## What it produces

`build/build-packages.mjs` walks miso's dependency closure across the
inplace database this build leaves under `dist-newstyle/` and the cabal
store, copies each non-boot package's files into `dist/pkgs/<id>/lib`, and
rewrites every `.conf`'s absolute paths to `${pkgroot}`-relative ones — the
same shape `dist/lib`'s own confs already use, so the tree works both on
disk and mounted at `/lib/pkgs` in the playground's virtual filesystem. Boot
packages (bytestring, containers, mtl, text…) are left out here; they are
already in `dist/lib`, and `pack-assets.mjs --miso` works out which of them
miso's closure actually needs by reading `depends:` out of the copied confs,
rather than from a hand-kept list.

## Requirements

The compiler must be the exact one that built `dist/lib` — `build.mjs`
checks this and refuses otherwise, the same way `build/build-compiler.mjs`
does. miso's `cbits/foreign.c` is still compiled (not linked — see
`-ddisable-js-c-sources` in `build/README.md`) with whatever C compiler that
install's `settings` names, so this is only verified working with the
compiler `dist/lib` itself came from.
