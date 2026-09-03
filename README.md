# ghc-js

GHC's JavaScript backend, as a JavaScript program.

The compiler here is GHC itself. GHC's compiler library is compiled to
JavaScript by GHC's own JavaScript backend and driven through the GHC API, so
its output is byte-identical to a native `javascript-unknown-ghcjs-ghc`
cross compiler's — not similar, identical. There is no port to keep in sync.

Nothing at run time needs Haskell, nix, or a native toolchain. Node runs it.

```bash
npm install ghc-js

ghc-js Main.hs                    # compile and link to Main.jsexe
node Main.jsexe/all.js

ghc-js -O2 -o app Main.hs
ghc-js -c Foo.hs Bar.hs           # compile only
GHC_PACKAGE_PATH=db1:db2 ghc-js -isrc Main.hs
```

Every GHC flag passes straight through. Two are our own:
`--ghc-js-version` and `--ghc-js-libdir <dir>`.

## As a library

```ts
import { compile } from "ghc-js";

const result = await compile({ args: ["-O2", "Main.hs"], packageDbs: [db] });
if (!result.ok) process.exit(result.code);
```

## What is in here

| | |
| --- | --- |
| `src/` | the CLI and its library API, TypeScript |
| `build/` | the pipeline that produces the compiler, and the ~40-line GHC-API driver it compiles |
| `playground/` | the same compiler in a browser, over a filesystem made of `Uint8Array`s |
| `scripts/` | Lynx helpers: pack a bundle, serve it, drive it headless |

`node build/build-compiler.mjs` turns a GHC JavaScript-target installation
into `dist/ghc.cjs` (the compiler, 276 MB at `-O0`) and `dist/lib` (the boot
libraries a compiled program needs, 147 MB). Run it once per GHC version.
See `build/README.md`.

## In a browser

`playground/` runs the same `ghc.cjs` in a page: it supplies the four node
modules GHC's runtime asks for and a virtual filesystem, and the compiler
never knows the difference. Compiling and running a small program takes about
15 seconds in Chrome. "Open a folder…" mounts a real project directory through
the File System Access API. See `playground/README.md`.

## Two things worth knowing

`-ddisable-js-c-sources` is passed by default. Without it GHC links a
package's C sources with `emcc`, which is a native toolchain, and on some
packages it fails outright. The flag is what keeps this pure JavaScript.

The compiler bundle is `.cjs`, not `.js`. GHC's runtime finds node through
`require` and `module`; loaded as an ES module it starts with no arguments
and no filesystem.

## Verified against real code

`ghc-in-js/MISOGRAM.md` records this compiler building misogram — 1,632 lines
over miso, ghcjs-base and aeson — to an `out.js` matching the native build
byte for byte, and that bundle running on an Android device.
