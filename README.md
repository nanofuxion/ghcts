# ghcts

GHC's JavaScript backend, as a JavaScript program.

The compiler here is GHC itself. GHC's compiler library is compiled to
JavaScript by GHC's own JavaScript backend and driven through the GHC API, so
its output is byte-identical to a native `javascript-unknown-ghcjs-ghc`
cross compiler's — not similar, identical. There is no port to keep in sync.

Nothing at run time needs Haskell, nix, or a native toolchain. Node runs it.

```bash
npm install ghcts

ghcts Main.hs                    # compile and link to Main.jsexe
node Main.jsexe/all.js

ghcts -O2 -o app Main.hs
ghcts -c Foo.hs Bar.hs           # compile only
GHC_PACKAGE_PATH=db1:db2 ghcts -isrc Main.hs
```

Every GHC flag passes straight through. Three are our own:
`--ghcts-version`, `--ghcts-libdir <dir>` and `--ghcts-project [dir]`.

## Building a project's dependencies

```bash
ghcts --ghcts-project . -o app
```

Project mode reads the directory's `.cabal` and `cabal.project`, and takes
each dependency the project pins to a git revision.

A pin that is already built is not built again. `dist/pkgs-<revision>` is
used when it is that revision, and the ordinary `dist/pkgs` otherwise:
compiling a library takes tens of minutes, and a version mismatch says so in
seconds. `haskell-miso/mario` builds in 74 seconds this way, `flatris` in 52.

A pin nothing has is fetched and compiled with the program - one `--make` run
over both, with the flags each `.cabal` asks for, into `dist-ghcts/`. The
second build only redoes what changed, because GHC's own recompilation
checking is the cache.

That is the dependency that varies between projects. `miso` is pinned by
revision in every app in the haskell-miso organisation, and each app wants a
different one. A pinned package's *own* dependencies are ordinary Hackage
packages, which do not vary, and those come from the package database beside
the compiler. Nothing is fetched from Hackage: resolving and building that is
cabal's job, and `cabal build --with-compiler` is the way to have it.

The `.cabal` reading is real enough for real files: `common` blocks and the
`import:` that pulls them in, and `if`/`elif`/`else` resolved against this
compiler rather than collected from every branch at once. The browser uses
the same module - `npm run build` copies it to `playground/cabal.js`, since a
page can only load what is served under `playground/`.

## As a library

```ts
import { compile } from "ghcts";

const result = await compile({ args: ["-O2", "Main.hs"], packageDbs: [db] });
if (!result.ok) process.exit(result.code);
```

## What is in here

| | |
| --- | --- |
| `src/` | the CLI, its `.cabal` reader and project builder, and the library API |
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
15 seconds in Chrome. A collapsible file tree on the left edits whatever is
mounted; "Open a folder…" mounts a real project through the File System
Access API, and a `github.com/owner/repo` link in the header loads one
straight off GitHub with no server in between. Either way its `.cabal` file
says where the program starts. Packages beyond the Prelude - `random`,
`containers`, `miso` - are fetched and exposed by themselves, going by what
the sources import and what a `.cabal` asks for. A program that needs `miso`
renders into the pane on the right rather than printing to a log; a console
program that calls `getLine` gets an input box. Template Haskell works too:
GHC's interpreter runs in a second global in the same page rather than in a
node subprocess. See `playground/README.md`.

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
