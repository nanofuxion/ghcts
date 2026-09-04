# GHC in the browser

The compiler runs unchanged. It is the same `dist/ghc.cjs` the CLI uses; the
page only supplies the four node modules GHC's runtime asks `require` for at
startup, and a filesystem built out of `Uint8Array`s.

```bash
node build/build-compiler.mjs        # dist/ghc.cjs and dist/lib
node playground/pack-assets.mjs --minimal   # also copies ghc.cjs into assets/
npx serve playground                 # any static server
```

The packer copies the compiler rather than linking it: a static server that
will not follow a symlink out of its root answers 404, and the page would
then evaluate the error document as JavaScript. If anything fails to load,
the status line names the URL and its status.

Both `assets/ghc.cjs` (276 MB) and `assets/lib.bin` (79 MB) are worth serving
precompressed with a long cache. Content types do not matter: the page
fetches them as bytes.

Compiling and running a ten-primes program takes about 15 s in Chrome.

## The file tree

The left panel is the VFS, not a separate model: `project.mjs`'s
`mountDirectory`/`findEntry` and the tree renderer all read and write the same
`Vfs` the compiler runs over, so a compiled program's `.jsexe/` output shows
up right there next to its source. Click a directory row to collapse or
expand it, click a file to open it in the editor, and the ☰ button hides the
whole panel. Switching files (or compiling) saves the one currently open back
into the VFS first, so nothing written is lost by looking somewhere else.

## Opening a folder

"Open a folder…" uses the File System Access API (Chrome and Edge; Firefox
and Safari do not have it, and the button says so). Every file mounts into
the VFS at `/project`, and files opened from there also keep their real
`FileSystemFileHandle` — an edit is written back to both the VFS and the
actual file on disk, best-effort, whenever you switch away from it or compile.

The entry point is not assumed to be `Main.hs` at the root. `project.mjs`
looks for a `.cabal` file and reads its first runnable stanza's `main-is` and
`hs-source-dirs` - the standard Haskell project config - then falls back to
this repo's own `ghcts.json` shape, then to the conventional `Main.hs` /
`app/Main.hs` / `src/Main.hs` paths. A `.cabal` file's `build-depends` also
decides whether the miso package database gets fetched, the same as picking
the miso template does. None of this is a full Cabal parser - conditional
`if`/`else` stanzas are not descended into - but it reads every real `.cabal`
file this repo ships (`references/miso/sample-app/app.cabal`,
`references/misogram/miso-gram.cabal`) correctly; see `test/project.test.mjs`,
which is also the honest way to check "does opening a folder work" at all -
there is no way to script a browser's own native folder picker.

## miso, in the same page

Picking "miso" from the template menu - or opening a folder whose `.cabal`
depends on `miso` - fetches a second, separate blob (`assets/miso.bin`) the
first time it is needed, and adds `-package-db /lib/pkgs/package.conf.d
-package miso` to the compile. The result does not print to the log: it loads
into the `<iframe>` below it, on a blank page with a `<div id="app">`, exactly
what `startApp ... { mountPoint = Just "app" }` expects. The iframe is not
sandboxed, so its own uncaught errors get posted back into the compile log
above it.

`assets/miso.bin` is `dist/pkgs` (built by `node build/miso-web/build.mjs` -
see `build/miso-web/README.md`) plus whatever extra boot packages miso's own
closure needs beyond the Prelude's minimal set (`bytestring`, `containers`,
`mtl`, `text`, and the rest `pack-assets.mjs --miso` works out from
`dist/pkgs`'s own `depends:` fields, not a hand-kept list).

## How it works

`vfs.mjs` is a tree of directories and files with node's `fs` shape over it —
28 functions, which is everything GHC's runtime uses. Files can be *lazy*: the
boot libraries arrive as one 79 MB blob plus an index, and a file is only
decoded when GHC opens it.

`host.mjs` runs the compiler with that filesystem in place of node's. GHC
decides it is on node by looking for `global`, `process`, `require` and
`module`; give it those and it never asks where the files really are. The same
function is what the node-side test uses, backed by real files, which is how
the shim is checked.

## What the browser needed that node did not

Four things, all in `host.mjs`, none of them touching the compiler:

- **`process.binding('constants')`** — a private node table the runtime reads
  for file modes and errno. Captured into `constants.mjs`.
- **`Buffer.alloc`** — the runtime's staging buffer for reads and writes. A
  `Uint8Array` is all it needs.
- **posix stubs** — `geteuid`, `sysconf`, `getpwuid_r` and friends come from a
  C shim that `-ddisable-js-c-sources` leaves out. Node never reaches them
  because it has a real `HOME` and real processors.
- **an exit that exits** — GHC's shutdown calls `process.exit` and expects
  never to return. Here it throws a sentinel that every callback we hand the
  runtime swallows; without it GHC reports "shutdownHaskellAndExit did not
  exit" and keeps going forever.

## Size

| | |
| --- | --- |
| `ghc.cjs` | 276 MB, ~21 MB gzipped |
| `assets/lib.bin` (`--minimal`) | 79 MB, always fetched |
| `assets/miso.bin` | ~120 MB, fetched only for a miso program |

Serve both with `Content-Encoding: gzip` and a long cache. Neither has been
shrunk yet: the compiler is linked at `-O0` with no dead-code pass, and the
library blob keeps every module of every boot package.

`pack-assets.mjs` splits each of these into 20 MiB chunks (`ghc.cjs.0`,
`ghc.cjs.1`, … plus `ghc.cjs.chunks.json` naming the count); the page
refetches and reassembles them before use. This is for Cloudflare Pages,
which refuses any single deployed file over 25 MiB - the whole `playground/`
directory, `assets/` included, can be pointed at directly as its build
output.
