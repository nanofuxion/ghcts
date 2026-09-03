# GHC in the browser

The compiler runs unchanged. It is the same `dist/ghc.cjs` the CLI uses; the
page only supplies the four node modules GHC's runtime asks `require` for at
startup, and a filesystem built out of `Uint8Array`s.

```bash
node build/build-compiler.mjs        # dist/ghc.cjs and dist/lib
node playground/pack-assets.mjs --minimal
ln -s ../dist/ghc.cjs playground/ghc.cjs
npx serve playground                 # any static server
```

Compiling and running a ten-primes program takes about 15 s in Chrome.

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

## Opening your own folder

"Open a folder…" uses the File System Access API, so a real project directory
mounts at `/project` and compiles the way it would on disk. Chrome and Edge
have it; Firefox and Safari do not, and the picker says so.

Writing results back to the folder is not wired up yet: the compiler's output
lands in the virtual filesystem, and only what the page displays comes out.

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
| `assets/lib.bin` (`--minimal`) | 79 MB |

Serve both with `Content-Encoding: gzip` and a long cache. Neither has been
shrunk yet: the compiler is linked at `-O0` with no dead-code pass, and the
library blob keeps every module of every boot package.
