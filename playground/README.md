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

## Typing at a program

A console program that calls `getLine` gets a one-line input box under the
log, and what you type is echoed there the way a terminal would. `makeStdin`
in `host.mjs` is the whole of it: `read()` plus a `readable` event is all
GHC's RTS ever asks of `process.stdin`. That run also reports `isTTY: true`,
because GHC's handles read it to choose their buffering - block-buffered
output would sit unseen until the program ended, long after it asked you a
question.

## Loading a repository

Paste `github.com/owner/repo` into the box in the header and press Enter.
There is no server of ours in this page, and none in this either: the tree
API says what is in the repository and raw.githubusercontent.com serves the
files, and both allow cross-origin reads. Only sources and the files that
describe the build are taken - `.hs`, `.cabal`, `cabal.project` - so a repo
full of screenshots costs nothing. `/tree/<branch>` and a subdirectory in the
URL both work.

The tree API is the rate-limited half, at 60 listings an hour from an
address with no token, so it is asked once per repository and the files are
not. A preview of a repo's app also gets a `<base>` pointing back at
raw.githubusercontent.com, which is how `assets/mario.png` in a stylesheet
finds its sprite.

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
`app/Main.hs` / `src/Main.hs` paths. `default-language` and `default-extensions` are passed
on as `-X` flags, which is what cabal would otherwise be doing. A `.cabal`
file's `build-depends` is also one of
the two things that decide which extra packages get fetched and exposed - see
below; the other is what the sources actually import. None of this is a full Cabal parser - conditional
`if`/`else` stanzas are not descended into - but it reads every real `.cabal`
file this repo ships (`references/miso/sample-app/app.cabal`,
`references/misogram/miso-gram.cabal`) correctly; see `test/project.test.mjs`,
which is also the honest way to check "does opening a folder work" at all -
there is no way to script a browser's own native folder picker.

## Everything that is not the Prelude

`assets/lib.bin` is only the packages a Prelude program needs. `miso`,
`random`, `containers`, `text` and the rest live in a second, separately
fetched blob (`assets/miso.bin`), and the page works out for itself when a
program wants one of them: `neededPackages` in `project.mjs` reads every
`import` in every `.hs` under the root, plus a `.cabal`'s `build-depends`,
against `assets/pkgs.json` - a module-to-package index `pack-assets.mjs`
writes next to the blob, small enough to fetch up front. Anything it matches
fetches `miso.bin` and adds `-package-db /lib/pkgs/package.conf.d`, plus
`-package <name>` for each package that lives in that database. So a single
pasted file that says `import System.Random` compiles, with no project
around it and nothing to configure.

One thing the packages do not bring with them is the JavaScript GHC's linker
would have made from their C sources, which `-ddisable-js-c-sources` leaves
out. `C_SHIMS` in `index.html` is prepended to a compiled program to cover
it: `assets/jsbi-shim.js`, the same one `build-compiler.mjs` puts in front of
the compiler, plus splitmix's seed, which every `randomRIO` and `newStdGen`
in `random` starts from.

`{-# LANGUAGE CPP #-}` would normally make GHC hand the file to a real cpp
before it parses anything, and there is nothing here to spawn. `cpp.mjs` is
what answers instead, from inside the `child_process` shim: conditionals,
object- and function-like macros, `#include`, and line markers so GHC's
errors still point at the real source. Every miso example uses CPP for its
`#ifdef WASM` block, so this is the difference between a repository loading
and not.

## More than one miso

A `cabal.project` can pin a revision of miso, and the API has moved: `View`
and `Effect` have each gained a type parameter since 1.10, so a project
written against the older one does not typecheck against the newer.

`node build/miso-web/build.mjs --ref 1.10.0` builds that tag as well, into
`dist/pkgs-1.10.0`. Only miso itself is kept there: its dependencies are the
same builds `dist/pkgs` already holds, so the two databases stack and the
alternate is 11 MB rather than 90. `pack-assets.mjs` packs each one as its own
blob and records it in `pkgs.json`, and the page fetches it only when a
mounted project's pin names it. `-package-id miso-1.10.0.0-inplace` is what
selects it: `-package miso` would take the newest version on offer.

An old miso may need a fix to build or run under this compiler, the same way
ghcjs-base does. `miso-<ref>.patch` beside `build.mjs` is applied to the
worktree if it is there; 1.10.0's is one character, an FFI import that writes
`$2` in a body whose parameter list stops at `$1`.

When there is no build for a pin, the page names it after a failed compile.
Read that as a hint and not a verdict: `haskell-miso/snake` fails on
`windowSub`, and its own pinned miso has the same signature - the repository
is simply behind, and two lines in its `subs` fix it.

## Template Haskell

A splice has to *run*, and GHC's answer for the JavaScript target is a second
process: it makes two pipes, starts `node ghc-interp.js` on the far end, feeds
it `LOAD <file>` lines until it has an RTS and the GHCi server, sends
`RUN_SERVER`, and then talks the ordinary GHCi protocol across the pipes. See
Note [The JS interpreter] in GHC.

None of that needs a process here. The compiler is already JavaScript, so the
interpreter is a second global in the same page - a hidden same-origin iframe
- and the pipes are arrays. `startInterpreter` in `host.mjs` is the whole of
it, and GHC never learns the difference: it asks for `pipe(2)`, gets fds whose
queues are ours, spawns something whose stdin we read commands from, and
writes its protocol into an array the interpreter is waiting on.

Four things had to give way for it:

- **`h$pipe`** is unimplemented in the RTS. It is filled in by a shim
  prepended to the compiler's own bundle, because the fd table it has to
  write into is a local of the scope that bundle runs in.
- **`fcntl`** in the RTS always fails, and GHC uses it to set close-on-exec on
  those pipes. Nothing here ever execs, so it now succeeds.
- **`emcc`** gets called even under `-ddisable-js-c-sources`: the interpreter
  link asks for C sources unconditionally. It writes an empty `clibs.js`,
  which leaves the interpreter in the state the compiler is already in.
- **a `<script>`, not `eval`.** An indirect eval keeps its own `const`
  bindings to itself, and the RTS declares a good many at the top level for
  the code loaded after it to read. Loading a file as a real script element
  is what makes them visible.

It is slow: linking GHC's interpreter takes minutes, and the page does not
repaint while it happens. `ghc-heap` is in `dist/lib` for this (`ghci` depends
on it), and `ghci`'s whole closure rides in `miso.bin`, fetched when a source
turns out to have `TemplateHaskell` or `QuasiQuotes` in it.

A program that needs `miso` does not print to the log: it loads into the
`<iframe>` below it, on a blank page with a `<div id="app">`, exactly what
`startApp ... { mountPoint = Just "app" }` expects. The iframe is not
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
| `assets/miso.bin` | ~120 MB, fetched only for a program that needs a package beyond the Prelude |

Serve both with `Content-Encoding: gzip` and a long cache. Neither has been
shrunk yet: the compiler is linked at `-O0` with no dead-code pass, and the
library blob keeps every module of every boot package.

`pack-assets.mjs` splits each of these into 20 MiB chunks (`ghc.cjs.0`,
`ghc.cjs.1`, … plus `ghc.cjs.chunks.json` naming the count); the page
refetches and reassembles them before use. This is for Cloudflare Pages,
which refuses any single deployed file over 25 MiB - the whole `playground/`
directory, `assets/` included, can be pointed at directly as its build
output.
