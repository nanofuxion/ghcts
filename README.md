# ghcts

`ghcts` is a TypeScript-native Haskell-to-TypeScript compiler. Install it with
`npm install ghcts`, add `ghcts.json` to a local Haskell project, then run:

```sh
npx ghcts build --project .
```

To build and serve the browser output without a separate server dependency:

```sh
npx ghcts serve --project .
```

The build emits inspectable TypeScript and ESM for a source-driven Haskell
program. It includes layout-aware parsing, module/import resolution, retained
signatures and constraints, typed Core lowering, curried lazy evaluation,
algebraic data, records, pattern matching, `IO`, CPP selection, and generic
JavaScript FFI. The Miso fixture is compiled from the checked-in Haskell
sources; there is no generated counter implementation or `Miso.*` compiler
replacement. Browser builds package the selected Miso JavaScript asset and a
Node-native `serve` command is provided for local testing.

The current release targets the reachable default-browser Miso graph and Haskell 2010/GHC-compatible syntax used by that graph. Hackage solving, Template Haskell execution, arbitrary C FFI, and the remaining GHC extension surface are intentionally diagnosed as unsupported until implemented.

## Credits

ghcts was influenced by the design and conventions of several Haskell and
Haskell-to-JavaScript projects:

- [**miso**](https://github.com/dmjio/miso) — the compile-and-run benchmark and
  the application model ghcts targets; browser builds package Miso's JavaScript
  assets rather than substituting a compiler-owned implementation.
- [**GHCJS**](https://github.com/ghcjs/ghcjs) — lazy call-by-need evaluation,
  `foreign import javascript` FFI (including `GHCJS_NEW` callback-style
  imports), and the CPP branch conventions Miso's browser Cabal target expects.
- [**MicroHs**](https://github.com/augustss/MicroHs) — a compact, self-hosting
  Haskell compiler with combinator-based execution and a JavaScript runtime,
  showing how far a minimal compiler pipeline can reach in the browser.
- [**GHC**](https://www.haskell.org/ghc/) — wired-in boot libraries, Core-style
  lowering, and the Haskell 2010/GHC-compatible language surface ghcts aims to
  support.
- [**aihc**](https://github.com/ai-haskell-compiler/aihc) — phased compiler
  structure (parse, module resolution, typechecking) and layout-sensitive
  parsing patterns.

miso, GHCJS, GHC, and aihc are tracked as git submodules under `references/`.
After cloning, initialize them with:

```sh
git submodule update --init --recursive
```

The phrase "Any application that can be written in JavaScript, will eventually
be written in JavaScript" is known as **Jeff Atwood's Law**, coined by the
co-founder of Stack Overflow in 2009.

### Special thanks

Special thanks to [**dmjio**](https://github.com/dmjio) of
[**haskell-miso**](https://github.com/haskell-miso) for sparking an interest in
the idea, and also for creating the perfect framework to benchmark with.