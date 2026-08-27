# Build status

## Source extraction

The isolated snapshot currently contains 103 source files:

- `extracted/current-ghc/compiler/GHC/JS`
- `extracted/current-ghc/compiler/GHC/StgToJS`
- `extracted/current-ghc/rts/js`
- `extracted/legacy-ghcjs/src/Gen2`
- the legacy GHCJS hook/program entrypoints

This is intentionally a source snapshot, not yet a standalone Cabal package.
The current-GHC backend imports the rest of GHC's internal compiler API, so a
buildable reduction must be driven by GHC's package/component graph rather than
by copying only these directories.

## Binaryen probe

`probes/hello.wasm` was generated with `clang --target=wasm32-wasip1 -nostdlib`
and converted successfully to `probes/hello.js` with Binaryen's `wasm2js`.
The output is direct JavaScript generated from Wasm instructions.

## JS-backend probe

The native host GHC 9.6.7 package contains `GHC.StgToJS`. The probe in
`probes/StgToJSProbe.hs` compiled with `-package ghc` and ran successfully,
printing `GHC.StgToJS is linkable`. This validates the intended JS-compiler
backend direction before attempting WASI hosting.

## Toolchain assessment

The official `ghc-wasm-meta` flake is available under `toolchain/ghc-wasm-meta`
and exposes a `wasm32-wasi-ghc` toolchain through Nix. Its first invocation
must still realize a large dependency closure, so the driver compilation has
not yet started. The host GHC is 9.6.7, while the checked-in GHC source is an
older development snapshot; the extracted driver must use matching GHC
sources and libraries.

The initial ordinary-Haskell WASI probe is now complete, but it is only a
host-toolchain sanity check; it does not validate the GHCJS backend. The
required compiler-host probe must use a matching GHC 8.10/GHCJS 8.10 graph and
must still import and execute the GHCJS JavaScript backend.

The standalone `ghc-wasm-meta#wasm32-wasi-ghc-9_6` output cannot be evaluated
on this aarch64-darwin host: the channel has no `aarch64-darwin-9.6` artifact.
The `9.14` artifact exists, but its closure still pulls a build-time npm
dependency and has not completed realization here. It is also not the right
version for a strict GHC 9.6 backend comparison. The checked-in GHC source is
newer development code, so the eventual probe should use a matching
source/toolchain pair rather than silently mixing versions.

## GHCJS bootstrap probe

The matching GHCJS 8.10.7 bootstrap now completes successfully. Its global
package database contains the legacy GHCJS compiler/runtime packages,
including `ghc-8.10.7`, `ghci-8.10.7`, `ghcjs-prim`, `ghcjs-th`, and the
boot libraries.

The booted compiler was verified with `Hello.hs`: it emits the standard
`.jsexe` bundle (`all.js`, `rts.js`, `lib.js`, `out.js`, `runmain.js`) and
the generated code uses the expected GHCJS symbol conventions such as
`h$...`, rather than producing a native executable. This is the first
end-to-end proof that the legacy JS backend is operational in the isolated
build environment.

This native GHCJS output is the compatibility oracle for the eventual WASI
host: the Wasm-to-JavaScript lowering must affect only the compiler host, not
replace the GHCJS code generator or change the emitted `.jsexe` shape.

## WASI-to-JavaScript lowering

Binaryen's `wasm2js` accepts Wasm/WAT and transforms it to asm.js/JavaScript.
The local probe confirms that it emits direct JavaScript, so it is preferred
over the smaller `thlorenz/wasm2js` package for the compiler-host lowering
stage. An npm wrapper can still expose the generated output as CommonJS or
ESM after this build-time conversion.

## WASI host probe

The ARM64-native `wasm32-wasi-ghc-9.14` bindist plus its matching WASI SDK
and libffi payload now compiles a Haskell probe to a valid Wasm module. A
direct `ghcjs` library build against it is correctly rejected by Cabal because
GHCJS 8.10.7 requires `base < 4.15`, while GHC 9.14 supplies `base-4.22`.
This is an explicit version-compatibility gate: the final compiler host must
use a matching GHC 8.10-era WASI toolchain or a deliberate, tested GHCJS port;
mixing the 8.10 backend with GHC 9.14 packages would invalidate the output
compatibility requirement.

A direct self-hosting probe reached 549 GHCJS compiler modules and then stopped
on non-boot external dependencies (`aeson`, `vector`, `unordered-containers`,
`hashable`, `safe`, and `wl-pprint-text`). Cabal cannot be used as the
self-hosting driver without additional package-specific handling because its
archive phase expects native `.o` files while GHCJS produces `.js_o`. This
confirms the viable fallback shape (a JavaScript GHCJS compiler bundle) but
does not yet replace the required WASI-hosted artifact.

An isolated worktree of the exact GHC 8.10.7 source now configures as a
`wasm32-unknown-wasi` cross compiler using the matching GHC 8.10.7 bootstrap
compiler. Target C compilation, LLVM code-generation setup, WASI `ar`, and
the GHC 8.10 build/host/target split all pass configuration. This is a
stronger feasibility result than the modern GHC 9.14 probe, but compilation
still needs to validate the old GHC sources against the available LLVM/WASI
toolchain.

The first cross-build attempt now gets past host bootstrap: it builds the
8.10 `ghc-cabal` utility and begins stage-1 package dependency generation.
The current failure is in the target-layout `deriveConstants` C probe;
WASI SDK Clang 21 and Homebrew LLVM 15 both crash while compiling the
generated probe. This is now the active source/toolchain issue, after the
build/host/target configuration and host bootstrap have been validated.

GHCup's `javascript-unknown-ghcjs-9.6.7` bindist is available for this host and
downloaded successfully, but its configure step rejects the installed LLVM
22.1.8 toolchain. The bindist requires LLVM 11 through 16 and recommends
Emscripten 3.1.74. This is relevant for a possible JS bootstrap route, but it
is separate from the intended result: the compiler still needs to use
`GHC.StgToJS`, while WASI or JS is only its host/distribution target.

The required Emscripten 3.1.74 SDK is now installed under `toolchain/emsdk`
and `emcc` passes its sanity check. However, this SDK does not expose the
standalone LLVM `llc`/`opt` tools required by the GHCup bindist configure
script, so the host falls back to Homebrew LLVM 22 and the bindist is rejected.
The next bootstrap attempt needs an LLVM 15-era toolchain (or explicit
configure overrides) in addition to Emscripten.

Attempting to build the legacy `ghcjs-boot` with the available native GHC 9.6.7
also fails at dependency resolution: GHCJS 8.10.7 requires `base < 4.15`, while
the host provides base 4.18.3. This confirms that the legacy tree needs a
matching GHC 8.10 toolchain and should remain a compatibility reference rather
than the first build target.

LLVM 15 is available at `/opt/homebrew/opt/llvm@15`, and with it plus the
installed Emscripten 3.1.74 SDK the GHCJS 9.6.7 bindist now installs
successfully at `~/.ghcup/ghc/javascript-unknown-ghcjs-9.6.7`. A plain Haskell
link still fails until the GHCJS boot libraries/object archive are built; the
failure is in the GHCJS linker while resolving `Control.Exception.Base`.
This confirms the compiler executable itself is present and identifies boot
libraries as the next required input.

The installed JavaScript-target GHC contains compiler package interfaces and
archives, but no target boot object archive. Compiling even `Hello.hs` reaches
the JS linker and fails on `Control.Exception.Base` because the target boot
objects are absent. This is a bootstrap dependency, not a backend failure:
the next artifact needed is a boot package database and archives generated by
the matching GHCJS toolchain.

With the matching GHC 8.10.7 host now available, `ghcjs-boot` progresses
through its dependencies but the legacy GHCJS package fails because the
`references/ghcjs/ghc` submodule does not contain the required GHC compiler
sources (including `HieTypes`). Substituting the newer `references/ghc` tree
would be an unverified compiler/API mix and is intentionally not done. The
legacy boot route therefore remains a reference until that exact submodule is
populated.
