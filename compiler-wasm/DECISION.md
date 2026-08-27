# Extraction decision

The first implementation candidate is the current GHC tree's `GHC.StgToJS`
backend, with the legacy GHCJS `Gen2` backend retained as the compatibility
reference.

This is preferable to trying to compile the complete legacy GHCJS package
unchanged: the checked-in GHC already contains a maintained JavaScript backend
(`compiler/GHC/StgToJS`) and a maintained WASM target/runtime (`rts/wasm`). The
legacy GHCJS tree remains authoritative for the output conventions required by
the existing fixtures, so generated output must be compared before switching
the backend.

The first executable probe should therefore be a current-GHC compiler driver
with JavaScript backend support, not `ghcjs-boot` or the legacy package manager.
There are two distinct compilation directions:

* **Compiler target:** the extracted compiler must invoke `GHC.StgToJS` and
  emit GHC-compatible JavaScript for Haskell input.
* **Compiler host:** that compiler executable may itself be compiled to
  `wasm32-wasi`, then optionally lowered with Binaryen `wasm2js` so npm can run
  it without a native executable.

Only the second direction uses the WASI backend. Binaryen `wasm2js` is a final
packaging/lowering experiment, not part of the Haskell frontend or JS backend.

## Open technical gates

1. Determine whether the current GHC JS backend emits the exact identifiers,
   wrapper layout, RTS calls, and module shape expected by `counter` and
   `misogram`.
2. Identify the minimum GHC driver/API and package database needed by that
   backend.
3. Prove that the reduced executable avoids unsupported WASI features.
4. Compare direct Wasm execution against Binaryen-lowered JavaScript; retain
   direct Wasm if it is smaller or more reliable.
