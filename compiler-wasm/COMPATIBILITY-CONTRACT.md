# JavaScript compatibility contract

The output target is the existing GHCJS-shaped module format used by the
fixtures, not merely executable JavaScript. The compatibility baseline includes:

- module files whose generated bindings use the established encoded Haskell
  names (for example `v_Module_2e_Submodule_2e_name`);
- the project runtime's lazy/forced application convention;
- GHCJS foreign-function markers and `$1`, `$2`, ... argument conventions;
- the existing `GHC.JS.Prim`, `GHC.JS.Foreign.Callback`, and `GHCJS.Marshal`
  interop surface;
- the runtime/linker module layout consumed by the counter and misogram
  fixtures.

Any extracted GHC backend must be compared at the generated-module and runtime
levels. A compiler that produces semantically equivalent JavaScript but changes
these names, wrappers, or FFI shapes is not compatible with this repository.

The legacy generated files under `test/fixtures/miso-counter/dist` and
`references/misogram/dist` are the current golden artifacts. The extracted
current-GHC backend is only a candidate until it reproduces those contracts.
