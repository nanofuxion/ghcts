/** Per-(module, binding) source patches applied in memory during `loadProgram`,
 * so a dependency's checked-out source never needs local edits to build.
 *
 * Each entry replaces a `value` declaration with a `foreign import javascript`
 * of the same name, arity, and type - the same shape `parser.ts`'s `foreign()`
 * already produces, so every later stage treats it like an ordinary FFI import.
 *
 * TEMPORARY: this is a fork of upstream behaviour, kept here only until the
 * fix lands in the dependency itself. Remove the entry once it does - an
 * override keyed on a name upstream still defines goes on silently shadowing
 * it, so a stale entry outlives the bug it was written for.
 */
export const BINDING_OVERRIDES: Record<string, Record<string, { javascript: string; signature: string[] }>> = {
  // Miso's `now` reads `performance.now()` unconditionally
  // (src/Miso/FFI/Internal.hs). Lynx's background-thread realm has no
  // `performance` global, so that throw took down anything timestamped from
  // there, including gesture handling like double-tap detection. Falls back
  // to `Date.now()`, which every realm has.
  //
  // Sent upstream as https://github.com/dmjio/miso/pull/1627, which moves the
  // fallback into `now_ffi` across miso's js, wasm and ghc FFI backends.
  // Delete this entry once that merges and the submodule is bumped past it.
  "Miso.FFI.Internal": {
    now: {
      javascript:
        "(() => (typeof performance !== 'undefined' && performance && typeof performance.now === 'function') ? performance.now() : Date.now())",
      signature: ["IO Double"],
    },
  },
};
