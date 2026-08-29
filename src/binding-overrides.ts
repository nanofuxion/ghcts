/** Per-(module, binding) source patches applied in memory during `loadProgram`,
 * so a dependency's checked-out source never needs local edits to build.
 *
 * Each entry replaces a `value` declaration with a `foreign import javascript`
 * of the same name, arity, and type - the same shape `parser.ts`'s `foreign()`
 * already produces, so every later stage treats it like an ordinary FFI import.
 *
 * TEMPORARY: this is a fork of upstream behaviour, kept here only until the
 * fix lands in the dependency itself. Remove the entry once it does.
 */
export const BINDING_OVERRIDES: Record<string, Record<string, { javascript: string; signature: string[] }>> = {
  // Miso's `now` reads `performance.now()` unconditionally
  // (src/Miso/FFI/Internal.hs). Lynx's background-thread realm has no
  // `performance` global, so that throw took down anything timestamped from
  // there, including gesture handling like double-tap detection. Falls back
  // to `Date.now()`, which every realm has.
  "Miso.FFI.Internal": {
    now: {
      javascript:
        "(() => (typeof performance !== 'undefined' && performance && typeof performance.now === 'function') ? performance.now() : Date.now())",
      signature: ["IO Double"],
    },
  },
};
