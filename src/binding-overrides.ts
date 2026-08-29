/** Per-(module, binding) source patches applied in memory during `loadProgram`,
 * so a dependency's checked-out source never needs local edits to build.
 *
 * Each entry replaces a `value` declaration with a `foreign import javascript`
 * of the same name, arity, and type - the same shape `parser.ts`'s `foreign()`
 * already produces, so every later stage treats it like an ordinary FFI import.
 *
 * Every entry is a fork of upstream behaviour, so each one is temporary: keep
 * it only until the fix lands in the dependency itself, and delete it once it
 * does. An override keyed on a name upstream still defines goes on silently
 * shadowing it, so a stale entry outlives the bug it was written for.
 */
export const BINDING_OVERRIDES: Record<string, Record<string, { javascript: string; signature: string[] }>> = {
  // Empty: miso's `performance.now()` crash on Lynx, the entry this layer was
  // written for, is fixed upstream as of dmjio/miso#1627.
};
