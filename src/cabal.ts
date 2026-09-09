/**
 * Enough of `.cabal` and `cabal.project` to build a project.
 *
 * Not a Cabal implementation: conditional blocks are not descended into, and
 * the only fields read are the ones a build needs. Real projects put those at
 * a stanza's top level, which is what this covers.
 *
 * `playground/project.mjs` parses `.cabal` too, for the browser, over a
 * virtual filesystem and only far enough to find where a program starts.
 */

export interface Stanza {
  /** `library`, `executable`, `test-suite`, `benchmark`, `common` */
  type: string;
  name: string;
  fields: Map<string, string[]>;
}

export interface Conditions {
  /** What `arch(...)` is true of. */
  arch: string;
  /** Flags that are on; every other `flag(...)` is off. */
  flags: Set<string>;
}

const DEFAULTS: Conditions = { arch: "javascript", flags: new Set() };

/**
 * An `if`/`elif`/`else` condition, as much of one as a `.cabal` uses:
 * `flag(x)`, `arch(x)`, `impl(x)`, `os(x)`, `!`, `&&`, `||`. Anything it does
 * not recognise is false, which is the safe way to be wrong - a branch is
 * skipped rather than wrongly taken.
 */
export function evalCondition(text: string, cond: Conditions): boolean {
  const atom = (s: string): boolean => {
    const m = /^(flag|arch|os|impl)\s*\(\s*([^)\s]+)/.exec(s.trim());
    if (!m) return s.trim().toLowerCase() === "true";
    if (m[1] === "flag") return cond.flags.has(m[2]!.toLowerCase());
    if (m[1] === "arch") return m[2]!.toLowerCase() === cond.arch;
    // `impl(ghcjs)` is the old compiler, never this one, and no `os` test
    // matters to a build that only ever targets JavaScript.
    return false;
  };
  const parts = (s: string, sep: string) => {
    const out: string[] = [];
    let depth = 0;
    let at = 0;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === "(") depth++;
      else if (s[i] === ")") depth--;
      else if (depth === 0 && s.startsWith(sep, i)) {
        out.push(s.slice(at, i));
        i += sep.length - 1;
        at = i + 1;
      }
    }
    out.push(s.slice(at));
    return out;
  };
  const value = (s: string): boolean => {
    const t = s.trim();
    if (parts(t, "||").length > 1) return parts(t, "||").some(value);
    if (parts(t, "&&").length > 1) return parts(t, "&&").every(value);
    if (t.startsWith("!")) return !value(t.slice(1));
    // A whole expression in brackets, rather than a `flag(x)`-style call.
    if (/^\(/.test(t) && !/^[a-z]/i.test(t)) return value(t.slice(1, t.lastIndexOf(")")));
    return atom(t);
  };
  return value(text);
}

/**
 * A `key: value` field, with the value on the same line or indented below.
 * `if`/`elif`/`else` blocks are evaluated, so a stanza's fields are the ones
 * that apply to `cond` rather than every branch's at once.
 */
export function parseCabal(text: string, cond: Conditions = DEFAULTS): Stanza[] {
  const stanzas: Stanza[] = [];
  let current: Stanza | undefined;
  let field: string | undefined;
  let fieldIndent = 0;
  /** One frame per open conditional: how far it is indented, whether this
   * branch applies, and whether an earlier branch of it already did. */
  let blocks: { indent: number; on: boolean; taken: boolean }[] = [];
  const indentOf = (raw: string) => raw.length - raw.trimStart().length;
  const live = () => blocks.every((b) => b.on);

  for (const raw of text.split("\n")) {
    const line = raw.replace(/--.*$/, "");
    const header = /^(library|executable|test-suite|benchmark|common)\b\s*(\S*)/.exec(line);
    if (header && !/^\s/.test(raw)) {
      current = { type: header[1]!, name: header[2] ?? "", fields: new Map() };
      stanzas.push(current);
      field = undefined;
      blocks = [];
      continue;
    }
    if (!/^\s/.test(raw) && raw.trim() !== "") {
      current = undefined;
      field = undefined;
      blocks = [];
      continue;
    }
    if (!current || !raw.trim()) continue;

    const indent = indentOf(raw);
    const branch = /^\s*(if|elif|else)\b\s*(.*)$/.exec(line);
    // A block ends where the indentation comes back to its own level - except
    // for the `elif`/`else` that continues it, which sits at exactly that
    // level and has to see the frame to know whether a branch was taken.
    const continues = branch !== null && branch[1] !== "if";
    while (blocks.length && indent < blocks[blocks.length - 1]!.indent) blocks.pop();
    while (blocks.length && indent === blocks[blocks.length - 1]!.indent && !continues) blocks.pop();

    if (branch) {
      field = undefined;
      if (!continues) {
        blocks.push({ indent, on: live() && evalCondition(branch[2]!, cond), taken: false });
        blocks[blocks.length - 1]!.taken = blocks[blocks.length - 1]!.on;
        continue;
      }
      const previous = blocks.pop();
      const on = !previous?.taken && live() && (branch[1] === "else" || evalCondition(branch[2]!, cond));
      blocks.push({ indent, on, taken: (previous?.taken ?? false) || on });
      continue;
    }

    const kv = /^\s+([a-zA-Z][a-zA-Z0-9_-]*):\s*(.*)$/.exec(raw);
    if (kv) {
      field = live() ? kv[1]!.toLowerCase() : undefined;
      fieldIndent = indent;
      if (!field) continue;
      const list = current.fields.get(field) ?? [];
      if (kv[2]!.trim()) list.push(kv[2]!.trim());
      current.fields.set(field, list);
    } else if (field && indent > fieldIndent) {
      // Deeper than the `key:` line it follows, so it continues that field.
      current.fields.get(field)!.push(raw.trim());
    } else {
      field = undefined;
    }
  }
  return stanzas;
}

/**
 * A stanza with the `common` blocks it imports folded in.
 *
 * `import: cpp, deps` is how a `.cabal` shares settings between stanzas, and
 * miso keeps most of its build there, so a stanza read on its own is missing
 * the half that matters. Imported values come first, the stanza's own after.
 */
export function withImports(stanzas: Stanza[], stanza: Stanza): Stanza {
  const commons = new Map(stanzas.filter((s) => s.type === "common").map((s) => [s.name, s]));
  const merged: Stanza = { type: stanza.type, name: stanza.name, fields: new Map() };
  const add = (from: Stanza) => {
    for (const [key, values] of from.fields) {
      if (key === "import") continue;
      merged.fields.set(key, [...(merged.fields.get(key) ?? []), ...values]);
    }
  };
  for (const name of (stanza.fields.get("import") ?? []).join(" ").split(",").map((n) => n.trim())) {
    const common = commons.get(name);
    if (common) add(withImports(stanzas, common));
  }
  add(stanza);
  return merged;
}

/** A field's value, split into words. */
export const words = (stanza: Stanza | undefined, name: string): string[] =>
  (stanza?.fields.get(name) ?? []).flatMap((v) => v.split(/\s+/)).filter(Boolean);

/** `build-depends` entries carry version constraints: `miso >= 1 && < 2`. */
export const dependencies = (stanza: Stanza | undefined): string[] =>
  (stanza?.fields.get("build-depends") ?? [])
    .join(" ")
    .split(",")
    .map((s) => s.trim().split(/\s/)[0]!)
    .filter(Boolean);

/** `default-language` and `default-extensions`, as GHC flags. */
export const extensions = (stanza: Stanza | undefined): string[] =>
  [...words(stanza, "default-language"), ...words(stanza, "default-extensions")].map((x) => `-X${x}`);

export interface SourcePin {
  location: string;
  tag?: string;
  subdir?: string;
  /** The last path segment of the location, without `.git`. */
  name: string;
}

/** `cabal.project`'s `packages:` paths and its `source-repository-package`
 * pins, which is how a project asks for a dependency by git revision. */
export function parseCabalProject(text: string): { packages: string[]; pins: SourcePin[] } {
  const packages = /^packages:\s*([\s\S]*?)(?=^\S|\Z)/m.exec(text)?.[1] ?? "";
  const pins: SourcePin[] = [];
  for (const block of text.split(/^source-repository-package/m).slice(1)) {
    const location = /^\s*location:\s*(\S+)/m.exec(block)?.[1];
    if (!location) continue;
    pins.push({
      location,
      tag: /^\s*tag:\s*(\S+)/m.exec(block)?.[1],
      subdir: /^\s*subdir:\s*(\S+)/m.exec(block)?.[1],
      name: location.replace(/\.git$/, "").replace(/\/$/, "").split("/").pop()!,
    });
  }
  return { packages: packages.split(/\s+/).filter(Boolean), pins };
}
