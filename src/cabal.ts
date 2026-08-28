/** Minimal Cabal stanza reader used by the local-package resolver.  It keeps
 * package metadata separate from Haskell parsing and deliberately reports
 * only the source directories/assets that ghcts can consume today.
 *
 * Conditionals are resolved here rather than left to a caller: a package's
 * `js-sources` are routinely reachable only through them.  miso declares its
 * entire JavaScript runtime inside an `if flag(native) && flag(production)`
 * chain nested in a `common` stanza, so a reader that skipped conditionals
 * reported no JavaScript at all for it. */
export interface CabalLibrary {
  sourceDirs: string[];
  jsSources: string[];
  buildDepends: string[];
  cppOptions: string[];
}

/** A stanza also records the `common` stanzas it inherits from. */
interface Stanza extends CabalLibrary {
  imports: string[];
}

const FIELDS: Record<string, keyof Stanza> = {
  'hs-source-dirs': 'sourceDirs', 'js-sources': 'jsSources', 'build-depends': 'buildDepends',
  'cpp-options': 'cppOptions', 'import': 'imports',
};

interface Line { indent: number; text: string }

/** One frame per open `if`.  `taken` records whether any branch of the chain
 * has already matched, which is what `elif`/`else` test. */
interface Frame { indent: number; active: boolean; taken: boolean }

export function parseCabalLibrary(source: string, flags: Iterable<string> = []): CabalLibrary {
  const lines: Line[] = [];
  for (const raw of source.split(/\r?\n/)) {
    const stripped = raw.replace(/--.*$/, '').replace(/\s+$/, '');
    if (stripped.trim()) lines.push({ indent: stripped.length - stripped.trimStart().length, text: stripped.trim() });
  }

  const enabled = new Set([...flags].map(flag => flag.toLowerCase()));
  const defaults = flagDefaults(lines);
  // A flag the project does not name falls back to the package's own `default:`.
  const flagValue = (name: string): boolean => enabled.has(name) || defaults.get(name) === true;

  const stanzas = new Map<string, Stanza>();
  const stanza = (name: string): Stanza => {
    const existing = stanzas.get(name);
    if (existing) return existing;
    const fresh: Stanza = { sourceDirs: [], jsSources: [], buildDepends: [], cppOptions: [], imports: [] };
    stanzas.set(name, fresh);
    return fresh;
  };

  let current: Stanza | undefined;
  let stack: Frame[] = [];
  let fieldName: string | undefined;
  let fieldIndent = 0;

  for (const line of lines) {
    if (line.indent === 0) {
      const common = /^common\s+([A-Za-z0-9_-]+)/.exec(line.text);
      current = /^library\b/.test(line.text) ? stanza('library') : common ? stanza(common[1]) : undefined;
      stack = []; fieldName = undefined;
      continue;
    }
    if (!current) continue;

    const chain = /^(elif\b|else\b)/.test(line.text);
    // A frame closes once indentation returns to or passes its own level; the
    // `elif`/`else` continuing that same chain is the one line that keeps it.
    while (stack.length) {
      const top = stack[stack.length - 1];
      if (top.indent > line.indent || (top.indent === line.indent && !chain)) stack.pop();
      else break;
    }

    const iff = /^if\s+(.*)$/.exec(line.text);
    if (iff) {
      const taken = condition(iff[1], flagValue);
      stack.push({ indent: line.indent, active: stack.every(frame => frame.active) && taken, taken });
      fieldName = undefined;
      continue;
    }
    if (chain) {
      const frame = stack[stack.length - 1];
      if (!frame || frame.indent !== line.indent) continue;
      const elif = /^elif\s+(.*)$/.exec(line.text);
      const taken = !frame.taken && (elif ? condition(elif[1], flagValue) : true);
      frame.active = stack.slice(0, -1).every(outer => outer.active) && taken;
      frame.taken = frame.taken || taken;
      fieldName = undefined;
      continue;
    }

    const active = stack.every(frame => frame.active);
    const continuation = fieldName !== undefined && line.indent > fieldIndent;
    const match = continuation ? undefined : /^([A-Za-z][A-Za-z0-9-]*)\s*:\s*(.*)$/.exec(line.text);
    if (match) {
      fieldName = match[1].toLowerCase();
      fieldIndent = line.indent;
      const field = FIELDS[fieldName];
      if (field && active) append(current[field], match[2]);
      continue;
    }
    const field = fieldName === undefined ? undefined : FIELDS[fieldName];
    if (continuation && field && active) append(current[field], line.text);
  }

  // `import: client` splices a `common` stanza's fields in ahead of the
  // library's own, which is the order cabal itself composes them in.
  const library = stanzas.get('library') ?? stanza('library');
  const merged: CabalLibrary = { sourceDirs: [], jsSources: [], buildDepends: [], cppOptions: [] };
  for (const source of [...library.imports.map(name => stanzas.get(name)), library]) {
    if (!source) continue;
    for (const key of Object.keys(merged) as (keyof CabalLibrary)[]) merged[key].push(...source[key]);
  }
  return merged;
}

/** Every `flag` stanza's `default:`.  Cabal allows the value on the following
 * line, which is how miso writes all of its. */
function flagDefaults(lines: Line[]): Map<string, boolean> {
  const defaults = new Map<string, boolean>();
  for (let i = 0; i < lines.length; i++) {
    const flag = /^flag\s+([A-Za-z0-9_-]+)$/.exec(lines[i].text);
    if (!flag || lines[i].indent !== 0) continue;
    let value = false;
    for (let j = i + 1; j < lines.length && lines[j].indent > 0; j++) {
      const field = /^default\s*:\s*(.*)$/i.exec(lines[j].text);
      if (field) value = /^true$/i.test(field[1].trim() || (lines[j + 1]?.text ?? '').trim());
    }
    defaults.set(flag[1].toLowerCase(), value);
  }
  return defaults;
}

/** The fragment of Cabal's condition language packages actually use for
 * `js-sources`: `flag(x)`, negation, `&&`, `||`.  Everything else resolves
 * against what ghcts is - GHC's JavaScript backend - so `arch(javascript)`
 * holds and `impl(ghcjs)`, `arch(wasm32)` and the rest do not.
 *
 * `||` is split before `&&` because it binds loosest; neither operator can
 * occur inside the parentheses of a `flag(...)`, so a plain split is exact. */
function condition(expr: string, flagValue: (name: string) => boolean): boolean {
  if (expr.includes('||')) return expr.split('||').some(part => condition(part, flagValue));
  if (expr.includes('&&')) return expr.split('&&').every(part => condition(part, flagValue));
  const atom = expr.trim();
  if (atom.startsWith('!')) return !condition(atom.slice(1), flagValue);
  const call = /^([A-Za-z]+)\s*\(\s*([^)]*)\)$/.exec(atom);
  if (!call) return false;
  const argument = call[2].trim().toLowerCase();
  if (call[1].toLowerCase() === 'flag') return flagValue(argument);
  return call[1].toLowerCase() === 'arch' && argument === 'javascript';
}

function append(target: string[], value: string) {
  for (const item of value.split(',').map(item => item.trim()).filter(Boolean)) target.push(item.replace(/\s.*$/, ''));
}
