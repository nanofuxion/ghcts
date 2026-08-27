/** Minimal Cabal stanza reader used by the local-package resolver.  It keeps
 * package metadata separate from Haskell parsing and deliberately reports
 * only the source directories/assets that ghcts can consume today. */
export interface CabalLibrary {
  sourceDirs: string[];
  jsSources: string[];
  buildDepends: string[];
  cppOptions: string[];
}

export function parseCabalLibrary(source: string): CabalLibrary {
  const library: CabalLibrary = { sourceDirs: [], jsSources: [], buildDepends: [], cppOptions: [] };
  let inLibrary = false; let field: keyof CabalLibrary | undefined;
  const fields: Record<string, keyof CabalLibrary> = {
    'hs-source-dirs': 'sourceDirs', 'js-sources': 'jsSources', 'build-depends': 'buildDepends', 'cpp-options': 'cppOptions',
  };
  for (const raw of source.split(/\r?\n/)) {
    const line = raw.replace(/--.*$/, '');
    if (/^library\b/.test(line)) { inLibrary = true; field = undefined; continue; }
    if (/^[A-Za-z][A-Za-z0-9 -]*\b/.test(line) && !/^\s/.test(line)) { if (inLibrary) break; continue; }
    if (!inLibrary || !line.trim()) continue;
    // Library-level fields are indented two spaces.  Four-space fields are
    // conditional branches; target selection belongs to the resolver, so
    // they must not be merged into the unconditional library interface.
    const match = /^ {2}([A-Za-z-]+)\s*:\s*(.*)$/.exec(line);
    if (match && fields[match[1]]) { field = fields[match[1]]; append(library[field], match[2]); continue; }
    if (field && /^\s+/.test(line)) append(library[field], line.trim());
  }
  return library;
}

function append(target: string[], value: string) {
  for (const item of value.split(',').map(item => item.trim()).filter(Boolean)) target.push(item.replace(/\s.*$/, ''));
}
