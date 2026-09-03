/**
 * Turn a folder the user picked into VFS files, and figure out where the
 * program starts.
 *
 * `mountDirectory` only needs `entries()`/`getFile()`/`kind` — the shape the
 * File System Access API's `FileSystemDirectoryHandle` has — so it, and the
 * `.cabal` parsing below, are exercised from plain node in
 * `test/project.test.mjs` against a handle built from an object literal.
 * There is no way to script the browser's own folder picker.
 */

/** Recursively copy a picked directory into the VFS, keeping file handles so
 * edits can be written back to the real files they came from. */
export async function mountDirectory(vfs, handle, root) {
  const handles = new Map();
  let count = 0;
  const walk = async (dir, at) => {
    for await (const [name, entry] of dir.entries()) {
      if (name.startsWith(".")) continue; // .git and friends
      const path = `${at}/${name}`;
      if (entry.kind === "directory") {
        vfs.mkdirp(path);
        await walk(entry, path);
      } else {
        const file = await entry.getFile();
        vfs.writeFile(path, new Uint8Array(await file.arrayBuffer()), file.lastModified);
        handles.set(path, entry);
        count++;
      }
    }
  };
  vfs.mkdirp(root);
  await walk(handle, root);
  return { count, handles };
}

/** A cabal `key: value` field, value on the same line or indented below it.
 * Not a real parser: stanza nesting (`if`/`else`) is not tracked, so a field
 * written only inside a conditional block is read as if it were not. Real
 * projects put `main-is`/`hs-source-dirs`/`build-depends` at the stanza's top
 * level, which this covers. */
function parseCabalStanzas(text) {
  const stanzas = [];
  let current;
  let field, fieldIndent;
  const indentOf = (raw) => raw.length - raw.trimStart().length;
  for (const raw of text.split("\n")) {
    const line = raw.replace(/--.*$/, "");
    const header = /^(executable|library|test-suite|benchmark)\b\s*(\S*)/.exec(line);
    if (header && !/^\s/.test(raw)) {
      current = { type: header[1], name: header[2] || "", fields: new Map() };
      stanzas.push(current);
      field = undefined;
      continue;
    }
    if (!/^\s/.test(raw) && raw.trim() !== "") {
      current = undefined; // a new top-level (non-stanza) block
      field = undefined;
      continue;
    }
    if (!current || !raw.trim()) continue;
    const kv = /^\s+([a-zA-Z][a-zA-Z0-9_-]*):\s*(.*)$/.exec(raw);
    if (kv) {
      field = kv[1].toLowerCase();
      fieldIndent = indentOf(raw);
      const list = current.fields.get(field) ?? [];
      if (kv[2].trim()) list.push(kv[2].trim());
      current.fields.set(field, list);
    } else if (field && indentOf(raw) > fieldIndent) {
      // Deeper than the `key:` line it follows, so it is that field's
      // continuation. Anything shallower is a conditional block
      // (`if os(darwin)` and the like) this parser does not descend into -
      // stop attributing lines to `field` until a real key: line appears.
      current.fields.get(field).push(raw.trim());
    } else {
      field = undefined;
    }
  }
  return stanzas;
}

const words = (values) => values.flatMap((v) => v.split(/\s+/)).filter(Boolean);
/** `build-depends` entries carry version constraints: `miso >= 1 && < 2`. */
const bareDependencies = (values) =>
  values
    .join(" ")
    .split(",")
    .map((s) => s.trim().split(/\s/)[0])
    .filter(Boolean);

/** Every runnable stanza a `.cabal` file declares, in file order. */
export function parseCabal(text) {
  return parseCabalStanzas(text)
    .filter((s) => s.type === "executable" || s.type === "test-suite")
    .map((s) => ({
      name: s.name,
      mainIs: s.fields.get("main-is")?.join(" ").trim(),
      hsSourceDirs: s.fields.has("hs-source-dirs") ? words(s.fields.get("hs-source-dirs")) : ["."],
      dependencies: bareDependencies(s.fields.get("build-depends") ?? []),
    }))
    .filter((e) => e.mainIs);
}

/** ghcts's own project format (`references/misogram/ghcts.json` and
 * similar): no version parsing needed, the dependency list is already names. */
function parseGhctsJson(text) {
  const j = JSON.parse(text);
  if (!j.entry?.module) return [];
  const dirs = j.sourceRoots?.length ? j.sourceRoots : ["."];
  return [{ name: j.entry.export ?? "main", mainIs: `${j.entry.module.split(".").join("/")}.hs`, hsSourceDirs: dirs, dependencies: j.dependencies ?? [] }];
}

/**
 * Where a mounted project's program starts: a `.cabal` file's first
 * executable whose `main-is` exists on disk, then `ghcts.json`, then the
 * conventional paths every Haskell starter uses.
 */
export function findEntry(vfs, root) {
  const listing = vfs.lookup(root)?.children ? [...vfs.lookup(root).children.keys()] : [];
  const candidates = [];
  for (const name of listing.filter((n) => n.endsWith(".cabal")))
    candidates.push(...parseCabal(new TextDecoder().decode(vfs.readFile(`${root}/${name}`))));
  if (listing.includes("ghcts.json")) candidates.push(...parseGhctsJson(new TextDecoder().decode(vfs.readFile(`${root}/ghcts.json`))));

  for (const c of candidates) {
    for (const dir of c.hsSourceDirs) {
      const rel = dir === "." ? c.mainIs : `${dir}/${c.mainIs}`;
      if (vfs.lookup(`${root}/${rel}`))
        return { entry: rel, includeDirs: c.hsSourceDirs, dependencies: c.dependencies, usesMiso: c.dependencies.includes("miso") };
    }
  }

  for (const guess of ["Main.hs", "app/Main.hs", "src/Main.hs"])
    if (vfs.lookup(`${root}/${guess}`)) {
      const dir = guess.includes("/") ? guess.slice(0, guess.lastIndexOf("/")) : ".";
      return { entry: guess, includeDirs: [dir], dependencies: [], usesMiso: false };
    }

  return undefined;
}
