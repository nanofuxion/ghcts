/**
 * Turn a folder the user picked into VFS files, and figure out where the
 * program starts.
 *
 * `mountDirectory` only needs `entries()`/`getFile()`/`kind` — the shape the
 * File System Access API's `FileSystemDirectoryHandle` has — so it, and the
 * `.cabal` parsing below, are exercised from plain node in
 * `test/project.test.mjs` against a handle built from an object literal.
 * There is no way to script the browser's own folder picker.
 *
 * The `.cabal` reading itself is `cabal.js`, the same module the CLI uses,
 * copied here by `npm run build` because a page can only load what is served
 * under `playground/`.
 */
import { dependencies as cabalDependencies, extensions as cabalExtensions, parseCabal as cabalStanzas, withImports, words as cabalWords } from "./cabal.js";

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

/** Every runnable stanza a `.cabal` file declares, in file order, reduced to
 * the pieces a compile needs. */
export function parseCabal(text) {
  const stanzas = cabalStanzas(text);
  return stanzas
    .filter((s) => s.type === "executable" || s.type === "test-suite")
    .map((s) => withImports(stanzas, s))
    .map((s) => {
      const dirs = cabalWords(s, "hs-source-dirs");
      return {
        name: s.name,
        mainIs: cabalWords(s, "main-is")[0],
        hsSourceDirs: dirs.length ? dirs : ["."],
        dependencies: cabalDependencies(s),
        // `default-language` and `default-extensions` are `-X` flags by
        // another name, and `cpp-options` are `-D`s. cabal is what would
        // otherwise be passing them on.
        extensions: cabalExtensions(s),
        cppOptions: cabalWords(s, "cpp-options"),
      };
    })
    .filter((e) => e.mainIs);
}

/** ghcts's own project format (`references/misogram/ghcts.json` and
 * similar): no version parsing needed, the dependency list is already names. */
function parseGhctsJson(text) {
  const j = JSON.parse(text);
  if (!j.entry?.module) return [];
  const dirs = j.sourceRoots?.length ? j.sourceRoots : ["."];
  return [{ name: j.entry.export ?? "main", mainIs: `${j.entry.module.split(".").join("/")}.hs`, hsSourceDirs: dirs, dependencies: j.dependencies ?? [], extensions: [], cppOptions: [] }];
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
        return { entry: rel, includeDirs: c.hsSourceDirs, dependencies: c.dependencies, extensions: c.extensions, cppOptions: c.cppOptions, usesMiso: c.dependencies.includes("miso") };
    }
  }

  for (const guess of ["Main.hs", "app/Main.hs", "src/Main.hs"])
    if (vfs.lookup(`${root}/${guess}`)) {
      const dir = guess.includes("/") ? guess.slice(0, guess.lastIndexOf("/")) : ".";
      return { entry: guess, includeDirs: [dir], dependencies: [], extensions: [], cppOptions: [], usesMiso: false };
    }

  return undefined;
}

/** Every module a Haskell source imports. */
export function importedModules(text) {
  return [...text.matchAll(/^import\s+(?:qualified\s+)?([A-Z][\w.']*)/gm)].map((m) => m[1]);
}

/** Every `.hs` file under `root`, so a compile can be told what its whole
 * project imports and not just what its entry module does. */
export function haskellSources(vfs, root) {
  const found = [];
  const walk = (path) => {
    const node = vfs.lookup(path);
    if (node?.children) for (const name of node.children.keys()) walk(`${path}/${name}`);
    else if (node && /\.l?hs$/i.test(path)) found.push(new TextDecoder().decode(vfs.readFile(path)));
  };
  walk(root);
  return found;
}

/**
 * Which packages from the separately-fetched database a compile needs, going
 * by what its sources import and what its `.cabal` asks for. `index` is
 * `assets/pkgs.json`, written by pack-assets.mjs: `modules` maps a module to
 * the package it comes from, `expose` are the packages that live in that
 * database (so they need `-package name`), and `boot` the ones already
 * registered globally that only need their files fetched.
 */
export function neededPackages(sources, dependencies, index) {
  const shipped = new Set([...index.expose, ...index.boot]);
  const need = new Set(dependencies.filter((d) => shipped.has(d)));
  for (const text of sources)
    for (const mod of importedModules(text)) if (index.modules[mod]) need.add(index.modules[mod]);
  return [...need];
}

/**
 * `https://github.com/owner/repo`, with or without the scheme, and with or
 * without a `/tree/<ref>` and a subdirectory under it. A bare `owner/repo`
 * works too, which is what people paste half the time.
 */
export function parseGitHubUrl(text) {
  const m = /^(?:https?:\/\/)?(?:www\.)?(?:github\.com\/)?([\w.-]+)\/([\w.-]+?)(?:\.git)?(?:\/(?:tree|blob)\/([^/]+)(?:\/(.*))?)?\/?$/.exec(text.trim());
  return m ? { owner: m[1], repo: m[2], ref: m[3] ?? "HEAD", dir: (m[4] ?? "").replace(/\/$/, "") } : undefined;
}

/** Sources, and the files that say how to build them. The rest of a repo is
 * images, CI config and a nix flake, none of which the compiler reads. */
const WANTED = /\.(hs|lhs|cabal)$|(^|\/)(cabal\.project|ghcts\.json)$/i;

/**
 * Copy a public GitHub repo into the VFS, with no server of our own in the
 * middle: one call to the tree API for the file list, then the files
 * themselves straight off raw.githubusercontent.com. Both send
 * `Access-Control-Allow-Origin: *`, so a page may read them directly.
 *
 * The tree API is the rate-limited one (60 an hour from an address, with no
 * token), which is why it is asked once and the files are not.
 */
export async function mountGitHub(vfs, repo, root, onProgress) {
  const api = `https://api.github.com/repos/${repo.owner}/${repo.repo}/git/trees/${repo.ref}?recursive=1`;
  const res = await fetch(api);
  if (!res.ok)
    throw new Error(
      res.status === 403 || res.status === 429
        ? "GitHub is rate-limiting this address. It allows 60 repository listings an hour."
        : `${res.status} ${res.statusText} for ${api}`,
    );
  const { tree, truncated } = await res.json();
  const prefix = repo.dir ? `${repo.dir}/` : "";
  const wanted = (tree ?? []).filter((e) => e.type === "blob" && e.path.startsWith(prefix) && WANTED.test(e.path));
  if (!wanted.length)
    throw new Error(truncated ? "that repository is too large for GitHub to list in one go" : "no Haskell sources in that repository");

  vfs.mkdirp(root);
  let done = 0;
  await Promise.all(
    wanted.map(async (e) => {
      const url = `https://raw.githubusercontent.com/${repo.owner}/${repo.repo}/${repo.ref}/${e.path}`;
      const r = await fetch(url);
      if (!r.ok) throw new Error(`${r.status} ${r.statusText} for ${url}`);
      const at = `${root}/${e.path.slice(prefix.length)}`;
      vfs.mkdirp(at.slice(0, at.lastIndexOf("/")));
      vfs.writeFile(at, new Uint8Array(await r.arrayBuffer()), Date.now());
      onProgress?.(++done, wanted.length);
    }),
  );
  return { count: wanted.length };
}

/**
 * Whether a compile is going to run a Template Haskell splice.
 *
 * It cannot, here: GHC runs splices in a separate interpreter process it
 * starts over a pipe, and a page has neither. Knowing in advance is worth
 * something anyway, because what GHC says when it hits one is that a module
 * is missing, which sounds like a packaging problem and is not.
 */
export function usesTemplateHaskell(sources, extensions = []) {
  const pragma = /\{-#\s*LANGUAGE\b[^#]*\b(TemplateHaskell|TemplateHaskellQuotes|QuasiQuotes)\b/;
  return extensions.some((x) => /-X(TemplateHaskell|QuasiQuotes)$/.test(x)) || sources.some((text) => pragma.test(text));
}

/**
 * What revision of miso a project's `cabal.project` pins, if it pins one.
 *
 * The page ships exactly one build of miso, so a project written against a
 * different revision can fail with a plain type error and no hint as to why.
 * Naming the pin is the hint.
 */
export function pinnedMiso(vfs, root) {
  const file = vfs.lookup(`${root}/cabal.project`) ? new TextDecoder().decode(vfs.readFile(`${root}/cabal.project`)) : "";
  for (const block of file.split(/^source-repository-package/m).slice(1)) {
    const location = /^\s*location:\s*(\S+)/m.exec(block)?.[1] ?? "";
    const tag = /^\s*tag:\s*(\S+)/m.exec(block)?.[1];
    if (tag && /\/miso(\.git)?\/?$/.test(location)) return tag;
  }
  return undefined;
}
