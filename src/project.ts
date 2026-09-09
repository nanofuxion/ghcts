/**
 * Build a project's source dependencies at compile time, instead of shipping
 * them prebuilt.
 *
 * The dependency that varies between projects is the one pinned to a git
 * revision in `cabal.project` - miso, for every app in the haskell-miso
 * organisation. That one is checked out here, once per revision, and compiled
 * as part of the program: one `--make` run over the app's source directories
 * and the dependency's, with the flags each `.cabal` asks for. GHC's own
 * recompilation checking is the cache, so the second build only redoes what
 * changed.
 *
 * One process, one dependency graph, no archives and no package registration.
 * Nothing is fetched from Hackage: a dependency's *own* dependencies come from
 * a package database, which is what `dist/pkgs` still is.
 *
 * A pin that is *already built* is not built again. A database named after the
 * revision is used first, then the default one; only a pin nothing has is
 * fetched and compiled, which is the slow path and the point of the exercise.
 */
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readdirSync, readFileSync } from "node:fs";
import { homedir } from "node:os";
import { join, resolve } from "node:path";
import { dependencies, extensions, parseCabal, parseCabalProject, type SourcePin, type Stanza, withImports, words } from "./cabal.js";

export interface Plan {
  /** GHC flags: include path, build directory, extensions, cpp defines. */
  args: string[];
  /** The program's entry file, which goes last on the command line. */
  entry: string;
  /** `js-sources` from every package in the build, to put in front of the
   * linked program: GHC does not link them for a source dependency. */
  jsSources: string[];
  /** Where the `.hi` and `.o` live between builds. */
  buildDir: string;
}

const run = (cmd: string, args: string[], cwd?: string) => {
  const r = spawnSync(cmd, args, { cwd, stdio: "inherit" });
  if (r.status !== 0) throw new Error(`${cmd} ${args.join(" ")} failed (${r.status ?? r.signal})`);
};

/** Where a pinned dependency's sources are kept, one directory per revision. */
export const checkoutDir = (pin: SourcePin, cache: string) => join(cache, `${pin.name}-${pin.tag ?? "HEAD"}`);

/** Clone a pin's revision if it is not already there. Shallow: only the one
 * commit is ever needed, and these repositories are not small. */
export function ensureCheckout(pin: SourcePin, cache: string): string {
  const dir = checkoutDir(pin, cache);
  if (existsSync(join(dir, ".git"))) return dir;
  mkdirSync(dir, { recursive: true });
  console.error(`ghcts: fetching ${pin.name} ${pin.tag ?? "HEAD"}`);
  run("git", ["init", "-q", dir]);
  run("git", ["remote", "add", "origin", pin.location], dir);
  run("git", ["fetch", "-q", "--depth", "1", "origin", pin.tag ?? "HEAD"], dir);
  run("git", ["checkout", "-q", "FETCH_HEAD"], dir);
  return dir;
}

/** The stanzas of the one `.cabal` in a directory, each with the `common`
 * blocks it imports already folded in. */
const cabalIn = (dir: string): Stanza[] => {
  const name = readdirSync(dir).find((f) => f.endsWith(".cabal"));
  if (!name) return [];
  const stanzas = parseCabal(readFileSync(join(dir, name), "utf8"));
  return stanzas.map((s) => withImports(stanzas, s));
};

const sourceDirs = (stanza: Stanza | undefined, dir: string) =>
  (words(stanza, "hs-source-dirs").length ? words(stanza, "hs-source-dirs") : ["."]).map((d) => resolve(dir, d));

/** The package names a database holds. `-hide-package` is an error for a name
 * no database has, so a pin is only hidden when there is something to hide. */
export function packageNames(db: string): Set<string> {
  const names = new Set<string>();
  if (!existsSync(db)) return names;
  for (const file of readdirSync(db).filter((f) => f.endsWith(".conf"))) {
    const name = /^name:\s*(\S+)/m.exec(readFileSync(join(db, file), "utf8"))?.[1];
    if (name) names.add(name);
  }
  return names;
}

/**
 * @param dir the project root, holding its `.cabal` and `cabal.project`
 * @param databases package databases the build will see, so a pin that also
 *   has a prebuilt copy in one of them can be hidden in favour of the source
 * @param cache where pinned checkouts are kept, `~/.cache/ghcts/src` by default
 */
/** The unit id a database holds for a package, which is what selects that
 * build rather than the newest version on offer. */
const packageId = (db: string, name: string) =>
  readdirSync(db)
    .find((f) => f.startsWith(`${name}-`) && f.endsWith(".conf"))
    ?.replace(/\.conf$/, "");

/**
 * @param dir the project root, holding its `.cabal` and `cabal.project`
 * @param databases package databases the build will see, so a pin one of them
 *   already holds is used rather than built again
 * @param alternates package databases by the revision they were built from, so
 *   a pin naming that revision gets exactly that build
 * @param cache where pinned checkouts are kept, `~/.cache/ghcts/src` by default
 */
export function planProject(
  dir: string,
  databases: string[] = [],
  alternates: Record<string, string> = {},
  cache = join(homedir(), ".cache", "ghcts", "src"),
): Plan {
  const registered = new Set(databases.flatMap((db) => [...packageNames(db)]));
  const stanzas = cabalIn(dir);
  const app = stanzas.find((s) => s.type !== "library" && s.fields.has("main-is"));
  if (!app) throw new Error(`no executable stanza with a main-is in ${dir}`);
  const mainIs = words(app, "main-is")[0]!;

  const projectFile = join(dir, "cabal.project");
  const { pins } = existsSync(projectFile) ? parseCabalProject(readFileSync(projectFile, "utf8")) : { pins: [] as SourcePin[] };

  const includes = sourceDirs(app, dir);
  const flags = new Set(extensions(app));
  const jsSources: string[] = [];
  const hide: string[] = [];

  // A pin the project does not actually depend on is not worth building.
  const wanted = new Set(dependencies(app));
  for (const pin of pins.filter((p) => wanted.has(p.name))) {
    // Built already, for this very revision.
    const alternate = pin.tag ? alternates[pin.tag] : undefined;
    if (alternate) {
      const id = packageId(alternate, pin.name);
      console.error(`ghcts: ${pin.name} ${pin.tag} is built already, in ${alternate}`);
      hide.push("-package-db", alternate, ...(id ? ["-package-id", id] : ["-package", pin.name]));
      continue;
    }
    // Built already, though not necessarily from this revision. Compiling a
    // library takes tens of minutes, and a mismatch says so in seconds.
    if (registered.has(pin.name)) {
      console.error(`ghcts: ${pin.name} is in a package database already, not building it`);
      continue;
    }
    const at = pin.subdir ? join(ensureCheckout(pin, cache), pin.subdir) : ensureCheckout(pin, cache);
    const lib = cabalIn(at).find((s) => s.type === "library");
    if (!lib) throw new Error(`${pin.name} has no library stanza in ${at}`);
    includes.push(...sourceDirs(lib, at));
    for (const f of extensions(lib)) flags.add(f);
    for (const d of words(lib, "cpp-options")) flags.add(d);
    jsSources.push(...words(lib, "js-sources").map((f) => resolve(at, f)));
  }
  // `cpp-options` are only reachable with the extension that turns cpp on.
  if ([...flags].some((f) => f.startsWith("-D"))) flags.add("-XCPP");

  const buildDir = join(dir, "dist-ghcts");
  return {
    buildDir,
    jsSources,
    entry: resolve(includes[0]!, mainIs),
    args: [`-i${includes.join(":")}`, "-hidir", buildDir, "-odir", buildDir, ...flags, ...hide],
  };
}
