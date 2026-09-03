import { spawnSync } from "node:child_process";
import { existsSync, readdirSync, statSync } from "node:fs";
import { homedir } from "node:os";
import { delimiter, dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));

/** Where this package's own build put the compiler, if it has been built. */
export const bundledCompiler = (): { ghc: string; libdir: string } | undefined => {
  // `.cjs`, not `.js`: this package is `"type": "module"`, and GHC's RTS
  // detects node through `require`/`module`, which ESM does not have. Loaded
  // as ESM the compiler starts with no argv and no filesystem.
  const ghc = join(here, "ghc.cjs");
  const libdir = join(here, "lib");
  return existsSync(ghc) && existsSync(libdir) ? { ghc, libdir } : undefined;
};

/** A GHC JavaScript-target installation, as the compiler itself reports it. */
export interface GhcInstall {
  /** The binary that answered `--numeric-version`. */
  ghc: string;
  /** Its `ghc-pkg` sibling, if the installation ships one. */
  ghcPkg?: string;
  version: string;
  libdir: string;
}

const NAME = "javascript-unknown-ghcjs-ghc";
const versioned = new RegExp(`^${NAME}-\\d+(\\.\\d+)*$`);

/** Newest first, comparing version numbers rather than strings ("9.10" > "9.6"). */
const byVersionDesc = (a: string, b: string) => {
  const parts = (s: string) => (s.match(/\d+/g) ?? []).map(Number);
  const [x, y] = [parts(a), parts(b)];
  for (let i = 0; i < Math.max(x.length, y.length); i++) {
    const d = (y[i] ?? 0) - (x[i] ?? 0);
    if (d !== 0) return d;
  }
  return 0;
};

/** Every plausible compiler binary in one directory, newest first. */
function binariesIn(dir: string): string[] {
  let entries: string[];
  try {
    entries = readdirSync(dir);
  } catch {
    return [];
  }
  const found = entries.filter((f) => f === NAME || versioned.test(f));
  found.sort((a, b) => (a === NAME ? -1 : b === NAME ? 1 : byVersionDesc(a, b)));
  return found.map((f) => join(dir, f));
}

/**
 * Ask the compiler where it lives. Guessing from the binary's path does not
 * work: ghcup's entry on PATH is a shim whose directory has no `lib` beside
 * it, and a nix store path encodes a hash rather than a version.
 */
function probe(bin: string): GhcInstall | undefined {
  const ask = (flag: string) => {
    const r = spawnSync(bin, [flag], { encoding: "utf8" });
    return r.status === 0 ? r.stdout.trim() : undefined;
  };
  const version = ask("--numeric-version");
  const libdir = ask("--print-libdir");
  if (!version || !libdir) return undefined;
  const dir = dirname(bin);
  const ghcPkg = [`${NAME}-pkg-${version}`, `${NAME}-pkg`]
    .map((f) => join(dir, f))
    .find((p) => existsSync(p));
  return { ghc: bin, ghcPkg, version, libdir };
}

/** The installation at a path, which may name the binary or its directory. */
export function ghcInstallAt(path: string): GhcInstall | undefined {
  if (!existsSync(path)) return undefined;
  if (!statSync(path).isDirectory()) return probe(path);
  for (const bin of binariesIn(path)) {
    const install = probe(bin);
    if (install) return install;
  }
  return undefined;
}

/**
 * Find a GHC JavaScript cross compiler the way its own users install one:
 * `GHCTS_GHC` if set, then `PATH`, then ghcup's directories.
 */
export function findGhcJs(): GhcInstall | undefined {
  const configured = process.env.GHCTS_GHC;
  if (configured) return ghcInstallAt(configured);

  for (const dir of (process.env.PATH ?? "").split(delimiter)) {
    if (!dir) continue;
    for (const bin of binariesIn(dir)) {
      const install = probe(bin);
      if (install) return install;
    }
  }

  const ghcup = join(process.env.GHCUP_INSTALL_BASE_PREFIX ?? homedir(), ".ghcup");
  const roots: string[] = [];
  try {
    for (const entry of readdirSync(join(ghcup, "ghc")).sort(byVersionDesc))
      if (entry.startsWith("javascript-unknown-ghcjs-")) roots.push(join(ghcup, "ghc", entry, "bin"));
  } catch {
    // no ghcup, or no GHC installed through it
  }
  roots.push(join(ghcup, "bin"));
  for (const dir of roots) {
    for (const bin of binariesIn(dir)) {
      const install = probe(bin);
      if (install) return install;
    }
  }
  return undefined;
}

/** The `lib` directory GHC wants behind `-B`, as the compiler reports it. */
export function ghcLibdir(ghc: string): string {
  const install = ghcInstallAt(ghc);
  if (!install) throw new Error(`${ghc} did not answer --print-libdir`);
  return install.libdir;
}
