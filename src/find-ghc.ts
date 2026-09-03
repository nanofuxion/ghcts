import { existsSync, readdirSync } from "node:fs";
import { dirname, join } from "node:path";
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

/**
 * A `javascript-unknown-ghcjs-ghc` installation, for the build pipeline and
 * as a fallback libdir. `GHC_JS_BINDIR` wins; otherwise the nix store, whose
 * entries carry the version in the directory name, newest last.
 */
export function findGhcJs(): string | undefined {
  const configured = process.env.GHC_JS_BINDIR;
  if (configured && existsSync(configured)) return configured;
  const store = "/nix/store";
  if (!existsSync(store)) return undefined;
  let found: string | undefined;
  for (const entry of readdirSync(store).sort()) {
    if (!entry.includes("javascript-unknown-ghcjs-ghc")) continue;
    const bin = join(store, entry, "bin");
    if (existsSync(bin) && readdirSync(bin).some((f) => /^javascript-unknown-ghcjs-ghc-\d/.test(f))) found = bin;
  }
  return found;
}

/** The `lib` directory GHC wants behind `-B`. */
export function ghcLibdir(bindir: string): string {
  const root = dirname(bindir);
  const lib = join(root, "lib");
  const versioned = readdirSync(lib).find((f) => f.startsWith("javascript-unknown-ghcjs-ghc-"));
  return versioned ? join(lib, versioned, "lib") : lib;
}
