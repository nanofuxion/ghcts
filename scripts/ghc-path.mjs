import { existsSync, readdirSync } from "node:fs";
import { join } from "node:path";

export function resolveGhcJs() {
  const configured = process.env.GHCTS_GHC_JS;
  if (configured && existsSync(configured)) return configured;
  const store = "/nix/store";
  if (!existsSync(store)) return undefined;
  for (const entry of readdirSync(store).sort()) {
    if (!entry.includes("javascript-unknown-ghcjs-ghc")) continue;
    const candidate = join(store, entry, "bin", "javascript-unknown-ghcjs-ghc-9.12.2");
    if (existsSync(candidate)) return candidate;
  }
  return undefined;
}
