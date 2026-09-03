#!/usr/bin/env node
/**
 * Build the two miso-*native* apps and pack them into Lynx bundles.
 *
 * This is the phone path, not the browser playground: these apps use miso
 * built with `+native`, render through LynxJS rather than the DOM, and end up
 * as `.lynx.bundle` files served to Lynx Explorer. `playground/` is the web
 * path and shares none of this.
 *
 * miso is a package here, not a source tree, so a package database holding a
 * `+native` miso has to be named:
 *
 *   GHC_PACKAGE_PATH="$HOME/.local/state/cabal/store/ghc-9.12.2-9063/package.db:" \
 *     npm run build:lynx
 *
 * The trailing colon appends ghcts's own boot database.
 *
 * Which database, though, is not a detail. misogram's sources track
 * `references/miso`, so they need a miso built from that working tree - a
 * `cabal build` whose project lists `references/miso` as a package, which
 * leaves an inplace database under its `dist-newstyle/packagedb/`. A miso
 * from the cabal store may be an older pin, and then misogram fails on names
 * that pin does not export (`onLayoutMainWith` and friends). The counter is
 * older and builds against either.
 */
import { spawnSync } from "node:child_process";

if (!process.env.GHC_PACKAGE_PATH) {
  console.error(
    "GHC_PACKAGE_PATH is not set, and miso is a package rather than a source tree here.\n\n" +
      '  GHC_PACKAGE_PATH="$(cabal path --store-dir)/ghc-9.12.2-9063/package.db:" npm run build:lynx\n\n' +
      "The database must hold miso built with `+native` from references/miso;\n" +
      "an older store pin fails misogram on names it does not export.\n" +
      "The trailing colon appends ghcts's own boot database.",
  );
  process.exit(2);
}

const run = (cmd, args, opts = {}) => {
  const result = spawnSync(cmd, args, { stdio: "inherit", ...opts });
  if (result.status !== 0) process.exit(result.status ?? 1);
};

/** Compile one app with the ghcts CLI, leaving `<out>/app.jsexe/all.js`. */
const cli = new URL("../dist/cli.js", import.meta.url).pathname;
const compile = ({ cwd, src, main, out }) =>
  run("node", [cli, "-O0", "-XHaskell2010", "-DNATIVE", `-i${src}`, "-outputdir", `${out}/obj`, "-package", "miso", "-o", `${out}/app`, main], { cwd });

compile({ cwd: "references/miso-lynx/examples", src: "counter", main: "counter/Main.hs", out: "dist" });
run("node", ["scripts/pack-lynx.mjs", "--js", "references/miso-lynx/examples/dist/app.jsexe/all.js", "--out", "references/miso-lynx/examples/dist/lynx"]);

compile({ cwd: "references/misogram", src: "src", main: "src/Main.hs", out: "dist" });
run("node", [
  "scripts/pack-lynx.mjs",
  "--js", "references/misogram/dist/app.jsexe/all.js",
  "--out", "references/misogram/dist/lynx",
  "--styles", "references/misogram/styles.css",
  "--assets", "references/misogram/assets",
  "--registry", "__misoGramAssets",
]);
