#!/usr/bin/env node
/**
 * `ghc-js` — GHC's JavaScript backend, driven from node.
 *
 * Flags and source files pass straight through to GHC, so anything you would
 * write after `ghc` works here:
 *
 *   ghc-js Main.hs                       compile and link to Main.jsexe
 *   ghc-js -O2 -o app Main.hs            same, named
 *   ghc-js -c Foo.hs Bar.hs              compile only
 *   ghc-js -package-db <db> -isrc Main.hs
 *
 * Two flags are our own:
 *   --ghc-js-version   what this is, and where its pieces live
 *   --ghc-js-libdir <dir>
 */
import { bundledCompiler, findGhcJs, ghcLibdir } from "./find-ghc.js";
import { compile } from "./compiler.js";

const argv = process.argv.slice(2);

if (argv.length === 0 || argv[0] === "--help" || argv[0] === "-h") {
  console.log(
    [
      "ghc-js — GHC's JavaScript backend, running on node",
      "",
      "  ghc-js [ghc flags] <source.hs>...",
      "",
      "GHC's flags pass straight through, `-c` included.",
      "",
      "  --ghc-js-version        what this is, and where its pieces live",
      "  --ghc-js-libdir <dir>   use another GHC libdir",
      "",
      "Package databases come from GHC_PACKAGE_PATH, as with ghc.",
    ].join("\n"),
  );
  process.exit(argv.length === 0 ? 2 : 0);
}

if (argv[0] === "--ghc-js-version") {
  const bundled = bundledCompiler();
  const bindir = findGhcJs();
  console.log(`ghc-js`);
  console.log(`  compiler  ${bundled?.ghc ?? "(not built — run `node build/build-compiler.mjs`)"}`);
  console.log(`  libdir    ${bundled?.libdir ?? (bindir ? ghcLibdir(bindir) : "(none)")}`);
  process.exit(0);
}

const libdirAt = argv.indexOf("--ghc-js-libdir");
const libdir = libdirAt === -1 ? undefined : argv[libdirAt + 1];
const args = libdirAt === -1 ? argv : [...argv.slice(0, libdirAt), ...argv.slice(libdirAt + 2)];

const result = await compile({ args, libdir });
process.exit(result.code);
