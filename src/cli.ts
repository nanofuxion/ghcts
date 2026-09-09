#!/usr/bin/env node
/**
 * `ghcts` — GHC's JavaScript backend, driven from node.
 *
 * Flags and source files pass straight through to GHC, so anything you would
 * write after `ghc` works here:
 *
 *   ghcts Main.hs                       compile and link to Main.jsexe
 *   ghcts -O2 -o app Main.hs            same, named
 *   ghcts -c Foo.hs Bar.hs              compile only
 *   ghcts -package-db <db> -isrc Main.hs
 *
 * Two flags are our own:
 *   --ghcts-version   what this is, and where its pieces live
 *   --ghcts-libdir <dir>
 */
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { basename, join, resolve } from "node:path";
import { bundledCompiler, findGhcJs } from "./find-ghc.js";
import { compile } from "./compiler.js";
import { planProject } from "./project.js";

const argv = process.argv.slice(2);

if (argv.length === 0 || argv[0] === "--help" || argv[0] === "-h") {
  console.log(
    [
      "ghcts — GHC's JavaScript backend, running on node",
      "",
      "  ghcts [ghc flags] <source.hs>...",
      "",
      "GHC's flags pass straight through, `-c` included.",
      "",
      "  ghcts --ghcts-project [dir] [ghc flags]",
      "",
      "Project mode reads the directory's .cabal and cabal.project, checks out",
      "each dependency it pins to a git revision, and builds those from source",
      "along with the program. Nothing is prebuilt and nothing is fetched from",
      "Hackage; a dependency's own dependencies come from a package database.",
      "",
      "  --ghcts-version        what this is, and where its pieces live",
      "  --ghcts-libdir <dir>   use another GHC libdir",
      "  --ghcts-project [dir]  build a cabal project and its pinned sources",
      "",
      "Package databases come from GHC_PACKAGE_PATH, as with ghc.",
      "The build needs a GHC JavaScript cross compiler: GHCTS_GHC, then PATH, then ghcup.",
    ].join("\n"),
  );
  process.exit(argv.length === 0 ? 2 : 0);
}

if (argv[0] === "--ghcts-version") {
  const bundled = bundledCompiler();
  const install = findGhcJs();
  console.log(`ghcts`);
  console.log(`  compiler  ${bundled?.ghc ?? "(not built — run `node build/build-compiler.mjs`)"}`);
  console.log(`  libdir    ${bundled?.libdir ?? install?.libdir ?? "(none)"}`);
  console.log(`  ghc       ${install ? `${install.ghc} (${install.version})` : "(none found; set GHCTS_GHC)"}`);
  process.exit(0);
}

/** Pull a `--ghcts-*` flag and its value out of the arguments GHC will see. */
const take = (name: string, hasValue = true): string | undefined => {
  const at = argv.indexOf(name);
  if (at === -1) return undefined;
  const value = hasValue && argv[at + 1] && !argv[at + 1]!.startsWith("-") ? argv[at + 1] : undefined;
  argv.splice(at, value === undefined ? 1 : 2);
  return value ?? "";
};

const libdir = take("--ghcts-libdir");
const project = take("--ghcts-project");

let args = argv;
let plan;
if (project !== undefined) {
  // A pinned dependency is built from source, but its *own* dependencies are
  // ordinary Hackage packages, and those come from the database beside the
  // compiler unless the caller names another.
  const bundledDb = bundledCompiler() && join(bundledCompiler()!.libdir, "..", "pkgs", "package.conf.d");
  const named = argv.flatMap((a, i) => (a === "-package-db" ? [argv[i + 1]!] : []));
  const db = bundledDb && existsSync(bundledDb) && named.length === 0 ? [bundledDb] : named;
  plan = planProject(resolve(project || "."), db);
  args = [...(named.length === 0 ? db.flatMap((d) => ["-package-db", d]) : []), ...plan.args, ...argv, plan.entry];
}

const result = await compile({ args, libdir });
if (result.code !== 0 || !plan) process.exit(result.code);

// GHC links a source dependency's Haskell but not its `js-sources`, so those
// go in front of the program the way its own FFI expects to find them.
const outAt = args.indexOf("-o");
const named = outAt === -1 ? basename(plan.entry).replace(/\.l?hs$/i, "") : args[outAt + 1]!;
const built = join(`${named}.jsexe`, "all.js");
if (plan.jsSources.length && existsSync(built)) {
  const shim = plan.jsSources.map((f) => readFileSync(f, "utf8")).join("\n");
  writeFileSync(built, `${shim}\n${readFileSync(built, "utf8")}`);
}
process.exit(result.code);
