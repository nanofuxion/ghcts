import { deepStrictEqual, ok } from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { dependencies, evalCondition, extensions, parseCabal, parseCabalProject, withImports, words } from "../dist/cabal.js";

const misoCabal = () => readFileSync(new URL("../references/miso/miso.cabal", import.meta.url), "utf8");
const library = (text) => {
  const stanzas = parseCabal(text);
  return withImports(stanzas, stanzas.find((s) => s.type === "library"));
};

test("evalCondition reads the tests a .cabal actually uses", () => {
  const cond = { arch: "javascript", flags: new Set(["native"]) };
  ok(evalCondition("arch(javascript)", cond));
  ok(!evalCondition("arch(wasm32)", cond));
  ok(evalCondition("flag(native)", cond));
  ok(!evalCondition("flag(production)", cond));
  ok(!evalCondition("impl(ghcjs)", cond), "this compiler is GHC, never ghcjs");
  ok(evalCondition("impl(ghcjs) || arch(javascript)", cond));
  ok(!evalCondition("!flag(native)", cond));
  ok(evalCondition("!impl(ghcjs) && arch(javascript)", cond));
});

test("parseCabal takes one branch of an if/elif/else chain", () => {
  const [stanza] = parseCabal(
    [
      "library",
      "  if impl(ghcjs)",
      "    cpp-options: -DOLD",
      "  elif arch(javascript)",
      "    cpp-options: -DNEW",
      "  elif arch(wasm32)",
      "    cpp-options: -DWASM",
      "  else",
      "    cpp-options: -DVANILLA",
      "  hs-source-dirs: src",
    ].join("\n"),
  );
  deepStrictEqual(words(stanza, "cpp-options"), ["-DNEW"]);
  deepStrictEqual(words(stanza, "hs-source-dirs"), ["src"], "a field after the chain is not inside it");
});

test("withImports folds in the common blocks a stanza imports", () => {
  const stanzas = parseCabal(
    ["common cpp", "  cpp-options: -DSHARED", "", "library", "  import: cpp", "  hs-source-dirs: src"].join("\n"),
  );
  const lib = withImports(stanzas, stanzas.find((s) => s.type === "library"));
  deepStrictEqual(words(lib, "cpp-options"), ["-DSHARED"]);
  deepStrictEqual(words(lib, "hs-source-dirs"), ["src"]);
});

test("miso's own cabal reads as the JavaScript build it is", () => {
  const lib = library(misoCabal());
  deepStrictEqual(words(lib, "hs-source-dirs"), ["ffi/js", "src"], "not ffi/ghc, and not ffi/wasm");
  deepStrictEqual(words(lib, "cpp-options"), ["-DGHCJS_BOTH", "-DGHCJS_NEW"]);
  deepStrictEqual(words(lib, "js-sources"), ["js/miso.js"]);
  ok(dependencies(lib).includes("ghcjs-base"));
});

test("extensions turns default-language and default-extensions into -X flags", () => {
  const [stanza] = parseCabal(
    ["executable app", "  main-is: Main.hs", "  default-language: GHC2021", "  default-extensions:", "    LambdaCase", "    CPP"].join("\n"),
  );
  deepStrictEqual(extensions(stanza), ["-XGHC2021", "-XLambdaCase", "-XCPP"]);
});

test("parseCabalProject reads packages and the revisions it pins", () => {
  const { packages, pins } = parseCabalProject(
    [
      "packages:",
      "  .",
      "  ./sub",
      "",
      "source-repository-package",
      "  type: git",
      "  location: https://github.com/dmjio/miso",
      "  tag: 1.13.0",
    ].join("\n"),
  );
  deepStrictEqual(packages, [".", "./sub"]);
  deepStrictEqual(pins, [{ location: "https://github.com/dmjio/miso", tag: "1.13.0", subdir: undefined, name: "miso" }]);
});

test("packageNames reads what a database holds", async () => {
  const { packageNames } = await import("../dist/project.js");
  const db = new URL("../dist/lib/package.conf.d", import.meta.url).pathname;
  const names = packageNames(db);
  ok(names.has("base"), "the boot database has base");
  ok(!names.has("nothing-of-the-sort"));
  deepStrictEqual([...packageNames("/no/such/database")], []);
});
