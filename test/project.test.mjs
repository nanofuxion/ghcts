import { deepStrictEqual, ok } from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { Vfs } from "../playground/vfs.mjs";
import { findEntry, haskellSources, importedModules, mountDirectory, mountGitHub, neededPackages, parseCabal, parseGitHubUrl, pinnedMiso, usesTemplateHaskell } from "../playground/project.mjs";

const enc = (s) => new TextEncoder().encode(s);

test("parseCabal reads a real sample-app executable stanza", () => {
  const text = readFileSync(new URL("../references/miso/sample-app/app.cabal", import.meta.url), "utf8");
  const [exe] = parseCabal(text);
  deepStrictEqual(exe.mainIs, "Main.hs");
  deepStrictEqual(exe.hsSourceDirs, ["."]);
  ok(exe.dependencies.includes("miso"));
});

test("parseCabal reads misogram's hs-source-dirs", () => {
  const text = readFileSync(new URL("../references/misogram/miso-gram.cabal", import.meta.url), "utf8");
  const [exe] = parseCabal(text);
  deepStrictEqual(exe.mainIs, "Main.hs");
  deepStrictEqual(exe.hsSourceDirs, ["src"]);
  deepStrictEqual(exe.dependencies, ["base", "miso", "mtl", "containers"]);
});

test("parseCabal strips version constraints from build-depends", () => {
  const [exe] = parseCabal(
    ["executable app", "  main-is:", "    Main.hs", "  build-depends:", "    base >= 4 && < 5, text, containers ^>= 0.7"].join("\n"),
  );
  deepStrictEqual(exe.dependencies, ["base", "text", "containers"]);
});

test("parseCabal does not see a field written only inside an if-block as the stanza's own", () => {
  // Best-effort parser: this documents the limitation rather than hiding it.
  const [exe] = parseCabal(["executable app", "  main-is:", "    Main.hs", "  if os(darwin)", "    ghc-options: -threaded"].join("\n"));
  ok(exe.mainIs === "Main.hs");
});

/** A minimal stand-in for FileSystemDirectoryHandle: entries()/getFile()/kind. */
function fakeDir(tree) {
  return {
    kind: "directory",
    async *entries() {
      for (const [name, value] of Object.entries(tree)) {
        yield [name, typeof value === "string" ? fakeFile(name, value) : fakeDir(value)];
      }
    },
  };
}
function fakeFile(name, text) {
  return {
    kind: "file",
    async getFile() {
      return { name, lastModified: 0, async arrayBuffer() { return enc(text).buffer; } };
    },
  };
}

test("mountDirectory copies a fake picked folder into the VFS and keeps handles", async () => {
  const vfs = new Vfs();
  const tree = fakeDir({
    "app.cabal": "executable app\n  main-is:\n    Main.hs\n  build-depends:\n    base, miso\n",
    src: { "Main.hs": "module Main where\nmain = pure ()\n" },
    ".git": { HEAD: "ref: refs/heads/main\n" },
  });
  const { count, handles } = await mountDirectory(vfs, tree, "/project");
  deepStrictEqual(new TextDecoder().decode(vfs.readFile("/project/src/Main.hs")), "module Main where\nmain = pure ()\n");
  ok(handles.has("/project/src/Main.hs"));
  ok(!vfs.lookup("/project/.git"), "dotfiles are not mounted");
  deepStrictEqual(count, 2);
});

test("findEntry follows a mounted project's own .cabal file", async () => {
  const vfs = new Vfs();
  await mountDirectory(
    vfs,
    fakeDir({
      "miso-gram.cabal": readFileSync(new URL("../references/misogram/miso-gram.cabal", import.meta.url), "utf8"),
      src: { "Main.hs": "module Main where\n" },
    }),
    "/project",
  );
  const found = findEntry(vfs, "/project");
  deepStrictEqual(found.entry, "src/Main.hs");
  deepStrictEqual(found.includeDirs, ["src"]);
  ok(found.usesMiso);
});

test("findEntry falls back to ghcts.json, then to conventional paths", () => {
  const vfs = new Vfs();
  vfs.mkdirp("/a");
  vfs.writeFile("/a/ghcts.json", enc(JSON.stringify({ sourceRoots: ["src"], entry: { module: "Main" }, dependencies: ["miso"] })));
  vfs.mkdirp("/a/src");
  vfs.writeFile("/a/src/Main.hs", enc("module Main where\n"));
  const found = findEntry(vfs, "/a");
  deepStrictEqual(found.entry, "src/Main.hs");
  ok(found.usesMiso);

  const vfs2 = new Vfs();
  vfs2.mkdirp("/b/app");
  vfs2.writeFile("/b/app/Main.hs", enc("module Main where\n"));
  const found2 = findEntry(vfs2, "/b");
  deepStrictEqual(found2.entry, "app/Main.hs");
  deepStrictEqual(found2.includeDirs, ["app"]);
  ok(!found2.usesMiso);
});

test("findEntry returns undefined when nothing looks like a program", () => {
  const vfs = new Vfs();
  vfs.mkdirp("/empty");
  deepStrictEqual(findEntry(vfs, "/empty"), undefined);
});

/** The shape pack-assets.mjs writes to playground/assets/pkgs.json. */
const INDEX = {
  expose: ["miso", "random"],
  boot: ["containers", "mtl"],
  modules: { Miso: "miso", "Miso.Random": "miso", "System.Random": "random", "Data.Map": "containers", "Data.Map.Strict": "containers" },
};

test("importedModules reads plain, qualified and dotted imports", () => {
  const text = ["module Main where", "import Data.List", "import qualified Data.Map as M", "import System.Random (randomRIO)", "  import NotAnImport"].join("\n");
  deepStrictEqual(importedModules(text), ["Data.List", "Data.Map", "System.Random"]);
});

test("neededPackages picks up a lone file's imports, with no .cabal at all", () => {
  deepStrictEqual(neededPackages(["module Main where\nimport System.Random\n"], [], INDEX), ["random"]);
});

test("neededPackages takes build-depends the database has, and ignores the rest", () => {
  deepStrictEqual(neededPackages([], ["base", "containers", "miso", "mtl"], INDEX), ["containers", "miso", "mtl"]);
});

test("neededPackages says nothing is needed for a Prelude-only program", () => {
  deepStrictEqual(neededPackages(["module Main where\nimport Data.List\nmain = pure ()\n"], ["base"], INDEX), []);
});

test("haskellSources reads every .hs under the root, and nothing else", () => {
  const vfs = new Vfs();
  vfs.mkdirp("/p/src");
  vfs.writeFile("/p/src/Main.hs", enc("import Miso\n"));
  vfs.writeFile("/p/src/Cards.hs", enc("import Data.Map\n"));
  vfs.writeFile("/p/README.md", enc("import System.Random\n"));
  deepStrictEqual(neededPackages(haskellSources(vfs, "/p"), [], INDEX).sort(), ["containers", "miso"]);
});

test("parseCabal turns default-language and default-extensions into -X flags", () => {
  const [exe] = parseCabal(
    ["executable app", "  main-is: Main.hs", "  default-language: GHC2021", "  default-extensions:", "    LambdaCase", "    OverloadedStrings"].join("\n"),
  );
  deepStrictEqual(exe.extensions, ["-XGHC2021", "-XLambdaCase", "-XOverloadedStrings"]);
});

test("parseGitHubUrl reads the forms people actually paste", () => {
  deepStrictEqual(parseGitHubUrl("https://github.com/haskell-miso/mario"), { owner: "haskell-miso", repo: "mario", ref: "HEAD", dir: "" });
  deepStrictEqual(parseGitHubUrl("haskell-miso/mario"), { owner: "haskell-miso", repo: "mario", ref: "HEAD", dir: "" });
  deepStrictEqual(parseGitHubUrl("github.com/dmjio/miso.git"), { owner: "dmjio", repo: "miso", ref: "HEAD", dir: "" });
  deepStrictEqual(parseGitHubUrl("https://github.com/a/b/tree/main/sample-app"), { owner: "a", repo: "b", ref: "main", dir: "sample-app" });
  deepStrictEqual(parseGitHubUrl("not a url"), undefined);
});

test("mountGitHub takes the sources and leaves the rest behind", async () => {
  const tree = [
    { type: "blob", path: "app.cabal" },
    { type: "blob", path: "src/Main.hs" },
    { type: "blob", path: "docs/table.png" },
    { type: "tree", path: "src" },
  ];
  const fetched = [];
  const original = globalThis.fetch;
  globalThis.fetch = async (url) => {
    fetched.push(url);
    if (url.startsWith("https://api.github.com/")) return { ok: true, json: async () => ({ tree }) };
    return { ok: true, arrayBuffer: async () => enc(`-- ${url}`).buffer };
  };
  try {
    const vfs = new Vfs();
    const { count } = await mountGitHub(vfs, { owner: "o", repo: "r", ref: "HEAD", dir: "" }, "/project");
    deepStrictEqual(count, 2);
    ok(vfs.lookup("/project/src/Main.hs"));
    ok(!vfs.lookup("/project/docs/table.png"), "a png is not something the compiler reads");
    deepStrictEqual(fetched.filter((u) => u.startsWith("https://api.github.com/")).length, 1, "the rate-limited endpoint is asked once");
  } finally {
    globalThis.fetch = original;
  }
});

test("usesTemplateHaskell sees the pragma and the cabal extension", () => {
  ok(usesTemplateHaskell(["{-# LANGUAGE TemplateHaskell #-}\nmodule Model where\n"]));
  ok(usesTemplateHaskell([], ["-XGHC2021", "-XQuasiQuotes"]));
  ok(!usesTemplateHaskell(["{-# LANGUAGE OverloadedStrings #-}\n"], ["-XLambdaCase"]));
});

test("pinnedMiso reads a cabal.project's source-repository-package tag", () => {
  const vfs = new Vfs();
  vfs.mkdirp("/p");
  vfs.writeFile(
    "/p/cabal.project",
    enc(["packages: .", "", "source-repository-package", "  type: git", "  location: https://github.com/dmjio/miso", "  tag: 1.13.0"].join("\n")),
  );
  deepStrictEqual(pinnedMiso(vfs, "/p"), "1.13.0");

  const bare = new Vfs();
  bare.mkdirp("/p");
  bare.writeFile("/p/cabal.project", enc("packages: .\n"));
  deepStrictEqual(pinnedMiso(bare, "/p"), undefined);
});
