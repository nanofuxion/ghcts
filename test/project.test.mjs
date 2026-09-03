import { deepStrictEqual, ok } from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { Vfs } from "../playground/vfs.mjs";
import { findEntry, mountDirectory, parseCabal } from "../playground/project.mjs";

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
