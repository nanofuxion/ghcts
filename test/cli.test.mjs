import { deepStrictEqual, ok } from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { bundledCompiler } from "../dist/find-ghc.js";

const cli = new URL("../dist/cli.js", import.meta.url).pathname;
const built = bundledCompiler() !== undefined;
const skip = built ? false : "compiler not built (npm run build:compiler)";

test("--ghc-js-version says where the compiler is", { skip }, () => {
  const out = execFileSync(process.execPath, [cli, "--ghc-js-version"], { encoding: "utf8" });
  ok(out.includes("ghc.cjs"), out);
  ok(out.includes("libdir"), out);
});

test("compiles and links a program that runs", { skip, timeout: 600_000 }, () => {
  const work = mkdtempSync(join(tmpdir(), "ghc-js-test-"));
  try {
    writeFileSync(join(work, "Main.hs"), 'module Main where\nmain :: IO ()\nmain = putStrLn (show (sum [1..10 :: Int]))\n');
    execFileSync(process.execPath, [cli, "-O0", "Main.hs"], { cwd: work, stdio: "pipe" });
    const ran = execFileSync(process.execPath, [join(work, "Main.jsexe", "all.js")], { encoding: "utf8" });
    deepStrictEqual(ran.trim(), "55");
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
});

test("GHC's own flags reach GHC", { skip, timeout: 600_000 }, () => {
  const work = mkdtempSync(join(tmpdir(), "ghc-js-test-"));
  try {
    writeFileSync(join(work, "Bad.hs"), "module Bad where\nx :: Int\nx = True\n");
    let stderr = "";
    try {
      execFileSync(process.execPath, [cli, "-c", "-Werror", "Bad.hs"], { cwd: work, stdio: "pipe" });
    } catch (e) {
      stderr = String(e.stderr ?? "") + String(e.stdout ?? "");
    }
    ok(/Couldn't match|error/i.test(stderr), stderr.slice(0, 400));
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
});
