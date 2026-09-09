import { deepStrictEqual, ok } from "node:assert/strict";
import { test } from "node:test";
import { evalExpr, expand, parseDefine, preprocess } from "../playground/cpp.mjs";

/** The output without its line markers, which is what the Haskell is. */
const body = (r) => r.text.split("\n").filter((l) => !/^# \d+ "/.test(l)).join("\n");

test("evalExpr does C's integer arithmetic and precedence", () => {
  deepStrictEqual(evalExpr("1 + 2 * 3"), 7);
  deepStrictEqual(evalExpr("(1 + 2) * 3"), 9);
  deepStrictEqual(evalExpr("912 >= 900 && !0"), 1);
  deepStrictEqual(evalExpr("0x10 == 16"), 1);
  deepStrictEqual(evalExpr("7 / 2"), 3);
});

test("expand replaces object- and function-like macros, and stops at itself", () => {
  const macros = new Map([parseDefine("TWO 2"), parseDefine("ADD(a,b) ((a)+(b))"), parseDefine("LOOP LOOP + 1")]);
  deepStrictEqual(expand("ADD(TWO, 3)", macros), "((2)+(3))");
  deepStrictEqual(expand("LOOP", macros), "LOOP + 1");
  deepStrictEqual(expand("TWO'", macros), "TWO'", "a Haskell name ending in ' is not the macro");
});

test("preprocess drops the untaken branch and keeps every line number", () => {
  const source = ["module Main where", "#ifdef WASM", "wasmOnly = ()", "#else", "plainOnly = ()", "#endif", "main = pure ()"].join("\n");
  const r = preprocess(source, { path: "Main.hs" });
  deepStrictEqual(r.errors, []);
  deepStrictEqual(body(r).split("\n").slice(0, 7), ["module Main where", "", "", "", "plainOnly = ()", "", "main = pure ()"]);
});

test("preprocess names the real source in its first line marker", () => {
  const r = preprocess("main = pure ()\n", { path: "src/Main.hs" });
  ok(r.text.startsWith('# 1 "src/Main.hs"\n'));
});

test("preprocess follows #include and takes its macros", () => {
  const r = preprocess(['#include "version.h"', "#if __GLASGOW_HASKELL__ >= 900", "new = ()", "#else", "old = ()", "#endif"].join("\n"), {
    path: "Main.hs",
    resolveInclude: (name) => (name === "version.h" ? { path: name, text: "#define __GLASGOW_HASKELL__ 912\n" } : undefined),
  });
  deepStrictEqual(r.errors, []);
  ok(body(r).includes("new = ()"));
  ok(!body(r).includes("old = ()"));
});

test("preprocess joins a macro written across continued lines", () => {
  const r = preprocess(["#define BIG(a,b) \\", "  ((a) + (b))", "x = BIG(1,2)"].join("\n"), { path: "Main.hs" });
  deepStrictEqual(body(r).split("\n")[2], "x = ((1) + (2))");
});

test("preprocess reports #error and an unclosed #if", () => {
  ok(preprocess("#error nope\n", { path: "Main.hs" }).errors[0].endsWith("nope"));
  ok(preprocess("#ifdef X\n", { path: "Main.hs" }).errors[0].includes("unterminated"));
});

test("preprocess takes the first true branch of an #elif chain", () => {
  const r = preprocess(["#if 0", "a", "#elif 1", "b", "#elif 1", "c", "#else", "d", "#endif"].join("\n"), { path: "Main.hs" });
  deepStrictEqual(body(r).split("\n").filter(Boolean), ["b"]);
});
