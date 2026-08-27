import {
  cp,
  mkdir,
  readFile,
  readdir,
  stat,
  writeFile,
} from "node:fs/promises";
import { dirname, join, resolve } from "node:path";
import ts from "typescript";
import type { Declaration, Expr, LocalBinding, Module, Pattern } from "./ast.js";
import { error } from "./diagnostics.js";
import { bootModuleSource } from "./boot.js";
import { parseCabalLibrary } from "./cabal.js";
import { parseModule, type ParsedModule } from "./parser.js";
import { checkModules } from "./typecheck.js";
import { lowerModules } from "./core-legacy.js";
import { classMembers, instanceHead, instanceMethodValues } from "./dictionary.js";
import * as Syntax from "./js/syntax.js";
import * as Ppr from "./js/ppr.js";
import type {
  CompileProjectOptions,
  CompileResult,
  Diagnostic,
  GhctsConfig,
  Target,
} from "./types.js";
const packageRoot = dirname(dirname(new URL(import.meta.url).pathname));

// GHCJS exposes StaticKey as a 128-bit hexadecimal fingerprint.  The key is
// part of the cross-thread protocol, so descriptive strings are not valid:
// Miso serializes this value and looks it up as a Fingerprint hex string.
function staticPointerKey(moduleName: string, offset: number): string {
  let a = 0x811c9dc5;
  let b = 0x9e3779b9;
  const input = `${moduleName}:${offset}`;
  for (let i = 0; i < input.length; i++) {
    const c = input.charCodeAt(i);
    a = Math.imul(a ^ c, 0x01000193) >>> 0;
    b = Math.imul(b ^ (c + i), 0x85ebca6b) >>> 0;
  }
  return [a, b, a ^ b, Math.imul(a, b)].map((word) => (word >>> 0).toString(16).padStart(8, "0")).join("");
}
function staticPointerWords(key: string): [number, number, number, number] {
  return [0, 1, 2, 3].map((index) => Number.parseInt(key.slice(index * 8, index * 8 + 8), 16)) as [number, number, number, number];
}

async function readConfig(
  project: string,
): Promise<{ config?: GhctsConfig; diagnostics: Diagnostic[] }> {
  const file = join(project, "ghcts.json");
  try {
    const c = JSON.parse(await readFile(file, "utf8")) as Partial<GhctsConfig>;
    if (
      c.version !== 1 ||
      !Array.isArray(c.sourceRoots) ||
      !c.entry?.module ||
      !c.entry.export ||
      !Array.isArray(c.targets) ||
      !c.outDir
    )
      throw new Error(
        "must contain version: 1, sourceRoots, entry, targets, and outDir",
      );
    if (c.targets.some((target) => target !== "browser" && target !== "node"))
      throw new Error("targets must contain only browser or node");
    if (c.cpp && !Array.isArray(c.cpp)) throw new Error("cpp must be an array of CPP symbols");
    return { config: c as GhctsConfig, diagnostics: [] };
  } catch (cause) {
    return {
      diagnostics: [
        error(
          "E_CONFIG",
          `Cannot load ghcts.json: ${cause instanceof Error ? cause.message : String(cause)}`,
          file,
        ),
      ],
    };
  }
}
async function walk(root: string): Promise<string[]> {
  const entries = await readdir(root, { withFileTypes: true });
  return (
    await Promise.all(
      entries.map((entry) =>
        entry.isDirectory()
          ? walk(join(root, entry.name))
          : [join(root, entry.name)],
      ),
    )
  )
    .flat()
    .filter((path) => path.endsWith(".hs"));
}
async function exists(path: string) {
  try {
    return (await stat(path)).isDirectory();
  } catch {
    return false;
  }
}
/** Locate a checked-in dependency when running the repository fixtures.  npm
 * releases will replace this narrow development source with lockfile roots. */
async function dependencyRoots(
  project: string,
  dependencies: string[] | undefined,
): Promise<string[]> {
  const roots: string[] = [];
  for (const dependency of dependencies ?? []) {
    let cursor = project;
    while (true) {
      const candidate = join(cursor, "references", dependency);
      if (await exists(candidate)) {
        // Resolve local packages through their Cabal library stanza.  The
        // fallback retains the repository's FFI source tree, which is not a
        // Cabal hs-source-dir but contains real Haskell FFI modules.
        try {
          const cabal = parseCabalLibrary(
            await readFile(join(candidate, `${dependency}.cabal`), "utf8"),
          );
          roots.push(
            ...cabal.sourceDirs.map((sourceDir) => join(candidate, sourceDir)),
          );
        } catch {
          roots.push(join(candidate, "src"));
        }
        roots.push(join(candidate, "ffi", "js"));
        break;
      }
      const parent = dirname(cursor);
      if (parent === cursor) break;
      cursor = parent;
    }
  }
  return roots;
}
function cppDefines(config: GhctsConfig): Set<string> {
  const defines = new Set(["GHCJS_BOTH", "GHCJS_NEW"]);
  for (const flag of config.cpp ?? []) {
    const symbol = flag.replace(/^-D/, "");
    if (symbol) defines.add(symbol);
  }
  return defines;
}
async function jsSources(
  project: string,
  dependencies: string[] | undefined,
  defines: ReadonlySet<string>,
): Promise<string[]> {
  const assets: string[] = [];
  for (const dependency of dependencies ?? []) {
    let cursor = project;
    while (true) {
      const directory = join(cursor, "references", dependency, "js");
      // Mirrors Cabal's `common client` js-sources selection: native and
      // production are independent flags, each picking a `.prod` variant.
      const native = defines.has("NATIVE");
      const production = defines.has("PRODUCTION");
      const names = native
        ? production
          ? [`${dependency}-native.prod.js`, `${dependency}-native.js`, `${dependency}.js`]
          : [`${dependency}-native.js`, `${dependency}.js`]
        : production
          ? [`${dependency}.prod.js`, `${dependency}.js`]
          : [`${dependency}.js`];
      let found: string | undefined;
      for (const name of names) {
        const asset = join(directory, name);
        try {
          if ((await stat(asset)).isFile()) {
            found = asset;
            break;
          }
        } catch {
          /* try next name */
        }
      }
      if (found) {
        assets.push(found);
        break;
      }
      const parent = dirname(cursor);
      if (parent === cursor) break;
      cursor = parent;
    }
  }
  return assets;
}
async function loadModules(
  project: string,
  config: GhctsConfig,
): Promise<{ modules: Map<string, ParsedModule>; diagnostics: Diagnostic[] }> {
  const modules = new Map<string, ParsedModule>();
  const diagnostics: Diagnostic[] = [];
  // Cabal's default browser branch for Miso defines these two CPP symbols.
  // They are deliberately passed through the ordinary lexer/parser, rather
  // than selecting a compiler-owned Miso implementation.
  // Miso's JS Cabal stanza always defines these; they select the GHCJS_NEW
  // arrow FFI (`(($1) => ...)`) instead of the older `$r = ...` dialect.
  // Node and browser are both that JS backend, so both need the same macros.
  // Extra symbols (e.g. NATIVE) come from ghcts.json `cpp`, matching Cabal
  // `-D` flags rather than a compiler-owned Lynx path.
  const defines = cppDefines(config);
  const addSource = (source: string, file: string) => {
    const parsed = parseModule(source, file, defines);
    diagnostics.push(...parsed.diagnostics);
    if (parsed.module) {
      const previous = modules.get(parsed.module.ast.name);
      if (previous && previous.file !== file)
        diagnostics.push(
          error(
            "E_DUPLICATE_MODULE",
            `Duplicate module ${parsed.module.ast.name}`,
            file,
          ),
        );
      else modules.set(parsed.module.ast.name, parsed.module);
    }
  };
  const add = async (file: string) =>
    addSource(await readFile(file, "utf8"), file);
  for (const sourceRoot of config.sourceRoots) {
    try {
      for (const file of await walk(resolve(project, sourceRoot)))
        await add(file);
    } catch {
      diagnostics.push(
        error(
          "E_SOURCE_ROOT",
          `Cannot read source root ${sourceRoot}`,
          join(project, "ghcts.json"),
        ),
      );
    }
  }
  const roots = await dependencyRoots(project, config.dependencies);
  const queue = [...modules.values()];
  const considered = new Set<string>();
  while (queue.length) {
    const module = queue.shift()!;
    for (const declaration of module.ast.imports) {
      const imported = declaration.module;
      if (
        imported === "Prelude" ||
        modules.has(imported) ||
        considered.has(imported)
      )
        continue;
      considered.add(imported);
      let file: string | undefined;
      for (const root of roots) {
        const candidate = join(root, ...imported.split(".")) + ".hs";
        try {
          await stat(candidate);
          file = candidate;
          break;
        } catch {
          /* next package root */
        }
      }
      if (file) {
        await add(file);
        const loaded = modules.get(imported);
        if (loaded) queue.push(loaded);
      } else {
        const source = bootModuleSource(imported);
        if (source) {
          addSource(source, `<ghcts:boot/${imported}>`);
          const loaded = modules.get(imported);
          if (loaded) queue.push(loaded);
        }
      }
    }
  }
  for (const module of modules.values())
    for (const declaration of module.ast.imports)
      if (declaration.module !== "Prelude" && !modules.has(declaration.module))
        diagnostics.push(
          error(
            "E_IMPORT",
            `Cannot resolve module ${declaration.module}; add a project source root or a resolved package dependency`,
            module.file,
          ),
        );
  return { modules, diagnostics };
}

const builtin: Record<string, string> = {
  "+": "prelude.add",
  "-": "prelude.subtract",
  subtract: "prelude.subtractFunction",
  "*": "prelude.multiply",
  "/": "prelude.divide",
  ":": "prelude.cons",
  "&&": "prelude.and",
  "||": "prelude.or",
  otherwise: "prelude.otherwise",
  True: "prelude.true",
  False: "prelude.false",
  Nothing: "prelude.nothing",
  Just: "prelude.just",
  Left: "prelude.left",
  Right: "prelude.right",
  not: "prelude.not",
  "==": "prelude.equal",
  "/=": "prelude.notEqual",
  "<>": "prelude.append",
  mempty: "prelude.empty",
  "M.empty": "prelude.empty",
  parseJSON: "prelude.parseJSON",
  toJSON: "prelude.toJSON",
  forM_: "prelude.forM_",
  forM: "prelude.forM",
  reverse: "prelude.reverse",
  drop: "prelude.drop",
  dropWhile: "prelude.dropWhile",
  "S.Empty": "force(v_Data_2e_Sequence_2e_Empty)",
  "S.:<|": "force(v_Data_2e_Sequence_2e_Cons)",
  "S.empty": "force(v_Data_2e_Sequence_2e_Empty)",
  emptyQueue: "prelude.emptyQueue",
  forever: "prelude.forever",
  "foldl'": "prelude.foldlPrime",
  null: "prelude.isNull",
  length: "prelude.length",
  mconcat: "prelude.concat",
  "<|>": "prelude.alternative",
  "<$": "prelude.replace",
  "<*": "prelude.keepLeft",
  "<*>": "prelude.applyF",
  "*>": "prelude.keepRight",
  "++": "prelude.appendList",
  "!!": "prelude.index",
  "Prelude.!!": "prelude.index",
  "Data.List.!!": "prelude.index",
  "(,)": "prelude.pair",
  concat: "prelude.flatten",
  "<": "prelude.less",
  ">": "prelude.greater",
  "<=": "prelude.lessEqual",
  ">=": "prelude.greaterEqual",
  putStrLn: "prelude.putStrLn",
  error: "prelude.error",
  round: "prelude.round",
  pure: "prelude.pure",
  return: "prelude.pure",
  ">>=": "prelude.bind",
  ">>": "prelude.then",
  map: "prelude.map",
  mapM_: "prelude.mapM_",
  sequence_: "prelude.sequence_",
  maybe: "prelude.maybe",
  either: "prelude.either",
  foldr: "prelude.foldr",
  fromIntegral: "prelude.fromIntegral",
  realToFrac: "prelude.realToFrac",
  isNaN: "prelude.isNaN",
  fst: "prelude.fst",
  snd: "prelude.snd",
  last: "prelude.last",
  init: "prelude.init",
  toList: "prelude.toList",
  isSpace: "prelude.isSpace",
  traverse: "prelude.traverse",
  show: "prelude.show",
  ord: "prelude.ord",
  sum: "prelude.sum",
  fromEnum: "prelude.fromEnum",
  elem: "prelude.elem",
  filter: "prelude.filter",
  div: "prelude.div",
  mod: "prelude.mod",
  quot: "prelude.quot",
  rem: "prelude.rem",
  quotRem: "prelude.quotRem",
  even: "prelude.even",
  odd: "prelude.odd",
  min: "prelude.min",
  max: "prelude.max",
  minBound: "prelude.minBound",
  maxBound: "prelude.maxBound",
  succ: "prelude.succ",
  pred: "prelude.pred",
  divMod: "prelude.divMod",
  any: "prelude.any",
  concatMap: "prelude.concatMap",
  negate: "prelude.negate",
  zip: "prelude.zip",
  enumFrom: "prelude.enumFrom",
  enumFromTo: "prelude.enumFromTo",
  enumFromThen: "prelude.enumFromThen",
  enumFromThenTo: "prelude.enumFromThenTo",
  mapM: "prelude.mapM",
  sequence: "prelude.sequence",
  traverse_: "prelude.traverse_",
  uncurry: "prelude.uncurry",
  seq: "prelude.seq",
  "|>": "prelude.pipe",
  $: "prelude.dollar",
  "=<<": "prelude.bindFlip",
  "<$>": "prelude.fmap",
  fmap: "prelude.fmap",
  "Prelude.fmap": "prelude.fmap",
  "Data.Functor.fmap": "prelude.fmap",
  ".": "prelude.compose",
  id: "prelude.id",
  undefined: "prelude.undefined",
  toJSVal: "prelude.toJSVal",
  fromJSVal: "prelude.fromJSVal",
  fromJSValUnchecked: "prelude.fromJSValUnchecked",
  static: "prelude.staticPtr",
  deRefStaticPtr: "prelude.deRefStaticPtr",
  "GHC.StaticPtr.deRefStaticPtr": "prelude.deRefStaticPtr",
  staticKey: "prelude.staticKey",
  "GHC.StaticPtr.staticKey": "prelude.staticKey",
  unsafeLookupStaticPtr: "prelude.unsafeLookupStaticPtr",
  "GHC.StaticPtr.unsafeLookupStaticPtr": "prelude.unsafeLookupStaticPtr",
  readMaybe: "prelude.readMaybe",
  "Text.Read.readMaybe": "prelude.readMaybe",
  toObject: "prelude.toObject",
  toArgs: "prelude.toArgs",
  liftIO: "prelude.liftIO",
  flip: "prelude.flip",
  const: "prelude.constValue",
};
interface EmitScope {
  module: string;
  names: ReadonlyMap<string, string>;
  definedNames: ReadonlySet<string>;
  definesValue: ReadonlySet<string>;
  constructors: ReadonlyMap<string, Array<{ name: string; arity: number }>>;
  signatures: ReadonlyMap<string, string>;
  recordFields: ReadonlyMap<string, string[]>;
  emittedJs: Set<string>;
  staticSites: Array<{ key: string; value: Syntax.JExpr }>;
}
function isIOResultType(type: string | undefined): boolean {
  if (!type) return false;
  const stripped = type.replace(/^forall\b[^.]*\.\s*/i, "").trim();
  return /^IO\b/.test(stripped);
}
function constructorFieldOrder(
  constructor: string,
  recordFields: ReadonlyMap<string, string[]>,
): string[] | undefined {
  const unqualified = constructor.split(".").at(-1) ?? constructor;
  return recordFields.get(constructor) ?? recordFields.get(unqualified);
}
function constructorTag(name: string) {
  if (name === "S.:<|" || name === "S.Cons" || name.endsWith(".:<|")) return "Cons";
  return name.split(".").at(-1) ?? name;
}
let patternTemporary = 0;
function jsName(name: string) {
  return `v_${name.replace(/[^A-Za-z0-9_]/g, (char) => `_${char.codePointAt(0)?.toString(16)}_`)}`;
}
// GHC.JS.Syntax closures are printed as ordinary function expressions.
// Keep generated Haskell closures in that ABI shape instead of using arrows.
//
// Every function below builds real src/js/syntax.ts AST nodes - no RawStat/
// RawExpr is used anywhere in this file. That includes `throw` (as
// ThrowStat, a documented TS-only addition since GHC's own Syntax.hs has no
// throw constructor at all), the Miso.Native `[js| |]` FFI quasiquote body
// (parsed with the TypeScript compiler and translated into the same AST -
// see translateFfiBody below emitExpr), and source-derived annotations that
// carry no executable meaning - a signature, a rejected-declaration note -
// which become a real `void "<text>"` statement (jVoidNote) rather than a
// comment, since GHC.JS.Syntax has no comment node either but does have a
// genuine VoidOp. The ES module import/export wrapper in `lower()` is the
// one piece built from a different AST entirely (TypeScript's own factory/
// printer, not GHC.JS.Syntax's), since ES module syntax was never part of
// GHC.JS.Syntax's grammar to begin with - that's GHC.StgToJS.Linker's job,
// a different subsystem.
const jVar = (name: string): Syntax.JExpr => ({ tag: "ValExpr", value: { tag: "JVar", ident: name } });
const jStr = (value: string): Syntax.JExpr => ({ tag: "ValExpr", value: { tag: "JStr", value } });
const jInt = (value: number | bigint): Syntax.JExpr => ({ tag: "ValExpr", value: { tag: "JInt", value: BigInt(value) } });
/** GHC.JS.Syntax's JVal keeps JInt (Integer) and JDouble (Double) separate;
 * ghcts's "int"-tagged expr/pattern nodes carry a plain JS number that may
 * not actually be whole (e.g. a numeric literal like 0.3), so route it to
 * whichever JVal variant it can actually represent. */
const jNumber = (value: number): Syntax.JExpr => (Number.isInteger(value) ? jInt(value) : { tag: "ValExpr", value: { tag: "JDouble", value } });
const jBool = (value: boolean): Syntax.JExpr => ({ tag: "ValExpr", value: { tag: "JBool", value } });
const jList = (values: Syntax.JExpr[]): Syntax.JExpr => ({ tag: "ValExpr", value: { tag: "JList", values } });
const jSel = (obj: Syntax.JExpr, field: string): Syntax.JExpr => ({ tag: "SelExpr", obj, field });
const jCall = (fn: Syntax.JExpr, args: Syntax.JExpr[]): Syntax.JExpr => ({ tag: "ApplExpr", fn, args });
const jCallStat = (fn: Syntax.JExpr, args: Syntax.JExpr[]): Syntax.JStat => ({ tag: "ApplStat", fn, args });
const jFunc = (parameters: string[], body: Syntax.JStat): Syntax.JExpr => ({ tag: "ValExpr", value: { tag: "JFunc", args: parameters, body } });
/** A function expression whose body is exactly `return <expr>;` - matches
 * the old jsFunction helper's ABI (a JFunc, never an arrow function: GHC.JS
 * never emits arrows). */
const jFuncExpr = (parameters: string[], body: Syntax.JExpr): Syntax.JExpr => jFunc(parameters, jBlock([jReturn(body)]));
const jNot = (value: Syntax.JExpr): Syntax.JExpr => ({ tag: "UOpExpr", op: "NotOp", value });
const jBlock = (stats: Syntax.JStat[]): Syntax.JStat => ({ tag: "BlockStat", stats });
/** GHC.JS.Syntax has no comment node, so a Haskell-source annotation (a
 * signature, a rejected-declaration note, ...) that carries no executable
 * meaning is kept as a real `void "<text>"` statement instead of a comment -
 * `VoidOp` is a genuine GHC.JS UOp, and voiding a side-effect-free string
 * literal is a no-op at runtime, so this is exactly as inert as a comment
 * while still being an ordinary AST node with no Raw escape hatch. */
const jVoidNote = (text: string): Syntax.JStat => ({ tag: "UOpStat", op: "VoidOp", value: jStr(text) });
const jDecl = (ident: string, value?: Syntax.JExpr): Syntax.JStat => ({ tag: "DeclStat", ident, value });
const jReturn = (value: Syntax.JExpr): Syntax.JStat => ({ tag: "ReturnStat", value });
/** `throw new Error(message)`, built as a real ThrowStat/NewOp/ApplExpr tree
 * (src/js/syntax.ts's ThrowStat - a documented TS-only addition since GHC's
 * own JStat has no throw node at all). */
const jThrow = (message: Syntax.JExpr): Syntax.JStat => ({ tag: "ThrowStat", value: { tag: "UOpExpr", op: "NewOp", value: jCall(jVar("Error"), [message]) } });
const jThrowStatic = (message: string): Syntax.JStat => jThrow(jStr(message));
/** `String(prop(force(subject), "tag") || typeof force(subject))` - the
 * non-exhaustive-pattern diagnostic's dynamic half. The original used `??`,
 * which (like `throw`) GHC's Op enum has no constructor for; `||` is
 * behaviorally identical here since `prop(...)` is always either a non-empty
 * tag string or a falsy `undefined`/`null`, never `0`/`""`/`NaN`. */
const jTagOrType = (subject: string): Syntax.JExpr => {
  const forced = jCall(jVar("force"), [jVar(subject)]);
  return jCall(jVar("String"), [{ tag: "InfixExpr", op: "LOrOp", left: jCall(jVar("prop"), [forced, jStr("tag")]), right: { tag: "UOpExpr", op: "TypeofOp", value: forced } }]);
};
const jNonExhaustiveThrow = (prefix: string, subject: string): Syntax.JStat =>
  jThrow({ tag: "InfixExpr", op: "AddOp", left: jStr(prefix), right: jTagOrType(subject) });
const jIfStat = (cond: Syntax.JExpr, then: Syntax.JStat, els: Syntax.JStat = jBlock([])): Syntax.JStat => ({ tag: "IfStat", cond, then, else: els });
const jIfExpr = (cond: Syntax.JExpr, then: Syntax.JExpr, els: Syntax.JExpr): Syntax.JExpr => ({ tag: "IfExpr", cond, then, else: els });
const jAnd = (exprs: Syntax.JExpr[]): Syntax.JExpr => (exprs.length ? exprs.reduce((left, right): Syntax.JExpr => ({ tag: "InfixExpr", op: "LAndOp", left, right })) : jBool(true));
/** An IIFE built from a real JFunc, i.e. `(function() { <stats> })()`. */
const jIife = (stats: Syntax.JStat[]): Syntax.JExpr => jCall(jFunc([], jBlock(stats)), []);
const jThunkExpr = (body: Syntax.JExpr): Syntax.JExpr => jFunc([], jBlock([jReturn(body)]));
const jLazy = (expression: Syntax.JExpr): Syntax.JExpr => jCall(jVar("lazy"), [jThunkExpr(expression)]);
const jApply = (fn: Syntax.JExpr, argument: Syntax.JExpr): Syntax.JExpr => jCall(jVar("apply"), [fn, argument]);
/** A dotted global reference (e.g. "prelude.add") or the small `force(x)`
 * shape some `builtin` entries use, built as a real SelExpr/ApplExpr chain
 * instead of splicing the string in as source text. */
function globalPath(path: string): Syntax.JExpr {
  const forced = /^force\(([A-Za-z0-9_$]+)\)$/.exec(path);
  if (forced) return jCall(jVar("force"), [jVar(forced[1]!)]);
  const segments = path.split(".");
  return segments.slice(1).reduce<Syntax.JExpr>((acc, segment) => jSel(acc, segment), jVar(segments[0]!));
}
/** Build a JS literal AST node (string/number/bool/array/plain object) from a
 * TS value - used for the small JSON-ish specs (e.g. registerDerivedJSON's
 * argument) that used to go through JSON.stringify + a Raw splice. */
function jLit(value: unknown): Syntax.JExpr {
  if (value === null || value === undefined) return globalPath("null");
  if (typeof value === "string") return jStr(value);
  if (typeof value === "number") return jInt(value);
  if (typeof value === "boolean") return jBool(value);
  if (Array.isArray(value)) return jList(value.map(jLit));
  return { tag: "ValExpr", value: { tag: "JHash", entries: Object.entries(value as Record<string, unknown>).map(([key, v]): [string, Syntax.JExpr] => [key, jLit(v)]) } };
}
function emitWithBindings(
  result: Expr,
  bindings: import("./ast.js").LocalBinding[],
  locals: Set<string>,
  scope: EmitScope,
): Syntax.JExpr {
  if (!bindings.length) return emitExpr(result, locals, scope);
  const localNames = new Set([
    ...locals,
    ...bindings.flatMap(introducedNames),
  ]);
  return jIife([...emitLocalBindings(bindings, localNames, scope), jReturn(emitExpr(result, localNames, scope))]);
}
function emitPattern(
  pattern: Pattern,
  value: Syntax.JExpr,
): { test: Syntax.JExpr; bindings: Syntax.JStat[] } {
  switch (pattern.tag) {
    case "wild":
      return { test: jBool(true), bindings: [] };
    case "var":
      return { test: jBool(true), bindings: [jDecl(jsName(pattern.name), value)] };
    case "as": {
      const inner = emitPattern(pattern.pattern, value);
      return { test: inner.test, bindings: [jDecl(jsName(pattern.name), value), ...inner.bindings] };
    }
    case "int":
      return { test: { tag: "InfixExpr", op: "StrictEqOp", left: jCall(jVar("force"), [value]), right: jNumber(pattern.value) }, bindings: [] };
    case "string":
      return { test: { tag: "InfixExpr", op: "StrictEqOp", left: jCall(jVar("force"), [value]), right: jStr(pattern.value) }, bindings: [] };
    case "record": {
      const variable = `caseValue${pattern.span.start}_${patternTemporary++}`;
      const variableExpr = jVar(variable);
      const tests: Syntax.JExpr[] = [{ tag: "InfixExpr", op: "StrictEqOp", left: jCall(jVar("prop"), [variableExpr, jStr("tag")]), right: jStr(constructorTag(pattern.name)) }];
      const bindings: Syntax.JStat[] = [jDecl(variable, jCall(jVar("fromJSValAs"), [jStr(constructorTag(pattern.name)), value]))];
      for (const field of pattern.fields) {
        const nested = emitPattern(field.pattern, jCall(jVar("field"), [variableExpr, jStr(field.name)]));
        tests.push(nested.test);
        bindings.push(...nested.bindings);
      }
      return { test: jAnd(tests), bindings };
    }
    case "con": {
      const variable = `caseValue${pattern.span.start}_${patternTemporary++}`;
      const variableExpr = jVar(variable);
      const tests: Syntax.JExpr[] = [{ tag: "InfixExpr", op: "StrictEqOp", left: jCall(jVar("prop"), [variableExpr, jStr("tag")]), right: jStr(constructorTag(pattern.name)) }];
      const bindings: Syntax.JStat[] = [jDecl(variable, jCall(jVar("fromJSValAs"), [jStr(constructorTag(pattern.name)), value]))];
      pattern.args.forEach((arg, index) => {
        const nested = emitPattern(arg, jCall(jVar("fieldAt"), [variableExpr, jInt(index)]));
        tests.push(nested.test);
        bindings.push(...nested.bindings);
      });
      return { test: jAnd(tests), bindings };
    }
  }
}
function patternNames(pattern: Pattern): string[] {
  if (pattern.tag === "var") return [pattern.name];
  if (pattern.tag === "as")
    return [pattern.name, ...patternNames(pattern.pattern)];
  if (pattern.tag === "record") return pattern.fields.flatMap((field) => patternNames(field.pattern));
  return pattern.tag === "con" ? pattern.args.flatMap(patternNames) : [];
}
function introducedNames(binding: LocalBinding): string[] {
  if (binding.name.startsWith("__pattern_"))
    return binding.patterns.flatMap(patternNames);
  return [binding.name];
}
function emitAlternatives(
  alternatives: import("./ast.js").CaseAlternative[],
  subject: Syntax.JExpr,
  locals: Set<string>,
  scope: EmitScope,
): Syntax.JStat {
  const stats = alternatives.map((alternative) => {
    const compiled = emitPattern(alternative.pattern, subject);
    const alternativeLocals = new Set([
      ...locals,
      ...patternNames(alternative.pattern),
    ]);
    const buildGuards = (index: number, guardLocals: Set<string>): Syntax.JStat => {
      const guards = alternative.patternGuards ?? [];
      if (index >= guards.length) return jReturn(emitExpr(alternative.body, guardLocals, scope));
      const guard = guards[index]!;
      const source = `patternGuard${alternative.pattern.span.start}_${index}`;
      const nested = emitPattern(guard.pattern, jVar(source));
      const nextLocals = new Set([...guardLocals, ...patternNames(guard.pattern)]);
      return jBlock([
        jDecl(source, emitExpr(guard.source, guardLocals, scope)),
        ...nested.bindings,
        jIfStat(jNot(nested.test), jBlock([]), buildGuards(index + 1, nextLocals)),
      ]);
    };
    const test = alternative.guard
      ? ({ tag: "InfixExpr", op: "LAndOp", left: compiled.test, right: jCall(jVar("isTrue"), [emitExpr(alternative.guard, alternativeLocals, scope)]) } as Syntax.JExpr)
      : compiled.test;
    return jBlock([...compiled.bindings, jIfStat(test, buildGuards(0, alternativeLocals))]);
  });
  return jBlock(stats);
}
function dictionaryBinder(className: string, target: string, method: string): string {
  return `__dict_${[className, target, method].join("_").replace(/[^A-Za-z0-9_]+/g, "_")}`;
}
const primitiveMarshalTargets = new Set([
  "JSVal",
  "Int",
  "Integer",
  "Word",
  "Word8",
  "Word16",
  "Word32",
  "Word64",
  "Char",
  "Float",
  "Double",
  "Bool",
  "Text",
  "String",
  "JSString",
  "Value",
  "Object",
  "Maybe",
  "Either",
  "IO",
]);
function emittedMarshalClass(className: string, target: string): boolean {
  const name = className.split(".").at(-1) ?? className;
  if (name !== "FromJSVal" && name !== "ToJSVal") return false;
  const trimmed = target.trim();
  if (!trimmed || /\s/.test(trimmed) || trimmed.startsWith("(") || trimmed.startsWith("["))
    return false;
  const typeName =
    /^([A-Z][A-Za-z0-9_'.]*)/.exec(trimmed)?.[1]?.split(".").at(-1) ?? trimmed;
  if (!typeName || typeName === "()" || primitiveMarshalTargets.has(typeName)) return false;
  return true;
}
// The Miso.Native `[js| ... |]` quasiquote embeds a hand-written JavaScript
// snippet, after `${name}` placeholders have already been substituted with
// plain identifiers. Unlike everything else in this file, that text is not
// something ghcts derives from Haskell source it understands the shape of -
// it is arbitrary caller-authored JS. Parsing it with the TypeScript
// compiler (already a dependency, via `ts.createSourceFile`) and translating
// the result into real src/js/syntax.ts nodes still eliminates the last
// opaque-text path in this file; anything the small imperative JS subset
// below can't express throws a clear error naming the unsupported construct,
// rather than silently falling back to a raw splice.
function unsupportedFfi(node: ts.Node): never {
  throw new Error(`unsupported JavaScript in a [js| |] quasiquote: ${ts.SyntaxKind[node.kind]} (${node.getText()})`);
}
const FFI_BINARY_OPS: Partial<Record<ts.SyntaxKind, Syntax.Op>> = {
  [ts.SyntaxKind.LessThanToken]: "LtOp",
  [ts.SyntaxKind.GreaterThanToken]: "GtOp",
  [ts.SyntaxKind.LessThanEqualsToken]: "LeOp",
  [ts.SyntaxKind.GreaterThanEqualsToken]: "GeOp",
  [ts.SyntaxKind.EqualsEqualsToken]: "EqOp",
  [ts.SyntaxKind.EqualsEqualsEqualsToken]: "StrictEqOp",
  [ts.SyntaxKind.ExclamationEqualsToken]: "NeqOp",
  [ts.SyntaxKind.ExclamationEqualsEqualsToken]: "StrictNeqOp",
  [ts.SyntaxKind.PlusToken]: "AddOp",
  [ts.SyntaxKind.MinusToken]: "SubOp",
  [ts.SyntaxKind.AsteriskToken]: "MulOp",
  [ts.SyntaxKind.SlashToken]: "DivOp",
  [ts.SyntaxKind.PercentToken]: "ModOp",
  [ts.SyntaxKind.LessThanLessThanToken]: "LeftShiftOp",
  [ts.SyntaxKind.GreaterThanGreaterThanToken]: "RightShiftOp",
  [ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken]: "ZRightShiftOp",
  [ts.SyntaxKind.AmpersandToken]: "BAndOp",
  [ts.SyntaxKind.BarToken]: "BOrOp",
  [ts.SyntaxKind.CaretToken]: "BXorOp",
  [ts.SyntaxKind.AmpersandAmpersandToken]: "LAndOp",
  [ts.SyntaxKind.BarBarToken]: "LOrOp",
  [ts.SyntaxKind.InstanceOfKeyword]: "InstanceofOp",
  [ts.SyntaxKind.InKeyword]: "InOp",
};
/** Compound assignment operators GHC.JS's AOp has no direct constructor for
 * (only `=`, `+=`, `-=` exist) - desugared to `lhs = lhs <op> rhs`. */
const FFI_COMPOUND_ASSIGN_OPS: Partial<Record<ts.SyntaxKind, Syntax.Op>> = {
  [ts.SyntaxKind.AsteriskEqualsToken]: "MulOp",
  [ts.SyntaxKind.SlashEqualsToken]: "DivOp",
  [ts.SyntaxKind.PercentEqualsToken]: "ModOp",
  [ts.SyntaxKind.LessThanLessThanEqualsToken]: "LeftShiftOp",
  [ts.SyntaxKind.GreaterThanGreaterThanEqualsToken]: "RightShiftOp",
  [ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken]: "ZRightShiftOp",
  [ts.SyntaxKind.AmpersandEqualsToken]: "BAndOp",
  [ts.SyntaxKind.BarEqualsToken]: "BOrOp",
  [ts.SyntaxKind.CaretEqualsToken]: "BXorOp",
};
function ffiParams(params: ts.NodeArray<ts.ParameterDeclaration>): string[] {
  return params.map((p) => (ts.isIdentifier(p.name) ? p.name.text : unsupportedFfi(p)));
}
function translateFfiExpr(expr: ts.Expression): Syntax.JExpr {
  if (ts.isParenthesizedExpression(expr)) return translateFfiExpr(expr.expression);
  if (ts.isIdentifier(expr)) return jVar(expr.text);
  if (expr.kind === ts.SyntaxKind.ThisKeyword) return jVar("this");
  if (expr.kind === ts.SyntaxKind.NullKeyword) return globalPath("null");
  if (expr.kind === ts.SyntaxKind.TrueKeyword) return jBool(true);
  if (expr.kind === ts.SyntaxKind.FalseKeyword) return jBool(false);
  if (ts.isStringLiteralLike(expr)) return jStr(expr.text);
  if (ts.isNumericLiteral(expr)) return jNumber(Number(expr.text));
  if (ts.isPropertyAccessExpression(expr)) return jSel(translateFfiExpr(expr.expression), expr.name.text);
  if (ts.isElementAccessExpression(expr)) return { tag: "IdxExpr", obj: translateFfiExpr(expr.expression), index: translateFfiExpr(expr.argumentExpression) };
  if (ts.isCallExpression(expr)) return jCall(translateFfiExpr(expr.expression), expr.arguments.map(translateFfiExpr));
  if (ts.isNewExpression(expr)) return { tag: "UOpExpr", op: "NewOp", value: jCall(translateFfiExpr(expr.expression), (expr.arguments ?? []).map(translateFfiExpr)) };
  if (ts.isConditionalExpression(expr)) return jIfExpr(translateFfiExpr(expr.condition), translateFfiExpr(expr.whenTrue), translateFfiExpr(expr.whenFalse));
  if (ts.isArrayLiteralExpression(expr)) return jList(expr.elements.map(translateFfiExpr));
  if (ts.isObjectLiteralExpression(expr)) {
    return {
      tag: "ValExpr",
      value: {
        tag: "JHash",
        entries: expr.properties.map((prop): [string, Syntax.JExpr] => {
          if (!ts.isPropertyAssignment(prop)) return unsupportedFfi(prop);
          const key = ts.isIdentifier(prop.name) || ts.isStringLiteralLike(prop.name) ? prop.name.text : unsupportedFfi(prop.name);
          return [key, translateFfiExpr(prop.initializer)];
        }),
      },
    };
  }
  if (ts.isFunctionExpression(expr) || ts.isArrowFunction(expr)) {
    const params = ffiParams(expr.parameters);
    const body = ts.isBlock(expr.body) ? translateFfiStatements(expr.body.statements) : [jReturn(translateFfiExpr(expr.body))];
    return jFunc(params, jBlock(body));
  }
  if (ts.isPrefixUnaryExpression(expr)) {
    const value = translateFfiExpr(expr.operand);
    switch (expr.operator) {
      case ts.SyntaxKind.ExclamationToken: return { tag: "UOpExpr", op: "NotOp", value };
      case ts.SyntaxKind.TildeToken: return { tag: "UOpExpr", op: "BNotOp", value };
      case ts.SyntaxKind.MinusToken: return { tag: "UOpExpr", op: "NegOp", value };
      case ts.SyntaxKind.PlusToken: return { tag: "UOpExpr", op: "PlusOp", value };
      case ts.SyntaxKind.PlusPlusToken: return { tag: "UOpExpr", op: "PreIncOp", value };
      case ts.SyntaxKind.MinusMinusToken: return { tag: "UOpExpr", op: "PreDecOp", value };
      default: return unsupportedFfi(expr);
    }
  }
  if (ts.isPostfixUnaryExpression(expr)) {
    const value = translateFfiExpr(expr.operand);
    if (expr.operator === ts.SyntaxKind.PlusPlusToken) return { tag: "UOpExpr", op: "PostIncOp", value };
    if (expr.operator === ts.SyntaxKind.MinusMinusToken) return { tag: "UOpExpr", op: "PostDecOp", value };
    return unsupportedFfi(expr);
  }
  if (expr.kind === ts.SyntaxKind.TypeOfExpression) return { tag: "UOpExpr", op: "TypeofOp", value: translateFfiExpr((expr as ts.TypeOfExpression).expression) };
  if (expr.kind === ts.SyntaxKind.DeleteExpression) return { tag: "UOpExpr", op: "DeleteOp", value: translateFfiExpr((expr as ts.DeleteExpression).expression) };
  if (expr.kind === ts.SyntaxKind.VoidExpression) return { tag: "UOpExpr", op: "VoidOp", value: translateFfiExpr((expr as ts.VoidExpression).expression) };
  if (ts.isBinaryExpression(expr)) {
    const op = FFI_BINARY_OPS[expr.operatorToken.kind];
    if (op) return { tag: "InfixExpr", op, left: translateFfiExpr(expr.left), right: translateFfiExpr(expr.right) };
    return unsupportedFfi(expr);
  }
  return unsupportedFfi(expr);
}
/** Translate a JS assignment expression (used in statement position only -
 * GHC.JS.Syntax's AssignStat is a statement, not an expression, so this
 * cannot be nested inside a larger expression the way JS itself allows). */
function translateFfiAssignStat(expr: ts.BinaryExpression): Syntax.JStat {
  const lhs = translateFfiExpr(expr.left);
  if (expr.operatorToken.kind === ts.SyntaxKind.EqualsToken) return { tag: "AssignStat", lhs, op: "AssignOp", rhs: translateFfiExpr(expr.right) };
  if (expr.operatorToken.kind === ts.SyntaxKind.PlusEqualsToken) return { tag: "AssignStat", lhs, op: "AddAssignOp", rhs: translateFfiExpr(expr.right) };
  if (expr.operatorToken.kind === ts.SyntaxKind.MinusEqualsToken) return { tag: "AssignStat", lhs, op: "SubAssignOp", rhs: translateFfiExpr(expr.right) };
  const compound = FFI_COMPOUND_ASSIGN_OPS[expr.operatorToken.kind];
  if (compound) return { tag: "AssignStat", lhs, op: "AssignOp", rhs: { tag: "InfixExpr", op: compound, left: lhs, right: translateFfiExpr(expr.right) } };
  return unsupportedFfi(expr);
}
function translateFfiStatement(stmt: ts.Statement): Syntax.JStat {
  if (ts.isExpressionStatement(stmt)) {
    const expr = stmt.expression;
    if (ts.isBinaryExpression(expr) && (expr.operatorToken.kind === ts.SyntaxKind.EqualsToken || FFI_COMPOUND_ASSIGN_OPS[expr.operatorToken.kind] || expr.operatorToken.kind === ts.SyntaxKind.PlusEqualsToken || expr.operatorToken.kind === ts.SyntaxKind.MinusEqualsToken))
      return translateFfiAssignStat(expr);
    if (ts.isCallExpression(expr)) return { tag: "ApplStat", fn: translateFfiExpr(expr.expression), args: expr.arguments.map(translateFfiExpr) };
    if (ts.isPrefixUnaryExpression(expr) || ts.isPostfixUnaryExpression(expr)) {
      const value = translateFfiExpr(expr.operand);
      const op = (expr as ts.PrefixUnaryExpression | ts.PostfixUnaryExpression).operator === ts.SyntaxKind.PlusPlusToken
        ? (ts.isPrefixUnaryExpression(expr) ? "PreIncOp" : "PostIncOp")
        : (ts.isPrefixUnaryExpression(expr) ? "PreDecOp" : "PostDecOp");
      return { tag: "UOpStat", op, value };
    }
    if (ts.isConditionalExpression(expr))
      return jIfStat(translateFfiExpr(expr.condition), translateFfiStatement(ts.factory.createExpressionStatement(expr.whenTrue)), translateFfiStatement(ts.factory.createExpressionStatement(expr.whenFalse)));
    // Matches GHC.JS.Make.expr2stat: only ApplExpr/IfExpr/UOpExpr convert to
    // a statement; any other bare expression statement has no side effect
    // GHC.JS.Syntax can express, so it becomes the empty statement (nullStat).
    return jBlock([]);
  }
  if (ts.isReturnStatement(stmt)) return stmt.expression ? jReturn(translateFfiExpr(stmt.expression)) : jReturn(globalPath("undefined"));
  if (ts.isIfStatement(stmt)) return jIfStat(translateFfiExpr(stmt.expression), translateFfiStatement(stmt.thenStatement), stmt.elseStatement ? translateFfiStatement(stmt.elseStatement) : jBlock([]));
  if (ts.isBlock(stmt)) return jBlock(translateFfiStatements(stmt.statements));
  if (ts.isEmptyStatement(stmt)) return jBlock([]);
  if (ts.isThrowStatement(stmt)) return { tag: "ThrowStat", value: translateFfiExpr(stmt.expression) };
  if (ts.isBreakStatement(stmt)) return { tag: "BreakStat", label: stmt.label?.text };
  if (ts.isContinueStatement(stmt)) return { tag: "ContinueStat", label: stmt.label?.text };
  if (ts.isVariableStatement(stmt)) return jBlock(stmt.declarationList.declarations.map((decl): Syntax.JStat => {
    if (!ts.isIdentifier(decl.name)) return unsupportedFfi(decl);
    return jDecl(decl.name.text, decl.initializer && translateFfiExpr(decl.initializer));
  }));
  if (ts.isForStatement(stmt)) {
    const init: Syntax.JStat = !stmt.initializer
      ? jBlock([])
      : ts.isVariableDeclarationList(stmt.initializer)
        ? jBlock(stmt.initializer.declarations.map((decl): Syntax.JStat => (ts.isIdentifier(decl.name) ? jDecl(decl.name.text, decl.initializer && translateFfiExpr(decl.initializer)) : unsupportedFfi(decl))))
        : ts.isBinaryExpression(stmt.initializer) ? translateFfiAssignStat(stmt.initializer) : { tag: "ApplStat" as const, fn: translateFfiExpr(stmt.initializer), args: [] };
    const step: Syntax.JStat = !stmt.incrementor
      ? jBlock([])
      : ts.isBinaryExpression(stmt.incrementor)
        ? translateFfiAssignStat(stmt.incrementor)
        : ts.isPrefixUnaryExpression(stmt.incrementor) || ts.isPostfixUnaryExpression(stmt.incrementor)
          ? { tag: "UOpStat", op: stmt.incrementor.operator === ts.SyntaxKind.PlusPlusToken ? (ts.isPrefixUnaryExpression(stmt.incrementor) ? "PreIncOp" : "PostIncOp") : (ts.isPrefixUnaryExpression(stmt.incrementor) ? "PreDecOp" : "PostDecOp"), value: translateFfiExpr(stmt.incrementor.operand) }
          : { tag: "ApplStat" as const, fn: translateFfiExpr(stmt.incrementor), args: [] };
    return { tag: "ForStat", init, cond: stmt.condition ? translateFfiExpr(stmt.condition) : jBool(true), step, body: translateFfiStatement(stmt.statement) };
  }
  if (ts.isWhileStatement(stmt)) return { tag: "WhileStat", isDo: false, cond: translateFfiExpr(stmt.expression), body: translateFfiStatement(stmt.statement) };
  if (ts.isDoStatement(stmt)) return { tag: "WhileStat", isDo: true, cond: translateFfiExpr(stmt.expression), body: translateFfiStatement(stmt.statement) };
  if (ts.isTryStatement(stmt)) {
    const catchClause = stmt.catchClause;
    return {
      tag: "TryStat",
      body: jBlock(translateFfiStatements(stmt.tryBlock.statements)),
      ident: catchClause?.variableDeclaration && ts.isIdentifier(catchClause.variableDeclaration.name) ? catchClause.variableDeclaration.name.text : "e",
      catch: catchClause ? jBlock(translateFfiStatements(catchClause.block.statements)) : jBlock([]),
      finally: stmt.finallyBlock ? jBlock(translateFfiStatements(stmt.finallyBlock.statements)) : jBlock([]),
    };
  }
  return unsupportedFfi(stmt);
}
function translateFfiStatements(stmts: readonly ts.Statement[]): Syntax.JStat[] {
  return stmts.map(translateFfiStatement);
}
/** Parse and translate a `[js| ... |]` quasiquote body (after `${name}`
 * placeholder substitution) into real GHC.JS.Syntax statements. */
function translateFfiBody(body: string): Syntax.JStat[] {
  const sourceFile = ts.createSourceFile("ffi-quasiquote.ts", body, ts.ScriptTarget.ES2022, false, ts.ScriptKind.TS);
  return translateFfiStatements(sourceFile.statements);
}
function emitExpr(expr: Expr, locals: Set<string>, scope: EmitScope): Syntax.JExpr {
  const variable = (name: string): Syntax.JExpr => {
    const forced = (n: string) => jCall(jVar("force"), [jVar(jsName(n))]);
    if (locals.has(name)) return forced(name);
    if (scope.definesValue.has(name)) {
      const owned = scope.names.get(name) ?? `${scope.module}.${name}`;
      if (builtin[owned]) return globalPath(builtin[owned]);
      return forced(owned);
    }
    const resolved = scope.names.get(name);
    if (name === "!!" && resolved && scope.definedNames.has(resolved))
      return forced(resolved);
    if (builtin[name]) return globalPath(builtin[name]);
    if (resolved) {
      if (builtin[resolved]) return globalPath(builtin[resolved]);
      return forced(resolved);
    }
    if (name.includes(".")) return forced(name);
    const owned = `${scope.module}.${name}`;
    if (builtin[owned]) return globalPath(builtin[owned]);
    return forced(owned);
  };
  switch (expr.tag) {
    case "int":
      return jNumber(expr.value);
    case "string":
      return jStr(expr.value);
    case "unit":
      return globalPath("prelude.unit");
    case "tuple":
      return jCall(jVar("tuple"), [jList(expr.items.map((item) => jLazy(emitExpr(item, locals, scope))))]);
    case "list":
      return expr.items.reduceRight(
        (tail, head) =>
          jApply(jApply(globalPath("prelude.cons"), jLazy(emitExpr(head, locals, scope))), jLazy(tail)),
        globalPath("prelude.nil"),
      );
    case "listComp": {
      const lowerQualifiers = (
        index: number,
        scopeLocals: Set<string>,
      ): Syntax.JExpr => {
        if (index >= expr.qualifiers.length)
          return jApply(
            jApply(globalPath("prelude.cons"), jLazy(emitExpr(expr.body, scopeLocals, scope))),
            jLazy(globalPath("prelude.nil")),
          );
        const qualifier = expr.qualifiers[index];
        if (qualifier.tag === "guard")
          return jIfExpr(jCall(jVar("isTrue"), [emitExpr(qualifier.condition, scopeLocals, scope)]), lowerQualifiers(index + 1, scopeLocals), globalPath("prelude.nil"));
        const item = `listCompItem${expr.span.start}_${index}`;
        const pattern = emitPattern(qualifier.pattern, jVar(item));
        const nextLocals = new Set([
          ...scopeLocals,
          ...patternNames(qualifier.pattern),
        ]);
        const rest = lowerQualifiers(index + 1, nextLocals);
        const body = jBlock([
          jDecl(`${item}Value`, jCall(jVar("force"), [jVar(item)])),
          ...pattern.bindings,
          jIfStat(jNot(pattern.test), jReturn(globalPath("prelude.nil"))),
          jReturn(rest),
        ]);
        return jApply(
          jApply(globalPath("prelude.concatMap"), jLazy(jFunc([item], body))),
          jLazy(emitExpr(qualifier.source, scopeLocals, scope)),
        );
      };
      return lowerQualifiers(0, locals);
    }
    case "record": {
      const byName = new Map(expr.fields.map((field) => [field.name, field.value]));
      const order =
        constructorFieldOrder(expr.constructor, scope.recordFields) ??
        expr.fields.map((field) => field.name);
      return order.reduce(
        (value, name) =>
          jApply(value, jLazy(emitExpr(byName.get(name) ?? { tag: "var", name, span: expr.span }, locals, scope))),
        variable(expr.constructor),
      );
    }
    case "recordUpdate":
      return jCall(jVar("updateRecord"), [
        emitExpr(expr.base, locals, scope),
        { tag: "ValExpr", value: { tag: "JHash", entries: expr.fields.map((field): [string, Syntax.JExpr] => [field.name, jLazy(emitExpr(field.value, locals, scope))]) } },
      ]);
    case "var":
      return variable(expr.name);
    case "app":
      // A `do` block is an action, not a value: `forever`/`mapM_` and friends
      // force the same argument repeatedly and must perform it each time.
      // `lazy` memoises the first result, which silently runs the body once.
      // Static pointers need a link-time identity.  GHCJS uses a stable
      // fingerprint; deriving one from the source module/span gives every
      // JS context the same key without making the backend know any library.
      if (expr.fn.tag === "var" && expr.fn.name === "static") {
        const key = staticPointerKey(scope.module, expr.span.start);
        const value = emitExpr(expr.arg, locals, scope);
        scope.staticSites.push({ key, value });
        return jApply(jApply(globalPath("prelude.staticPtrStable"), jLazy(jStr(key))), jLazy(value));
      }
      return jApply(
        emitExpr(expr.fn, locals, scope),
        expr.arg.tag === "do" ? jCall(jVar("io"), [jThunkExpr(emitExpr(expr.arg, locals, scope))]) : jLazy(emitExpr(expr.arg, locals, scope)),
      );
    case "lambda":
      return jFuncExpr([jsName(expr.parameter)], emitExpr(expr.body, new Set([...locals, expr.parameter]), scope));
    case "lambdaCase": {
      const subject = `lambdaCase${expr.span.start}`;
      const subjectForced = jCall(jVar("force"), [jVar(subject)]);
      const nullaryTags = expr.alternatives
        .flatMap((alternative) =>
          alternative.pattern.tag === "con" && alternative.pattern.args.length === 0
            ? [alternative.pattern.name.split(".").at(-1)!]
            : [],
        );
      const vtext = expr.alternatives.find(
        (alternative) =>
          (alternative.pattern.tag === "con" || alternative.pattern.tag === "record") &&
          (alternative.pattern.name.endsWith("VText") || alternative.pattern.name.endsWith("Text")),
      );
      const vtextArity =
        vtext?.pattern.tag === "con"
          ? vtext.pattern.args.length
          : vtext?.pattern.tag === "record"
            ? vtext.pattern.fields.length
            : 0;
      const value = `${subject}Value`;
      const vtextFields: Syntax.JExpr[] =
        vtextArity >= 2
          ? [jLazy(globalPath("prelude.nothing")), jLazy(subjectForced)]
          : [jLazy(subjectForced)];
      const isString: Syntax.JExpr = { tag: "InfixExpr", op: "StrictEqOp", left: { tag: "UOpExpr", op: "TypeofOp", value: subjectForced }, right: jStr("string") };
      const vtextObj: Syntax.JExpr = { tag: "ValExpr", value: { tag: "JHash", entries: [["tag", jStr("VText")], ["fields", jList(vtextFields)]] } };
      const enumObj: Syntax.JExpr = { tag: "ValExpr", value: { tag: "JHash", entries: [["tag", subjectForced], ["fields", jList([])]] } };
      const nullaryCheck: Syntax.JExpr = nullaryTags.length
        ? { tag: "InfixExpr", op: "LAndOp", left: isString, right: jCall(jSel(jList(nullaryTags.map(jStr)), "includes"), [subjectForced]) }
        : jBool(false);
      const normalizedValue: Syntax.JExpr = vtext
        ? jIfExpr(isString, vtextObj, jIfExpr(nullaryCheck, enumObj, jVar(subject)))
        : jIfExpr(nullaryCheck, enumObj, jVar(subject));
      const body = jBlock([
        jDecl(value, normalizedValue),
        emitAlternatives(expr.alternatives, jVar(value), locals, scope),
        // Syntax.hs models no `throw` statement at all - GHC's own RTS never
        // needs one - so this stays a raw statement, not a shortcut around
        // structured control flow (see the note above jVar's definition).
        jNonExhaustiveThrow("Non-exhaustive patterns in lambda-case: ", value),
      ]);
      return jFunc([subject], body);
    }
    case "let": {
      const names = new Set(expr.bindings.flatMap(introducedNames));
      const localNames = new Set([...locals, ...names]);
      return jIife([...emitLocalBindings(expr.bindings, localNames, scope), jReturn(emitExpr(expr.body, localNames, scope))]);
    }
    case "do": {
      const foldDo = (index: number, scopeLocals: Set<string>): Syntax.JExpr => {
        if (index >= expr.statements.length) return globalPath("prelude.unit");
        const statement = expr.statements[index];
        if (statement.tag === "let") {
          const nextLocals = new Set(scopeLocals);
          for (const name of statement.bindings.flatMap(introducedNames))
            nextLocals.add(name);
          return jIife([...emitLocalBindings(statement.bindings, nextLocals, scope), jReturn(foldDo(index + 1, nextLocals))]);
        }
        const last = index === expr.statements.length - 1;
        if (statement.tag === "expr") {
          const action = emitExpr(statement.expr, scopeLocals, scope);
          if (last) return jCall(jVar("force"), [action]);
          return jApply(
            jApply(globalPath("prelude.then"), jLazy(action)),
            jLazy(foldDo(index + 1, scopeLocals)),
          );
        }
        const value = `doValue${expr.span.start}_${index}`;
        const pattern = emitPattern(statement.pattern, jVar(value));
        const source = emitExpr(statement.source, scopeLocals, scope);
        const nextLocals = new Set(scopeLocals);
        for (const name of patternNames(statement.pattern)) nextLocals.add(name);
        const body = jBlock([
          jDecl(value, jVar("result")),
          ...pattern.bindings,
          jIfStat(jNot(pattern.test), jThrowStatic("Pattern match failure in do binding")),
          jReturn(last ? jVar(value) : foldDo(index + 1, nextLocals)),
        ]);
        return jApply(
          jApply(globalPath("prelude.bind"), jLazy(source)),
          jLazy(jFunc(["result"], body)),
        );
      };
      return foldDo(0, new Set(locals));
    }
    case "if":
      return jIfExpr(
        jCall(jVar("isTrue"), [emitExpr(expr.condition, locals, scope)]),
        emitExpr(expr.thenBranch, locals, scope),
        emitExpr(expr.elseBranch, locals, scope),
      );
    case "case": {
      const subject = `caseSubject${expr.span.start}`;
      return jIife([
        jDecl(subject, jCall(jVar("lazy"), [jThunkExpr(emitExpr(expr.subject, locals, scope))])),
        emitAlternatives(expr.alternatives, jVar(subject), locals, scope),
        jNonExhaustiveThrow("Non-exhaustive patterns in case: ", subject),
      ]);
    }
    case "jsQuote": {
      // The FFI quasiquote body is opaque foreign JavaScript text by
      // construction - the same status a `foreign import javascript` string
      // has in GHCJS itself, which also never parses or structures it.
      const names = [
        ...new Set(
          [...expr.body.matchAll(/\$\{([A-Za-z_][A-Za-z0-9_']*)\}/g)].map(
            (match) => match[1]!,
          ),
        ),
      ];
      let body = expr.body;
      for (const [index, name] of names.entries())
        body = body.replaceAll(`\${${name}}`, `__p${index}`);
      if (!names.length) return jCall(jVar("io"), [jFunc([], jBlock(translateFfiBody(body)))]);
      const arrayJoinCheck: Syntax.JExpr = jIfExpr(
        {
          tag: "InfixExpr", op: "LAndOp",
          left: jCall(jSel(jVar("Array"), "isArray"), [jVar("v")]),
          right: jCall(jSel(jVar("v"), "every"), [jFuncExpr(["c"], { tag: "InfixExpr", op: "StrictEqOp", left: { tag: "UOpExpr", op: "TypeofOp", value: jVar("c") }, right: jStr("string") })]),
        },
        jCall(jSel(jVar("v"), "join"), [jStr("")]),
        jVar("v"),
      );
      const bindings = names.map((name, index) =>
        jDecl(`__p${index}`, jIife([jDecl("v", jCall(jVar("jsValue"), [variable(name)])), jReturn(arrayJoinCheck)])),
      );
      const params = names.map((_, index) => `__p${index}`);
      const callExpr = jCall(jFunc(params, jBlock(translateFfiBody(body))), params.map(jVar));
      return jCall(jVar("io"), [jFunc([], jBlock([...bindings, jReturn(callExpr)]))]);
    }
  }
}
function emitDeclaration(declaration: Declaration, scope: EmitScope): Syntax.JStat {
  const qualified = (name: string) => jsName(`${scope.module}.${name}`);
  if (declaration.tag === "signature")
    return jVoidNote(`${declaration.name} :: ${declaration.type}`);
  if (declaration.tag === "typeAlias")
    return jVoidNote(`type ${declaration.name} ${declaration.parameters.join(" ")} = ${declaration.target}`);
  if (declaration.tag === "class") {
    const methods: Syntax.JStat[] = [];
    const className = declaration.name.split(".").at(-1) ?? declaration.name;
    for (const member of classMembers(declaration)) {
      if (member.kind === "associatedType") continue;
      const ident = qualified(member.name);
      if (scope.emittedJs.has(ident)) continue;
      scope.emittedJs.add(ident);
      if (member.name === "at")
        methods.push(jDecl(ident, jLazy(globalPath("prelude.at"))));
      else if (member.name === "toJSON")
        methods.push(jDecl(ident, jLazy(globalPath("prelude.toJSON"))));
      else if (member.name === "parseJSON")
        methods.push(jDecl(ident, jLazy(globalPath("prelude.parseJSON"))));
      else
        methods.push(
          jDecl(ident, jLazy(jFuncExpr(["arg0"], jCall(jVar("classMethod"), [jStr(className), jStr(member.name), jVar("arg0")])))),
        );
    }
    return methods.length ? jBlock(methods) : jVoidNote(`class ${declaration.name}`);
  }
  if (declaration.tag === "instance") {
    const parsed = instanceHead(declaration.head);
    if (!parsed) return jVoidNote(`instance ${declaration.head}`);
    const parts: Syntax.JStat[] = [];
    const typeName =
      /^([A-Z][A-Za-z0-9_'.]*)/.exec(parsed.target.trim())?.[1].split(".").at(-1) ??
      parsed.target;
    const constructors = scope.constructors.get(typeName) ?? [];
    if (
      parsed.className === "ToJSVal" &&
      constructors.length > 0 &&
      constructors.every((constructor) => constructor.arity === 0)
    ) {
      for (const [index, constructor] of constructors.entries())
        parts.push(jCallStat(jVar("registerEnum"), [jStr(constructor.name), jInt(index), jStr(typeName)]));
      parts.push(jCallStat(jVar("registerEnumType"), [jStr(typeName)]));
    }
    for (const [index, method] of instanceMethodValues(declaration).entries()) {
      expandRecordWildcards(method, scope.recordFields);
      const dictName = dictionaryBinder(
        parsed.className,
        `${parsed.target}_${declaration.span.start}_${index}`,
        method.name,
      );
      parts.push(emitDeclaration({ ...method, name: dictName }, scope));
      parts.push(
        jCallStat(jVar("registerInstance"), [jStr(parsed.className.split(".").at(-1)!), jStr(parsed.target), jStr(method.name), jVar(qualified(dictName))]),
      );
    }
    return parts.length ? jBlock(parts) : jVoidNote(`instance ${declaration.head}`);
  }
  if (declaration.tag === "unsupported" || declaration.tag === "splice")
    return jVoidNote(`${declaration.tag === "splice" ? declaration.name : declaration.feature} declaration was rejected during typechecking`);
  if (declaration.tag === "foreign") {
    const thunk = isIOResultType(declaration.signature.at(-1)) && declaration.arity === 0 ? "io" : "lazy";
    const foreign = jCall(jVar("foreignFunction"), [jStr(declaration.javascript), jInt(declaration.arity)]);
    return jDecl(qualified(declaration.name), jCall(jVar(thunk), [jThunkExpr(foreign)]));
  }
  if (declaration.tag === "data") {
    const constructorStats = declaration.constructors.flatMap((constructorInfo) => {
      const accessors = (constructorInfo.fields ?? []).map((fieldName) =>
        jDecl(qualified(fieldName), jLazy(jFuncExpr(["record"], jCall(jVar("field"), [jVar("record"), jStr(fieldName)])))),
      );
      const constructorCallArgs: Syntax.JExpr[] = [jStr(constructorInfo.name), jInt(constructorInfo.arity)];
      if (constructorInfo.fields) constructorCallArgs.push(jList(constructorInfo.fields.map(jStr)));
      const constructorCall = jCall(jVar("constructor"), constructorCallArgs);
      return [
        jCallStat(jVar("registerConstructorType"), [jStr(constructorInfo.name), jStr(declaration.name), jList((constructorInfo.fields ?? []).map(jStr))]),
        jDecl(qualified(constructorInfo.name), jLazy(constructorCall)),
        ...accessors,
      ];
    });
    if (
      !declaration.deriving.includes("ToJSON") &&
      !declaration.deriving.includes("FromJSON")
    )
      return jBlock(constructorStats);
    const spec = {
      typeName: declaration.name,
      allNullary: declaration.constructors.every((constructorInfo) => constructorInfo.arity === 0),
      constructors: declaration.constructors.map((constructorInfo) => ({
        name: constructorInfo.name,
        arity: constructorInfo.arity,
        fields: constructorInfo.fields,
      })),
    };
    return jBlock([...constructorStats, jCallStat(jVar("registerDerivedJSON"), [jLit(spec)])]);
  }
  if (declaration.name.startsWith("__pattern_")) {
    const equation = declaration.equations[0];
    const pattern = equation?.patterns[0];
    if (!pattern) return jVoidNote(declaration.name);
    const subject = `letPattern${declaration.span.start}_${patternTemporary++}`;
    const compiled = emitPattern(pattern, jVar(subject));
    const rhs = emitWithBindings(
      equation.guards[0]?.body ?? { tag: "unit", span: declaration.span },
      equation.whereBindings ?? [],
      new Set(),
      scope,
    );
    const aliases = patternNames(pattern).map((name) => jDecl(qualified(name), jLazy(jVar(jsName(name)))));
    return jBlock([
      jDecl(subject, jLazy(rhs)),
      ...compiled.bindings,
      jIfStat(jNot(compiled.test), jThrowStatic(`Pattern match failure in ${declaration.name}`)),
      ...aliases,
    ]);
  }
  // `emptyQueue = mempty` needs Queue's Monoid instance, which we do not emit.
  // Keep the runtime polyfill so the scheduler queue stays a Queue record.
  if (declaration.name === "emptyQueue")
    return jDecl(qualified("emptyQueue"), jLazy(globalPath("prelude.emptyQueue")));
  const arity = declaration.equations[0]?.patterns.length ?? 0;
  const arguments_ = Array.from({ length: arity }, (_, index) => `arg${index}`);
  let fallback: Syntax.JStat = jThrowStatic(`Non-exhaustive patterns in ${declaration.name}`);
  for (const equation of [...declaration.equations].reverse()) {
    const compiled = equation.patterns.map((pattern, index) =>
      emitPattern(pattern, jVar(arguments_[index]!)),
    );
    const test = jAnd(compiled.map((pattern) => pattern.test));
    const equationLocals = new Set(equation.patterns.flatMap(patternNames));
    let guarded: Syntax.JStat = fallback;
    for (const guard of [...equation.guards].reverse()) {
      const condition = guard.condition
        ? jCall(jVar("isTrue"), [emitWithBindings(guard.condition, equation.whereBindings, equationLocals, scope)])
        : jBool(true);
      guarded = jBlock([jIfStat(condition, jReturn(emitWithBindings(guard.body, equation.whereBindings, equationLocals, scope))), guarded]);
    }
    fallback = jBlock([...compiled.flatMap((pattern) => pattern.bindings), jIfStat(test, guarded), fallback]);
  }
  let body: Syntax.JExpr = jIife([fallback]);
  for (const argument of arguments_.reverse())
    body = jFuncExpr([argument], body);
  const thunk =
    arity === 0 && isIOResultType(scope.signatures.get(declaration.name))
      ? "io"
      : "lazy";
  return jDecl(qualified(declaration.name), jCall(jVar(thunk), [jThunkExpr(body)]));
}
function emitPatternBinding(
  binding: LocalBinding,
  locals: Set<string>,
  scope: EmitScope,
): Syntax.JStat {
  const pattern = binding.patterns[0];
  if (!pattern)
    return jDecl(jsName(binding.name), jLazy(emitExpr(binding.value, locals, scope)));
  const subject = `letPattern${binding.span.start}_${patternTemporary++}`;
  const compiled = emitPattern(pattern, jVar(subject));
  return jBlock([
    jDecl(subject, jLazy(emitExpr(binding.value, locals, scope))),
    ...compiled.bindings,
    jIfStat(jNot(compiled.test), jThrowStatic("Pattern match failure in let binding")),
  ]);
}
function emitLocalBindings(bindings: LocalBinding[], locals: Set<string>, scope: EmitScope): Syntax.JStat[] {
  const grouped = new Map<string, LocalBinding[]>();
  for (const binding of bindings) grouped.set(binding.name, [...(grouped.get(binding.name) ?? []), binding]);
  return [...grouped.entries()].map(([name, equations]) => {
    if (name.startsWith("__pattern_") && equations.length === 1)
      return emitPatternBinding(equations[0]!, locals, scope);
    const arity = Math.max(...equations.map((e) => e.patterns.length), 0);
    const args = Array.from({ length: arity }, (_, i) => `localArg${patternTemporary++}_${i}`);
    let body: Syntax.JStat = jThrowStatic(`Non-exhaustive patterns in ${name}`);
    for (const equation of [...equations].reverse()) {
      const compiled = equation.patterns.map((pattern, i) => emitPattern(pattern, jVar(args[i]!)));
      const equationLocals = new Set([...locals, ...equation.patterns.flatMap(patternNames)]);
      const whereBindings = equation.whereBindings ?? [];
      const guards = equation.guards ?? [];
      let guarded: Syntax.JStat;
      if (guards.length) {
        guarded = body;
        for (const guard of [...guards].reverse()) {
          const condition = guard.condition
            ? jCall(jVar("isTrue"), [emitWithBindings(guard.condition, whereBindings, equationLocals, scope)])
            : jBool(true);
          guarded = jBlock([jIfStat(condition, jReturn(emitWithBindings(guard.body, whereBindings, equationLocals, scope))), guarded]);
        }
      } else {
        guarded = jReturn(emitWithBindings(equation.value, whereBindings, equationLocals, scope));
      }
      const test = jAnd(compiled.map((p) => p.test));
      body = jBlock([...compiled.flatMap((p) => p.bindings), jIfStat(test, guarded), body]);
    }
    // Local equations are curried just like top-level equations. Keep the
    // pattern-dispatch block in the innermost ordinary JS function, then
    // wrap it one parameter at a time. This is the same JFunc nesting used by
    // GHCJS; an arrow here changes the generated closure ABI.
    let functionValue: Syntax.JExpr = args.length ? jFunc([args.at(-1)!], jBlock([body])) : jIife([body]);
    for (const arg of args.slice(0, -1).reverse())
      functionValue = jFuncExpr([arg], functionValue);
    return jDecl(jsName(name), jLazy(functionValue));
  });
}
function declarationNames(module: Module): string[] {
  return module.declarations.flatMap((declaration) =>
    declaration.tag === "value" && declaration.name.startsWith("__pattern_")
      ? declaration.equations.flatMap((equation) =>
          equation.patterns.flatMap(patternNames),
        )
      : declaration.tag === "value" ||
          declaration.tag === "foreign" ||
          declaration.tag === "signature"
        ? [declaration.name]
        : declaration.tag === "data"
          ? declaration.constructors.flatMap((constructor) => [
              constructor.name,
              ...(constructor.fields ?? []),
            ])
          : declaration.tag === "class" || declaration.tag === "instance"
            ? declaration.members.flatMap((member) =>
                member.tag === "value" ||
                member.tag === "foreign" ||
                member.tag === "signature"
                  ? [member.name]
                  : [],
              )
            : [],
  );
}
// ES module import/export syntax is not part of GHC.JS.Syntax's grammar at
// all (that's GHC.StgToJS.Linker's domain, a different subsystem, and it
// doesn't use ES modules either) - so there is no GHC.JS AST node to build
// these from. TypeScript's own compiler is already a dependency here (see
// `ts.transpileModule` below), so its factory/printer API is the real AST
// this wrapper is built from instead of string concatenation.
const tsPrintTarget = ts.createSourceFile("ghcts-print.ts", "", ts.ScriptTarget.ES2022, false, ts.ScriptKind.TS);
const tsPrinter = ts.createPrinter({ newLine: ts.NewLineKind.LineFeed });
function printTsNode(node: ts.Node): string {
  return tsPrinter.printNode(ts.EmitHint.Unspecified, node, tsPrintTarget);
}
function tsNamedImport(names: string[], moduleSpecifier: string): string {
  return printTsNode(
    ts.factory.createImportDeclaration(
      undefined,
      ts.factory.createImportClause(
        false,
        undefined,
        ts.factory.createNamedImports(names.map((name) => ts.factory.createImportSpecifier(false, undefined, ts.factory.createIdentifier(name)))),
      ),
      ts.factory.createStringLiteral(moduleSpecifier),
    ),
  );
}
function tsNamedExport(names: string[]): string {
  return printTsNode(
    ts.factory.createExportDeclaration(
      undefined,
      false,
      ts.factory.createNamedExports(names.map((name) => ts.factory.createExportSpecifier(false, undefined, ts.factory.createIdentifier(name)))),
      undefined,
    ),
  );
}
/** `export const <name> = () => force(<forcedIdent>);` */
function tsEntryConst(name: string, forcedIdent: string): string {
  return printTsNode(
    ts.factory.createVariableStatement(
      [ts.factory.createModifier(ts.SyntaxKind.ExportKeyword)],
      ts.factory.createVariableDeclarationList(
        [ts.factory.createVariableDeclaration(
          name,
          undefined,
          undefined,
          ts.factory.createArrowFunction(undefined, undefined, [], undefined, undefined, ts.factory.createCallExpression(ts.factory.createIdentifier("force"), undefined, [ts.factory.createIdentifier(forcedIdent)])),
        )],
        ts.NodeFlags.Const,
      ),
    ),
  );
}
function tsDefaultExport(name: string): string {
  return printTsNode(ts.factory.createExportAssignment(undefined, false, ts.factory.createIdentifier(name)));
}
function lower(
  modules: Module[],
  entryModule: Module,
  entry: string,
  file: string,
): { code?: string; diagnostics: Diagnostic[]; moduleSources?: Record<string, string> } {
  patternTemporary = 0;
  const diagnostics: Diagnostic[] = [];
  const coreModules = lowerModules(modules);
  for (const coreModule of coreModules) {
    if (!modules.some((module) => module.name === coreModule.name)) {
      diagnostics.push(
        error(
          "E_CORE_MODULE",
          `Core module ${coreModule.name} has no corresponding source module`,
          file,
        ),
      );
    }
  }
  if (
    !entryModule.declarations.some(
      (declaration) =>
        declaration.tag === "value" && declaration.name === entry,
    )
  )
    diagnostics.push(
      error(
        "E_ENTRY_EXPORT",
        `Entry ${entry} is not a value declaration`,
        file,
      ),
    );
  if (diagnostics.length) return { diagnostics };
  const exports = new Map<string, Map<string, string>>(
    modules.map((module) => [
      module.name,
      new Map(
        declarationNames(module).map((name) => [
          name,
          `${module.name}.${name}`,
        ]),
      ),
    ]),
  );
  const namesFor = (module: Module) => {
    const names = new Map(exports.get(module.name));
    for (const imported of module.imports) {
      const importedExports =
        exports.get(imported.module) ?? new Map<string, string>();
      const selected = imported.exposing ?? [...importedExports.keys()];
      for (const name of selected) {
        if (imported.hiding?.includes(name)) continue;
        const target = importedExports.get(name);
        if (!target) continue;
        if (!imported.qualified) names.set(name, target);
        names.set(`${imported.alias ?? imported.module}.${name}`, target);
      }
      const importedModule = modules.find((item) => item.name === imported.module);
      for (const typeName of imported.exposingConstructors ?? []) {
        const data = importedModule?.declarations.find(
          (declaration) =>
            declaration.tag === "data" && declaration.name === typeName,
        );
        if (data?.tag === "data") {
        for (const constructor of data.constructors) {
          const target = `${imported.module}.${constructor.name}`;
          if (!imported.qualified) names.set(constructor.name, target);
          names.set(
            `${imported.alias ?? imported.module}.${constructor.name}`,
            target,
          );
          for (const fieldName of constructor.fields ?? []) {
            const fieldTarget = `${imported.module}.${fieldName}`;
            if (!imported.qualified) names.set(fieldName, fieldTarget);
            names.set(
              `${imported.alias ?? imported.module}.${fieldName}`,
              fieldTarget,
            );
          }
        }
        }
        const cls = importedModule?.declarations.find(
          (declaration) =>
            declaration.tag === "class" && declaration.name === typeName,
        );
        if (cls?.tag === "class") {
          for (const member of cls.members) {
            if (
              member.tag !== "signature" &&
              member.tag !== "value" &&
              member.tag !== "foreign"
            )
              continue;
            const target = `${imported.module}.${member.name}`;
            if (!imported.qualified) names.set(member.name, target);
            names.set(
              `${imported.alias ?? imported.module}.${member.name}`,
              target,
            );
          }
        }
      }
    }
    return names;
  };
  for (let pass = 0; pass <= modules.length; pass++) {
    let changed = false;
    for (const module of modules) {
      const moduleExports = exports.get(module.name)!;
      const names = namesFor(module);
      for (const reexport of module.reexports)
        for (const [name, target] of exports.get(reexport) ?? [])
          if (!moduleExports.has(name)) {
            moduleExports.set(name, target);
            changed = true;
          }
      for (const exported of module.exports) {
        const target = names.get(exported);
        if (target && !moduleExports.has(exported)) {
          moduleExports.set(exported, target);
          changed = true;
        }
      }
    }
    if (!changed) break;
  }
  const constructors = new Map<string, Array<{ name: string; arity: number }>>();
  const recordFields = new Map<string, string[]>();
  for (const module of modules)
    for (const declaration of module.declarations)
      if (declaration.tag === "data") {
        constructors.set(
          declaration.name,
          declaration.constructors.map((constructorInfo) => {
            if (constructorInfo.fields)
              recordFields.set(constructorInfo.name, constructorInfo.fields);
            return {
              name: constructorInfo.name,
              arity: constructorInfo.arity,
            };
          }),
        );
      }
  const definedNames = new Set(
    modules.flatMap((module) =>
      module.declarations.flatMap((declaration) =>
        declaration.tag === "value" || declaration.tag === "foreign"
          ? [`${module.name}.${declaration.name}`]
          : [],
      ),
    ),
  );
  const scopes = new Map<string, EmitScope>(
    modules.map((module) => [
      module.name,
      {
        module: module.name,
        names: namesFor(module),
        definedNames,
        definesValue: new Set(
          module.declarations.flatMap((declaration) =>
            declaration.tag === "value" && declaration.name.startsWith("__pattern_")
              ? declaration.equations.flatMap((equation) =>
                  equation.patterns.flatMap(patternNames),
                )
              : declaration.tag === "value" || declaration.tag === "foreign"
                ? [declaration.name]
                : declaration.tag === "data"
                  ? declaration.constructors.flatMap((constructorInfo) => [
                      constructorInfo.name,
                      ...(constructorInfo.fields ?? []),
                    ])
                  : [],
          ),
        ),
        constructors,
        recordFields,
        signatures: new Map(
          module.declarations.flatMap((declaration) =>
            declaration.tag === "signature"
              ? [[declaration.name, declaration.type] as const]
              : declaration.tag === "foreign"
                ? [[declaration.name, declaration.signature.at(-1) ?? ""] as const]
                : [],
          ),
        ),
        emittedJs: new Set(),
        staticSites: [],
      },
    ]),
  );
  const runtimeNames = ["apply", "classMethod", "constructor", "field", "fieldAt", "foreignFunction", "force", "fromJSValAs", "h$hs_spt_insert", "io", "isTrue", "jsValue", "lazy", "prelude", "prop", "registerConstructorType", "registerDerivedJSON", "registerEnum", "registerEnumType", "registerInstance", "tuple", "updateRecord"];
  const emitModule = (module: Module): string => {
    const parent = scopes.get(module.name)!;
    const scope = { ...parent, emittedJs: new Set<string>() };
    const body = module.declarations.map((declaration) => emitDeclaration(declaration, scope));
    const registrations = [...new Map(scope.staticSites.map((site) => [site.key, site])).values()]
      .map((site) => {
        const [key1, key2, key3, key4] = staticPointerWords(site.key);
        return jCallStat(jVar("h$hs_spt_insert"), [jInt(key1), jInt(key2), jInt(key3), jInt(key4), jLazy(site.value)]);
      });
    // Printed once per module - the whole module body is real GHC.JS.Syntax
    // AST by this point (see the note above jVar's definition for the two
    // narrow, genuinely-unrepresentable exceptions).
    return Ppr.renderStat(jBlock([...registrations, ...body]));
  };
  const moduleSources = Object.fromEntries(modules.map((module) => {
    const runtimeImport = `${"../".repeat(module.name.split(".").length + 1)}runtime.js`;
    const importedModules = [...new Map(module.imports.map((item) => [item.module, item])).values()];
    const imports = importedModules
      .map((item) => {
        const imported = modules.find((candidate) => candidate.name === item.module);
        if (!imported) return "";
        const selected = item.exposing ?? declarationNames(imported);
        const names = [...new Set(selected)]
          .filter((name) => !item.hiding?.includes(name))
          .filter((name) => declarationNames(imported).includes(name))
          .map((name) => jsName(`${imported.name}.${name}`));
        if (!names.length) return "";
        const prefix = "../".repeat(Math.max(0, module.name.split(".").length - 1));
        const path = (prefix || "./") + item.module.replace(/\./g, "/") + ".js";
        return tsNamedImport(names, path);
      })
      .filter(Boolean);
    const body = emitModule(module);
    const publicNames = module.exports.length
      ? module.exports.filter((name) => declarationNames(module).includes(name))
      : declarationNames(module);
    const exported = [...new Set(publicNames.map((name) => jsName(`${module.name}.${name}`)))];
    return [module.name, `// Generated module ${module.name} from the typed Core pipeline.\n${tsNamedImport(runtimeNames, runtimeImport)}\n${imports.join("\n")}\n${body}\n${tsNamedExport(exported)}\n`];
  }));
  return {
    diagnostics,
    moduleSources,
    code: `// Generated by ghcts from linked modules: ${modules.map((module) => module.name).join(", ")}.\n${tsNamedImport(runtimeNames, "./runtime.js")}\n\n${modules.map((module) => emitModule(module)).join("\n")}\n\n${tsEntryConst(entry, jsName(`${entryModule.name}.${entry}`))}\n${tsDefaultExport(entry)}\n`,
  };
}
async function emit(
  targetDir: string,
  target: Target,
  source: string,
  assets: string[] = [],
  moduleSources: Record<string, string> = {},
): Promise<string[]> {
  await mkdir(targetDir, { recursive: true });
  const tsPath = join(targetDir, "main.ts");
  const jsPath = join(targetDir, "main.js");
  await writeFile(tsPath, source);
  await cp(
    join(packageRoot, "dist", "runtime.js"),
    join(targetDir, "runtime.js"),
  );
  await writeFile(
    jsPath,
    ts.transpileModule(source, {
      compilerOptions: {
        target: ts.ScriptTarget.ES2022,
        module: ts.ModuleKind.ES2022,
      },
    }).outputText,
  );
  const modulePaths: string[] = [];
  for (const [moduleName, moduleSource] of Object.entries(moduleSources)) {
    const moduleBase = join(targetDir, "modules", ...moduleName.split("."));
    await mkdir(dirname(`${moduleBase}.ts`), { recursive: true });
    await writeFile(`${moduleBase}.ts`, moduleSource);
    await writeFile(`${moduleBase}.js`, ts.transpileModule(moduleSource, { compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ES2022 } }).outputText);
    modulePaths.push(`${moduleBase}.ts`, `${moduleBase}.js`);
  }
  await writeFile(join(targetDir, "package.json"), '{"type":"module"}\n');
  const copied: string[] = [];
  const assetSources: string[] = [];
  for (const asset of assets) {
    const destination = join(targetDir, "js", asset.split("/").at(-1)!);
    await mkdir(dirname(destination), { recursive: true });
    await cp(asset, destination);
    copied.push(destination);
    let source = await readFile(asset, "utf8");
    assetSources.push(source);
  }
  if (assetSources.length) {
    const generated = await readFile(jsPath, "utf8");
    await writeFile(
      jsPath,
      // A replacer function, not a template-built replacement string: a
      // vendored JS asset is free-form minified code, and single-letter `$`
      // identifiers next to `&`/digits (e.g. `$&`, `$1`) are common there.
      // String.replace treats those sequences as backreferences when they
      // appear in a *replacement string*, which spliced the matched import
      // line back into the file wherever the asset happened to contain one.
      generated.replace(
        /^(import .* from ['"]\.\/runtime\.js['"];\s*)/m,
        (matched) => `${matched}\n${assetSources.join("\n")}\n`,
      ),
    );
  }
  const inlineRuntime = (await readFile(join(targetDir, "runtime.js"), "utf8"))
    .replace(/\bexport\s+/g, "");
  const inlineMain = (await readFile(jsPath, "utf8"))
    .replace(/^import .* from ['"]\.\/runtime\.js['"];\s*/m, "")
    .replace(/\bexport\s+const\s+main\b/, "const main")
    .replace(/\bexport\s+default\s+main\s*;?/, "");
  // GHCJS links js-sources into all.js.  Pack consumes this file the same
  // way mkLynxBundle consumes a `.jsexe/all.js`.  GHCJS `h$main` does not
  // run the Haskell main during script evaluation: it forks a thread and
  // schedules `h$mainLoop` with `setImmediate`.  Start the same way so
  // host `renderPage` hooks installed by js-sources run first.
  await writeFile(
    join(targetDir, "all.js"),
    `${inlineRuntime}\n${assetSources.join("\n")}\n${inlineMain}\n(function start(main) {\n  var ran = false;\n  function run() {\n    if (ran) return;\n    ran = true;\n    runFiber(main);\n  }\n  if (typeof setImmediate === "function") setImmediate(run);\n  if (typeof setTimeout === "function") setTimeout(run, 0);\n  else if (typeof queueMicrotask === "function") queueMicrotask(run);\n  else run();\n})(main);\n`,
  );
  if (target === "browser") {
    await writeFile(
      join(targetDir, "bootstrap.js"),
      `const report = cause => {
  console.error('ghcts browser startup failed', cause);
  const message = cause instanceof Error ? cause.stack || cause.message : String(cause);
  const panel = document.createElement('pre');
  panel.id = 'ghcts-startup-error';
  panel.textContent = 'ghcts browser startup failed\\n\\n' + message;
  panel.style.cssText = 'white-space:pre-wrap;margin:1rem;font:14px/1.4 monospace;color:#b00020';
  document.body.replaceChildren(panel);
};
try {
  const { main } = await import('./main.js');
  await main();
  document.getElementById('ghcts-loading')?.remove();
} catch (cause) { report(cause); }
`,
    );
    // Some development-browser configurations block every external `.js`
    // request. Keep the inspectable ESM files above, but also provide a
    // completely self-contained module in index.html so the app can start
    // without fetching bootstrap.js, runtime.js, or main.js.
    const inlineRuntime = (await readFile(join(targetDir, "runtime.js"), "utf8"))
      .replace(/\bexport\s+/g, "");
    const inlineMain = (await readFile(jsPath, "utf8"))
      .replace(/^import .* from ['"]\.\/runtime\.js['"];\s*/m, "")
      .replace(/\bexport\s+const\s+main\b/, "const main")
      .replace(/\bexport\s+default\s+main\s*;?/, "");
    const inlineBootstrap = `(async () => {
const report = cause => {
  console.error('ghcts browser startup failed', cause);
  const message = cause instanceof Error ? cause.stack || cause.message : String(cause);
  const panel = document.createElement('pre');
  panel.id = 'ghcts-startup-error';
  panel.textContent = 'ghcts browser startup failed\\n\\n' + message;
  panel.style.cssText = 'white-space:pre-wrap;margin:1rem;font:14px/1.4 monospace;color:#b00020';
  document.body.replaceChildren(panel);
};
try {
${inlineRuntime}
${assetSources.map((source) => `  ${source.replace(/\n/g, "\n  ")}`).join("\n")}
${inlineMain}
  await main();
  document.getElementById('ghcts-loading')?.remove();
} catch (cause) { report(cause); }
})();
`;
    await writeFile(
      join(targetDir, "index.html"),
      `<!doctype html><meta charset="utf-8"><title>ghcts app</title><p id="ghcts-loading">Loading ghcts app…</p><noscript><p>ghcts requires JavaScript enabled in this browser.</p></noscript><div id="root"></div><script>${inlineBootstrap}</script>`,
    );
    return [
      tsPath,
      jsPath,
      ...modulePaths,
      ...copied,
      join(targetDir, "all.js"),
      join(targetDir, "bootstrap.js"),
      join(targetDir, "index.html"),
    ];
  }
  return [tsPath, jsPath, ...modulePaths, ...copied, join(targetDir, "all.js")];
}
function link(
  entry: ParsedModule,
  modules: Map<string, ParsedModule>,
  diagnostics: Diagnostic[],
): ParsedModule[] {
  const order: ParsedModule[] = [];
  const visiting = new Set<string>();
  const done = new Set<string>();
  const visit = (module: ParsedModule) => {
    if (done.has(module.ast.name)) return;
    if (visiting.has(module.ast.name)) {
      diagnostics.push(
        error(
          "E_IMPORT_CYCLE",
          `Cyclic imports through ${module.ast.name}`,
          module.file,
        ),
      );
      return;
    }
    visiting.add(module.ast.name);
    for (const declaration of module.ast.imports)
      if (declaration.module !== "Prelude") {
        const dependency = modules.get(declaration.module);
        if (dependency) visit(dependency);
      }
    visiting.delete(module.ast.name);
    done.add(module.ast.name);
    order.push(module);
  };
  visit(entry);
  return order;
}
function constructorFields(
  name: string,
  fields: ReadonlyMap<string, string[]>,
): string[] {
  return fields.get(name) ?? fields.get(name.split(".").at(-1) ?? name) ?? [];
}
function expandRecordWildcards(
  value: unknown,
  fields: ReadonlyMap<string, string[]>,
): void {
  if (!value || typeof value !== "object") return;
  const item = value as Record<string, any>;
  if (item.tag === "record" && typeof item.name === "string" && item.wildcard) {
    const existing = new Set((item.fields ?? []).map((field: any) => field.name));
    for (const name of constructorFields(item.name, fields))
      if (!existing.has(name))
        item.fields.push({ name, pattern: { tag: "var", name, span: item.span } });
    item.wildcard = false;
  }
  if (item.tag === "record" && typeof item.constructor === "string" && item.wildcard) {
    const existing = new Set((item.fields ?? []).map((field: any) => field.name));
    for (const name of constructorFields(item.constructor, fields))
      if (!existing.has(name))
        item.fields.push({ name, value: { tag: "var", name, span: item.span } });
    item.wildcard = false;
  }
  for (const child of Object.values(item))
    Array.isArray(child) ? child.forEach((entry) => expandRecordWildcards(entry, fields)) : expandRecordWildcards(child, fields);
}
function expandRecordPatterns(modules: Module[]): void {
  const fields = new Map<string, string[]>();
  for (const module of modules)
    for (const declaration of module.declarations)
      if (declaration.tag === "data")
        for (const constructor of declaration.constructors)
          if (constructor.fields) fields.set(constructor.name, constructor.fields);
  modules.forEach((module) => expandRecordWildcards(module, fields));
}
export async function compileProject(
  options: CompileProjectOptions,
): Promise<CompileResult> {
  const project = resolve(options.project);
  const configResult = await readConfig(project);
  if (!configResult.config)
    return { diagnostics: configResult.diagnostics, outputPaths: [] };
  const loaded = await loadModules(project, configResult.config);
  const origins = Object.fromEntries(
    [...loaded.modules].map(([name, module]) => [name, module.file]),
  );
  const diagnostics = [...configResult.diagnostics, ...loaded.diagnostics];
  const entry = loaded.modules.get(configResult.config.entry.module);
  if (!entry)
    diagnostics.push(
      error(
        "E_ENTRY",
        `Entry module ${configResult.config.entry.module} was not found`,
        join(project, "ghcts.json"),
      ),
    );
  if (
    entry &&
    diagnostics.every((diagnostic) => diagnostic.severity !== "error")
  ) {
    const linked = link(entry, loaded.modules, diagnostics);
    expandRecordPatterns(linked.map((module) => module.ast));
    diagnostics.push(
      ...checkModules(
        linked
          .map((module) => ({ module: module.ast, file: module.file }))
          .filter(Boolean),
        [{ module: entry.ast.name, name: configResult.config.entry.export }],
      ).diagnostics,
    );
    const lowered = diagnostics.some(
      (diagnostic) => diagnostic.severity === "error",
    )
      ? { diagnostics: [] }
      : lower(
          linked.map((module) => module.ast),
          entry.ast,
          configResult.config.entry.export,
          entry.file,
        );
    diagnostics.push(...lowered.diagnostics);
    if (lowered.code && options.emit !== false) {
      const outputPaths: string[] = [];
      const assets = await jsSources(
        project,
        configResult.config.dependencies,
        cppDefines(configResult.config),
      );
      for (const target of configResult.config.targets)
        outputPaths.push(
          ...(await emit(
            resolve(project, configResult.config.outDir, target),
            target,
            lowered.code,
            assets,
            lowered.moduleSources,
          )),
        );
      return {
        config: configResult.config,
        diagnostics,
        outputPaths,
        moduleOrigins: origins,
      };
    }
  }
  return {
    config: configResult.config,
    diagnostics,
    outputPaths: [],
    moduleOrigins: origins,
  };
}
