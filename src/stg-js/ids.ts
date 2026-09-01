/** Ported from GHC/StgToJS/Ids.hs - generation of JS identifiers for STG Ids.
 *
 * ghcts's `Binder` (src/stg.ts) plays the role of GHC's Core `Id`.
 *
 * The symbol-construction helpers below (`intBS` .. `mkFreshJsSymbol`) and the
 * z-encoder they rest on properly belong to GHC.StgToJS.Symbols and
 * GHC.Utils.Encoding. They live here rather than in `src/stg-js/symbols.ts`
 * because that file is generated wholesale by `scripts/gen-symbols.mjs`, which
 * only extracts literal symbol names and would clobber anything hand-written.
 */
import type { Binder, DataCon } from "../stg.js";
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { Var } from "../js/jstg-syntax.js";
import { decl } from "../js/make.js";
import { mconcatJStgStat } from "../js/jstg-syntax.js";
import type { GenState, Module } from "./monad.js";
import { getGlobalIdCache, idKey, IdType, setGlobalIdCache } from "./monad.js";

// ---------------------------------------------------------------------------
// GHC.Utils.Encoding: z-encoding
// ---------------------------------------------------------------------------

const zEncodeCh: Readonly<Record<string, string>> = {
  // Constructors
  "(": "ZL",
  ")": "ZR",
  "[": "ZM",
  "]": "ZN",
  ":": "ZC",
  Z: "ZZ",
  // Variables
  z: "zz",
  "&": "za",
  "|": "zb",
  "^": "zc",
  $: "zd",
  "=": "ze",
  ">": "zg",
  "#": "zh",
  ".": "zi",
  "<": "zl",
  "-": "zm",
  "!": "zn",
  "+": "zp",
  "'": "zq",
  "\\": "zr",
  "/": "zs",
  "*": "zt",
  _: "zu",
  "%": "zv",
};

const unencodedChar = (c: string): boolean => c !== "Z" && c !== "z" && /^[a-zA-Z0-9]$/.test(c);

const encodeAsUnicodeChar = (c: string): string => {
  const hex = `${(c.codePointAt(0) ?? 0).toString(16)}U`;
  return `z${/^[0-9]/.test(hex) ? hex : `0${hex}`}`;
};

const encodeCh = (c: string): string => {
  if (unencodedChar(c)) return c;
  return zEncodeCh[c] ?? encodeAsUnicodeChar(c);
};

/** Tuple names get their own encoding (Z2T, Z3H, ...) and no other encoding
 * starts with `Z<digit>`. */
function maybeTuple(cs: string): string | undefined {
  if (cs === "(##)") return "Z0H";
  if (cs === "()") return "Z0T";
  const unboxed = /^\(#(,*)#\)/.exec(cs);
  if (unboxed !== null) return `Z${unboxed[1].length + 1}H`;
  const boxed = /^\((,*)\)/.exec(cs);
  if (boxed !== null) return `Z${boxed[1].length + 1}T`;
  return undefined;
}

export function zEncodeString(cs: string): string {
  const tuple = maybeTuple(cs);
  if (tuple !== undefined) return tuple;
  // A leading digit is always escaped, otherwise names like "9pH-0.1" would
  // produce linker errors.
  return [...cs]
    .map((c, i) => (i === 0 && c >= "0" && c <= "9" ? encodeAsUnicodeChar(c) : encodeCh(c)))
    .join("");
}

// ---------------------------------------------------------------------------
// GHC.StgToJS.Symbols: symbol construction
// ---------------------------------------------------------------------------

/** Hexadecimal representation of a 64-bit word. Used for uniques. */
export const word64BS = (w: bigint): string => w.toString(16);

/** Hexadecimal representation of an int. Used for the sub indices. */
export const intBS = (i: number): string => word64BS(BigInt(i));

/** Return z-encoded unit:module. "ZC" is the z-encoding of ":". */
export const unitModuleStringZ = (mod: Module): string =>
  `${zEncodeString(mod.unitId)}ZC${zEncodeString(mod.moduleName)}`;

/** Make JS symbol corresponding to the given Haskell symbol in the given
 * module. "zi" is the z-encoding of ".". */
export const mkJsSymbol = (exported: boolean, mod: Module, s: string): string =>
  `${exported ? "h$" : "h$$"}${unitModuleStringZ(mod)}zi${zEncodeString(s)}`;

/** Make JS symbol for given module and unique. */
export const mkFreshJsSymbol = (mod: Module, i: number): string => `h$$${unitModuleStringZ(mod)}_${intBS(i)}`;

// ---------------------------------------------------------------------------
// GHC.StgToJS.Ids
// ---------------------------------------------------------------------------

/** GHC uses `typeSize (idType i)`; ghcts has no Core types, so a Binder
 * records directly how many JS values it occupies (src/stg.ts). */
const typeSize = (i: Binder): number => i.arity ?? 1;

/** GHC's `unpkUnique` splits a Unique into a class character and a 64-bit
 * number, and both go into the suffix of a local Id's symbol. ghcts's Binder
 * uniques carry no class, so every local Id gets the same tag. */
const uniqueClass = "u";

/** Get fresh unique number */
export function freshUnique(s: GenState): number {
  // No need for an atomic fetch-and-add: G is single-threaded.
  return s.gsId++;
}

/** Get fresh module-local Ident of the form: h$$unit:module_uniq */
export function freshIdent(s: GenState): Ident {
  return name(mkFreshJsSymbol(s.gsModule, freshUnique(s)));
}

/** Generate unique Ident for the given ID (uncached!)
 *
 * The ident has the following forms:
 *
 *    global Id: h$unit:module.name[_num][_type_suffix]
 *    local Id: h$$unit:module.name[_num][_type_suffix]_uniq
 *
 * Note that the string is z-encoded except for "_" delimiters.
 *
 * Optional "_type_suffix" can be "_e" for IdEntry, "_con_e" for IdConEntry.
 *
 * Optional "_num" is used for Haskell Ids that require several JS variables:
 * 64-bit numbers (Word64#, Int64#), Addr#, StablePtr#, unboxed tuples, etc.
 */
export function makeIdentForId(
  i: Binder,
  num: number | undefined,
  idType: IdType,
  currentModule: Module,
): Ident {
  const exported = i.exported === true;
  if (i.name === "JSVal") {
    const suffixType = idType === IdType.IdPlain ? "" : idType === IdType.IdEntry ? "_e" : "_con_e";
    const suffixNum = num === undefined ? "" : `_${intBS(num)}`;
    return name(`h$ghczminternalZCGHCziInternalziJSziPrimziJSVal${suffixNum}${suffixType}`);
  }
  // GHC uses the Id's own defining module when it is exported; ghcts Binders
  // carry no Name, hence no defining module, so the current one is always used.
  const mod = currentModule;
  const suffixNum = num === undefined ? "" : `_${intBS(num)}`;
  const suffixType = idType === IdType.IdPlain ? "" : idType === IdType.IdEntry ? "_e" : "_con_e";
  // A real top-level declaration is exported *and* has a real source name, so
  // its OccName is already distinct from every sibling and the name-only
  // symbol GHC's own convention gives it never collides. `i.internal` marks
  // the other case: core-to-stg.ts's `atom()` floats a literal-constructor
  // RHS to the top level (Sinker.hs's `alwaysSinkable`) under the single
  // literal name "t" every time, and marks it `exported` only so liveness
  // analysis treats it as global (see the field's own doc comment) - it is
  // not a real source declaration and two of them collide on the same
  // name-only symbol otherwise, silently aliasing unrelated literals.
  const suffixUniq =
    exported && i.internal !== true ? "" : `_${uniqueClass}_${word64BS(BigInt(i.unique))}`;
  return name(mkJsSymbol(exported, mod, i.name) + suffixNum + suffixType + suffixUniq);
}

/** Retrieve the cached Ident for the given Id if there is one. Otherwise make
 * a new one with 'makeIdentForId' and cache it. */
export function cachedIdentForId(
  s: GenState,
  i: Binder,
  mi: number | undefined,
  idType: IdType,
): Ident {
  const key = idKey(i.unique, mi ?? 0, idType);

  let ident = s.gsIdents.get(key);
  if (ident === undefined) {
    ident = makeIdentForId(i, mi, idType, s.gsModule);
    s.gsIdents.set(key, ident);
    // The symbol is a FastString in GHC, and interning one hands out the next
    // unique. `globalOccs` depends on that order; record it here, the only
    // place a symbol for an Id is built.
    if (!s.gsIdentMint.has(ident)) s.gsIdentMint.set(ident, s.gsIdentMint.size);
  }

  // Now update the GlobalId cache, if required.
  const updateGlobalCache = i.exported === true && mi === undefined && idType === IdType.IdPlain;
  if (updateGlobalCache) {
    const gidc = getGlobalIdCache(s);
    if (!gidc.has(ident)) {
      gidc.set(ident, { key, id: i });
      setGlobalIdCache(s, gidc);
    }
  }

  return ident;
}

/** Retrieve default Ident for the given Id */
export const identForId = (s: GenState, i: Binder): Ident => cachedIdentForId(s, i, undefined, IdType.IdPlain);

/** Retrieve default Ident for the given Id with sub index.
 *
 * Some types - Word64, Addr#, unboxed tuples - have more than one
 * corresponding JS var, hence the sub index identifying each JS variable. */
export const identForIdN = (s: GenState, i: Binder, n: number): Ident =>
  cachedIdentForId(s, i, n, IdType.IdPlain);

/** Retrieve all the idents for the given Id */
export function identsForId(s: GenState, i: Binder): Ident[] {
  const size = typeSize(i);
  if (size === 0) return [];
  if (size === 1) return [identForId(s, i)];
  return Array.from({ length: size }, (_, k) => identForIdN(s, i, k + 1));
}

/** Retrieve entry Ident for the given Id */
export const identForEntryId = (s: GenState, i: Binder): Ident => cachedIdentForId(s, i, undefined, IdType.IdEntry);

/** Retrieve datacon entry Ident for the given Id. Different name than the
 * datacon wrapper. */
export const identForDataConEntryId = (s: GenState, i: Binder): Ident =>
  cachedIdentForId(s, i, undefined, IdType.IdConEntry);

/** Retrieve default variable name for the given Id */
export const varForId = (s: GenState, i: Binder): JStgExpr => Var(identForId(s, i));

/** Retrieve default variable name for the given Id with sub index */
export const varForIdN = (s: GenState, i: Binder, n: number): JStgExpr => Var(identForIdN(s, i, n));

/** Retrieve all the JS vars for the given Id */
export function varsForId(s: GenState, i: Binder): JStgExpr[] {
  const size = typeSize(i);
  if (size === 0) return [];
  if (size === 1) return [varForId(s, i)];
  return Array.from({ length: size }, (_, k) => varForIdN(s, i, k + 1));
}

/** Retrieve entry variable name for the given Id */
export const varForEntryId = (s: GenState, i: Binder): JStgExpr => Var(identForEntryId(s, i));

/** Retrieve datacon entry variable name for the given Id */
export const varForDataConEntryId = (s: GenState, i: Binder): JStgExpr => Var(identForDataConEntryId(s, i));

/** GHC's `dataConWorkId`: the Id of a DataCon's worker. ghcts's DataCon
 * (src/stg.ts) carries no such Binder, so one is derived from the DataCon
 * itself - same name and unique, and exported, matching GHC where a worker is
 * always as visible as its constructor. */
const dataConWorkId = (d: DataCon): Binder => ({ name: d.name, unique: d.unique, exported: true });

/** Retrieve datacon worker entry Ident for the given datacon */
export const identForDataConWorker = (s: GenState, d: DataCon): Ident =>
  identForDataConEntryId(s, dataConWorkId(d));

/** Retrieve datacon worker entry variable name for the given datacon */
export const varForDataConWorker = (s: GenState, d: DataCon): JStgExpr =>
  varForDataConEntryId(s, dataConWorkId(d));

/** Declare all js vars for the id */
export function declVarsForId(s: GenState, i: Binder): JStgStat {
  return mconcatJStgStat(identsForId(s, i).map(decl));
}
