/** The hand-written half of GHC's JavaScript RTS.
 *
 * `src/stg-js/rts.ts` reproduces the half GHC *generates* from Haskell. This
 * is the other half: the files under `rts/js/` that GHC ships as ordinary
 * package JS sources. The linker concatenates them into `lib.js` rather than
 * `rts.js`, which is why they never showed up in the byte-for-byte diff -
 * but generated code calls into them constantly (`h$o`, `h$init_closure`,
 * `h$sti`, `h$stc`, `h$addCAF`, `h$rs`, `h$newByteArray`, `h$forkThread`),
 * so nothing ghcts emits runs without them.
 *
 * Nothing here is ported. These are GHC's own files, used verbatim, in the
 * order `rts/rts.cabal`'s `js-sources` lists - which is the order the linker
 * emits them and the order the oracle's lib.js confirms.
 *
 * The only code written here is CPP, because the sources carry
 * `//#OPTIONS: CPP` and GHC runs them through a real C preprocessor
 * (`GHC.StgToJS.Linker.Linker.jsLinkBinary` -> `doCpp` with `SCPJsCpp`),
 * after prepending the macro prelude that `genCommonCppDefs` builds.
 */
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import type { StgToJSConfig } from "./types.js";

const packageRoot = dirname(dirname(dirname(new URL(import.meta.url).pathname)));

/** Where GHC's own RTS sources live. */
export const rtsJsDir = join(packageRoot, "references/ghc/rts/js");

/** `js-sources` from rts/rts.cabal, in order. The linker emits them in this
 * order and later files depend on earlier ones, so it is not incidental. */
export const rtsJsFiles = [
  "config.js",
  "structs.js",
  "arith.js",
  "compact.js",
  "debug.js",
  "enum.js",
  "environment.js",
  "eventlog.js",
  "gc.js",
  "goog.js",
  "hscore.js",
  "md5.js",
  "mem.js",
  "node-exports.js",
  "object.js",
  "profiling.js",
  "rts.js",
  "stableptr.js",
  "staticpointer.js",
  "stm.js",
  "string.js",
  "thread.js",
  "unicode.js",
  "verify.js",
  "weak.js",
  "globals.js",
  "time.js",
];

// ---------------------------------------------------------------------------
// genCommonCppDefs
// ---------------------------------------------------------------------------

/** `ctJsName`/`ctNum` from GHC.StgToJS.Types, in `[minBound..maxBound]` order
 * (the declaration order of `data ClosureType`, which is not the numeric
 * order - Con is 2 but declared after Pap, which is 3). */
const closureTypes: ReadonlyArray<readonly [string, number]> = [
  ["CLOSURE_TYPE_THUNK", 0],
  ["CLOSURE_TYPE_FUN", 1],
  ["CLOSURE_TYPE_PAP", 3],
  ["CLOSURE_TYPE_CON", 2],
  ["CLOSURE_TYPE_BLACKHOLE", 5],
  ["CLOSURE_TYPE_STACKFRAME", -1],
];

/** `threadStatusJsName`/`threadStatusNum`, same ordering rule. */
const threadStatuses: ReadonlyArray<readonly [string, number]> = [
  ["THREAD_RUNNING", 0],
  ["THREAD_BLOCKED", 1],
  ["THREAD_FINISHED", 16],
  ["THREAD_DIED", 17],
];

/** `genMkTup`: `MK_TUPn` for n in 2..10.
 *
 * The constructor symbol is the z-encoded worker of the boxed n-tuple's data
 * constructor; GHC computes it through `makeIdentForId`, but for tuples the
 * result is mechanical and the oracle's lib.js confirms the spelling. */
function genMkTup(profiling: boolean, n: number): string {
  const xs = Array.from({ length: n }, (_, i) => `x${i + 1}`);
  return (
    `#define MK_TUP${n}(${xs.join(",")})` +
    `(h$c${n}(h$ghczmprimZCGHCziTupleziZ${n}T_con_e,` +
    xs.map((x) => `(${x})`).join(",") +
    (profiling ? ",h$currentThread?h$currentThread.ccs:h$CCS_SYSTEM" : "") +
    "))\n"
  );
}

/** Port of `genCommonCppDefs` in
 * `compiler/GHC/StgToJS/Linker/Utils.hs`. GHC prepends this to every RTS JS
 * file before running CPP over it. */
export function genCommonCppDefs(profiling: boolean): string {
  const mkIntDef = (n: string, v: number) => `#define ${n} (${v})\n`;
  const parts: string[] = [];
  for (const [n, v] of closureTypes) parts.push(mkIntDef(n, v));
  for (const [n, v] of threadStatuses) parts.push(mkIntDef(n, v));

  for (let n = 2; n <= 10; n++) parts.push(genMkTup(profiling, n));

  parts.push("#define TUP2_1(x) ((x).d1)\n");
  parts.push("#define TUP2_2(x) ((x).d2)\n");

  parts.push(
    profiling
      ? "#define MK_JSVAL(x) (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x), h$CCS_SYSTEM))\n"
      : "#define MK_JSVAL(x) (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x)))\n",
  );
  parts.push("#define JSVAL_VAL(x) ((x).d1)\n");

  parts.push(
    profiling
      ? "#define MK_JSEXCEPTION(msg,hsMsg) (h$c2(h$ghczminternalZCGHCziInternalziJSziPrimziJSException_con_e,(msg),(hsMsg),h$CCS_SYSTEM))\n"
      : "#define MK_JSEXCEPTION(msg,hsMsg) (h$c2(h$ghczminternalZCGHCziInternalziJSziPrimziJSException_con_e,(msg),(hsMsg)))\n",
  );

  parts.push(
    "#define HS_JSEXCEPTION_EXCEPTION h$ghczminternalZCGHCziInternalziJSziPrimzizdfExceptionJSException\n",
  );

  parts.push(
    profiling
      ? "#define MK_SOMEEXCEPTION(dict,except) (h$c2(h$ghczminternalZCGHCziInternalziExceptionziTypeziSomeException_con_e,(dict),(except),h$CCS_SYSTEM))\n"
      : "#define MK_SOMEEXCEPTION(dict,except) (h$c2(h$ghczminternalZCGHCziInternalziExceptionziTypeziSomeException_con_e,(dict),(except)))\n",
  );

  parts.push(
    profiling
      ? "#define MK_PTR(val,offset) (h$c2(h$ghczminternalZCGHCziInternalziPtrziPtr_con_e, (val), (offset), h$CCS_SYSTEM))\n"
      : "#define MK_PTR(val,offset) (h$c2(h$ghczminternalZCGHCziInternalziPtrziPtr_con_e, (val), (offset)))\n",
  );

  parts.push(
    "#define PUT_ADDR(a,o,va,vo) if (!(a).arr) (a).arr = []; (a).arr[o] = va; (a).dv.setInt32(o,vo,true);\n",
  );
  parts.push(
    "#define GET_ADDR(a,o,ra,ro) var ra = (((a).arr && (a).arr[o]) ? (a).arr[o] : null); var ro = (a).dv.getInt32(o,true);\n",
  );

  parts.push("#define HS_NOTHING h$ghczminternalZCGHCziInternalziMaybeziNothing\n");
  parts.push(
    "#define IS_NOTHING(cl) ((cl).f === h$ghczminternalZCGHCziInternalziMaybeziNothing_con_e)\n",
  );
  parts.push("#define IS_JUST(cl) ((cl).f === h$ghczminternalZCGHCziInternalziMaybeziJust_con_e)\n");
  parts.push("#define JUST_VAL(jj) ((jj).d1)\n");
  parts.push(
    profiling
      ? "#define MK_JUST(val) (h$c1(h$ghczminternalZCGHCziInternalziMaybeziJust_con_e, (val), h$CCS_SYSTEM))\n"
      : "#define MK_JUST(val) (h$c1(h$ghczminternalZCGHCziInternalziMaybeziJust_con_e, (val)))\n",
  );

  parts.push("#define HS_NIL h$ghczmprimZCGHCziTypesziZMZN\n");
  parts.push("#define HS_NIL_CON h$ghczmprimZCGHCziTypesziZMZN_con_e\n");
  parts.push("#define IS_CONS(cl) ((cl).f === h$ghczmprimZCGHCziTypesziZC_con_e)\n");
  parts.push("#define IS_NIL(cl) ((cl).f === h$ghczmprimZCGHCziTypesziZMZN_con_e)\n");
  parts.push("#define CONS_HEAD(cl) ((cl).d1)\n");
  parts.push("#define CONS_TAIL(cl) ((cl).d2)\n");
  if (profiling) {
    parts.push(
      "#define MK_CONS(head,tail) (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (head), (tail), h$CCS_SYSTEM))\n",
    );
    parts.push(
      "#define MK_CONS_CC(head,tail,cc) (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (head), (tail), (cc)))\n",
    );
  } else {
    parts.push(
      "#define MK_CONS(head,tail) (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (head), (tail)))\n",
    );
    parts.push(
      "#define MK_CONS_CC(head,tail,cc) (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (head), (tail)))\n",
    );
  }

  parts.push("#define DATA_TEXT_ARRAY(x) ((x).d1)\n");
  parts.push("#define DATA_TEXT_OFFSET(x) ((x).d2.d1)\n");
  parts.push("#define DATA_TEXT_LENGTH(x) ((x).d2.d2)\n");

  parts.push("#define LAZY_TEXT_IS_CHUNK(x) ((x).f.a === 2)\n");
  parts.push("#define LAZY_TEXT_IS_NIL(x) ((x).f.a === 1)\n");
  parts.push("#define LAZY_TEXT_CHUNK_HEAD(x) ((x))\n");
  parts.push("#define LAZY_TEXT_CHUNK_TAIL(x) ((x).d2.d3)\n");

  parts.push(
    "#define IS_BLACKHOLE(x) (typeof (x) === 'object' && (x) && (x).f && (x).f.t === CLOSURE_TYPE_BLACKHOLE)\n",
  );
  parts.push("#define BLACKHOLE_TID(bh) ((bh).d1)\n");
  parts.push("#define SET_BLACKHOLE_TID(bh,tid) ((bh).d1 = (tid))\n");
  parts.push("#define BLACKHOLE_QUEUE(bh) ((bh).d2)\n");
  parts.push("#define SET_BLACKHOLE_QUEUE(bh,val) ((bh).d2 = (val))\n");

  parts.push(
    "#define MAKE_RESUMABLE(closure,stack) { (closure).f = h$resume_e; (closure).d1 = (stack), (closure).d2 = null; }\n",
  );

  parts.push("#define MK_UPD_THUNK(closure) h$c1(h$upd_thunk_e,(closure))\n");

  parts.push("#define IS_THUNK(x) ((x).f.t === CLOSURE_TYPE_THUNK)\n");
  parts.push("#define CONSTR_TAG(x) ((x).f.a)\n");

  parts.push(
    "#define IS_WRAPPED_NUMBER(val) ((typeof(val)==='object')&&(val).f === h$unbox_e)\n",
  );
  parts.push("#define UNWRAP_NUMBER(val) ((typeof(val) === 'number')?(val):(val).d1)\n");

  if (profiling) {
    parts.push("#define MK_LAZY(fun) (h$c1(h$lazy_e, (fun), h$CCS_SYSTEM))\n");
    parts.push("#define MK_LAZY_CC(fun,cc) (h$c1(h$lazy_e, (fun), (cc)))\n");
  } else {
    parts.push("#define MK_LAZY(fun) (h$c1(h$lazy_e, (fun)))\n");
    parts.push("#define MK_LAZY_CC(fun,cc) (h$c1(h$lazy_e, (fun)))\n");
  }

  if (profiling) {
    parts.push("#define MK_DATA1_1(val) (h$c1(h$data1_e, (val), h$CCS_SYSTEM))\n");
    parts.push("#define MK_DATA1_2(val1,val2) (h$c2(h$data1_e, (val1), (val2), h$CCS_SYSTEM))\n");
    parts.push("#define MK_DATA2_1(val) (h$c1(h$data2_e, (val), h$CCS_SYSTEM))\n");
    // Not a typo: GHC's profiled MK_DATA2_2 really does build a h$data1_e.
    parts.push("#define MK_DATA2_2(val1,val2) (h$c2(h$data1_e, (val1), (val2), h$CCS_SYSTEM))\n");
    parts.push("#define MK_SELECT1(val) (h$c1(h$select1_e, (val), h$CCS_SYSTEM))\n");
    parts.push("#define MK_SELECT2(val) (h$c1(h$select2_e, (val), h$CCS_SYSTEM))\n");
    parts.push("#define MK_AP1(fun,val) (h$c2(h$ap1_e, (fun), (val), h$CCS_SYSTEM))\n");
    parts.push("#define MK_AP2(fun,val1,val2) (h$c3(h$ap2_e, (fun), (val1), (val2), h$CCS_SYSTEM))\n");
    parts.push(
      "#define MK_AP3(fun,val1,val2,val3) (h$c4(h$ap3_e, (fun), (val1), (val2), (val3), h$CCS_SYSTEM))\n",
    );
  } else {
    parts.push("#define MK_DATA1_1(val) (h$c1(h$data1_e, (val)))\n");
    parts.push("#define MK_DATA1_2(val1,val2) (h$c2(h$data1_e, (val1), (val2)))\n");
    parts.push("#define MK_DATA2_1(val) (h$c1(h$data2_e, (val)))\n");
    parts.push("#define MK_DATA2_2(val1,val2) (h$c2(h$data2_e, (val1), (val2)))\n");
    parts.push("#define MK_SELECT1(val) (h$c1(h$select1_e, (val)))\n");
    parts.push("#define MK_SELECT2(val) (h$c1(h$select2_e, (val)))\n");
    parts.push("#define MK_AP1(fun,val) (h$c2(h$ap1_e,(fun),(val)))\n");
    parts.push("#define MK_AP2(fun,val1,val2) (h$c3(h$ap2_e,(fun),(val1),(val2)))\n");
    parts.push("#define MK_AP3(fun,val1,val2,val3) (h$c4(h$ap3_e, (fun), (val1), (val2), (val3)))\n");
  }

  // unboxed tuple returns: RETURN_UBX_TUPn writes x2.. into h$ret1.. and
  // returns x1.
  for (let n = 2; n <= 10; n++) {
    const xs = Array.from({ length: n }, (_, i) => `x${i + 1}`);
    const sets = xs.slice(1).map((x, i) => `h$ret${i + 1} = (${x}); `).join("");
    parts.push(`#define RETURN_UBX_TUP${n}(${xs.join(",")}) { ${sets}return (x1); }\n`);
  }

  parts.push("#define RETURN_INT64(h,l) RETURN_UBX_TUP2((h)|0,(l)>>>0)\n");
  parts.push("#define RETURN_WORD64(h,l) RETURN_UBX_TUP2((h)>>>0,(l)>>>0)\n");
  parts.push("#define RETURN_ADDR(a,o) RETURN_UBX_TUP2(a,o)\n");

  // CALL_UBX_TUPn reads the extra results back out of h$ret1..
  for (let n = 2; n <= 10; n++) {
    const rs = Array.from({ length: n }, (_, i) => `r${i + 1}`);
    const gets = rs.slice(1).map((r, i) => `(${r}) = h$ret${i + 1}; `).join("");
    parts.push(`#define CALL_UBX_TUP${n}(${rs.join(",")},c) { (r1) = (c); ${gets}}\n`);
  }

  return parts.join("");
}

// ---------------------------------------------------------------------------
// The preprocessor
// ---------------------------------------------------------------------------

/** A preprocessing token. Whitespace and comments are tokens too, so that
 * text the preprocessor does not touch is reproduced byte for byte. */
interface Tok {
  readonly text: string;
  /** Whitespace or comment - skipped when looking for `(` after a macro name,
   * and elided around `##`. */
  readonly ws: boolean;
  /** A comment. `ws` for adjacency purposes, but rendered verbatim: GHC passes
   * `-CC` so cpp keeps comments untouched. */
  readonly comment?: boolean;
  /** Identifier - the only thing that can name a macro or a parameter. */
  readonly id: boolean;
}

interface Macro {
  /** Parameter names, or null for an object-like macro. */
  readonly params: string[] | null;
  /** Name of the trailing `args...` parameter, if the macro is variadic. */
  readonly variadic: string | null;
  readonly body: Tok[];
}

const tok = (text: string, ws = false, id = false): Tok => ({ text, ws, id });

/** Tokenize far enough to preprocess correctly: identifiers must be whole
 * (so `h$c2` is never mistaken for `h$c` + `2`), and strings and comments must
 * be opaque, because GHC runs a standard - not `-traditional` - cpp over these
 * files and standard cpp does not expand macros inside either. */
function tokenize(src: string): Tok[] {
  const out: Tok[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i]!;
    if (c === " " || c === "\t" || c === "\n" || c === "\r") {
      let j = i;
      while (j < src.length && /[ \t\n\r]/.test(src[j]!)) j++;
      out.push(tok(src.slice(i, j), true));
      i = j;
    } else if (c === "/" && src[i + 1] === "/") {
      let j = src.indexOf("\n", i);
      if (j < 0) j = src.length;
      out.push({ text: src.slice(i, j), ws: true, id: false, comment: true });
      i = j;
    } else if (c === "/" && src[i + 1] === "*") {
      let j = src.indexOf("*/", i + 2);
      j = j < 0 ? src.length : j + 2;
      out.push({ text: src.slice(i, j), ws: true, id: false, comment: true });
      i = j;
    } else if (c === '"' || c === "'" || c === "`") {
      let j = i + 1;
      while (j < src.length && src[j] !== c) {
        if (src[j] === "\\") j++;
        else if (src[j] === "\n" && c !== "`") break; // unterminated: bail out
        j++;
      }
      out.push(tok(src.slice(i, Math.min(j + 1, src.length))));
      i = Math.min(j + 1, src.length);
    } else if (/[A-Za-z_$]/.test(c)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_$]/.test(src[j]!)) j++;
      out.push(tok(src.slice(i, j), false, true));
      i = j;
    } else if (/[0-9]/.test(c)) {
      let j = i;
      while (j < src.length && /[0-9A-Za-z.]/.test(src[j]!)) j++;
      out.push(tok(src.slice(i, j)));
      i = j;
    } else if (c === "#" && src[i + 1] === "#") {
      out.push(tok("##"));
      i += 2;
    } else {
      out.push(tok(c));
      i++;
    }
  }
  return out;
}

/** How cpp renders a whitespace run.
 *
 * It reproduces each line's leading indentation (one space per tab) but
 * collapses every other horizontal whitespace run to a single space - the
 * oracle's lib.js shows this, structs.js's column-aligned assignments come out
 * single-spaced. `-P` (GHC passes it, `cppLinePragmas = False`) additionally
 * drops blank lines instead of padding the output to preserve line numbers.
 * Blank lines *inside* a comment survive, because comments are their own
 * tokens and are emitted verbatim under `-CC`. */
const renderWs = (text: string): string => {
  const nl = text.lastIndexOf("\n");
  if (nl < 0) return " ";
  return "\n" + text.slice(nl + 1).replace(/\t/g, " ");
};

/** Newlines inside a comment are hidden behind this while blank lines are
 * dropped, so a blank line in a block comment survives (`-CC` keeps comments
 * exactly as written). It cannot occur in the sources. */
const NL_IN_COMMENT = "\u0000";

const render = (toks: Tok[]): string => {
  const raw = toks
    .map((t) =>
      t.comment ? t.text.split("\n").join(NL_IN_COMMENT) : t.ws ? renderWs(t.text) : t.text,
    )
    .join("");
  // A line left holding only indentation - a macro that expanded to nothing,
  // which is what every tracing macro does in a default build - is a blank
  // line to cpp, and `-P` drops it.
  return raw
    .split("\n")
    .filter((l, i) => i === 0 || l.trim() !== "")
    .join("\n")
    .split(NL_IN_COMMENT)
    .join("\n");
};

/** Parse a `#define` body's parameter list and replacement list. Whitespace in
 * the replacement list is normalised to a single space, which is what cpp
 * emits and what the oracle's one-line macro expansions show. */
function parseDefine(rest: string): [string, Macro] | null {
  const m = rest.match(/^([A-Za-z_$][A-Za-z0-9_$]*)/);
  if (!m) return null;
  const name = m[1]!;
  let tail = rest.slice(name.length);
  let params: string[] | null = null;
  let variadic: string | null = null;
  // A function-like macro is one whose `(` touches the name with no space.
  if (tail.startsWith("(")) {
    const close = tail.indexOf(")");
    const inner = tail.slice(1, close).trim();
    tail = tail.slice(close + 1);
    params = inner === "" ? [] : inner.split(",").map((p) => p.trim());
    const last = params[params.length - 1];
    // GNU named variadic: `#define TRACE(args...)`.
    if (last && last.endsWith("...")) {
      variadic = last.slice(0, -3);
      params[params.length - 1] = variadic;
    }
  }
  const body = tokenize(tail.trim()).map((t) => (t.ws ? tok(" ", true) : t));
  return [name, { params, variadic, body }];
}

/** Substitute arguments into a replacement list and apply `##`. */
function substitute(
  macro: Macro,
  raw: Tok[][],
  expanded: Tok[][],
): Tok[] {
  const params = macro.params ?? [];
  const idx = (t: Tok) => (t.id ? params.indexOf(t.text) : -1);
  const body = macro.body;
  // Which body positions are `##` operands: those neighbour a `##` ignoring
  // whitespace. Operands of `##` use the unexpanded argument.
  const pasted = new Set<number>();
  for (let i = 0; i < body.length; i++) {
    if (body[i]!.text !== "##") continue;
    for (let j = i - 1; j >= 0 && body[j]!.ws; j--);
    let l = i - 1;
    while (l >= 0 && body[l]!.ws) l--;
    let r = i + 1;
    while (r < body.length && body[r]!.ws) r++;
    if (l >= 0) pasted.add(l);
    if (r < body.length) pasted.add(r);
  }

  const out: Tok[] = [];
  for (let i = 0; i < body.length; i++) {
    const t = body[i]!;
    const p = idx(t);
    if (p < 0) {
      out.push(t);
      continue;
    }
    const arg = (pasted.has(i) ? raw[p] : expanded[p]) ?? [];
    // An empty argument that is a `##` operand must leave nothing behind.
    out.push(...arg);
  }

  // Now apply `##` left to right over the substituted list.
  const res: Tok[] = [];
  for (let i = 0; i < out.length; i++) {
    if (out[i]!.text !== "##") {
      res.push(out[i]!);
      continue;
    }
    while (res.length && res[res.length - 1]!.ws) res.pop();
    let j = i + 1;
    while (j < out.length && out[j]!.ws) j++;
    const left = res.pop();
    const right = out[j];
    const text = (left?.text ?? "") + (right?.text ?? "");
    if (text !== "") res.push(tokenize(text)[0] ?? tok(text));
    i = j;
  }
  return res;
}

/** Macro-expand a token list. `disabled` carries the blue paint: a macro is
 * not re-expanded while its own replacement is being rescanned. */
function expand(toks: Tok[], macros: Map<string, Macro>, disabled: ReadonlySet<string>): Tok[] {
  const out: Tok[] = [];
  let i = 0;
  while (i < toks.length) {
    const t = toks[i]!;
    const macro = t.id ? macros.get(t.text) : undefined;
    if (!macro || disabled.has(t.text)) {
      out.push(t);
      i++;
      continue;
    }
    if (macro.params === null) {
      const sub = substitute(macro, [], []);
      out.push(...expand(sub, macros, new Set([...disabled, t.text])));
      i++;
      continue;
    }
    // Function-like: only an invocation if the next non-whitespace token is
    // `(`. Otherwise the name is just an identifier.
    let j = i + 1;
    while (j < toks.length && toks[j]!.ws) j++;
    if (j >= toks.length || toks[j]!.text !== "(") {
      out.push(t);
      i++;
      continue;
    }
    // Collect balanced arguments.
    const raw: Tok[][] = [];
    let cur: Tok[] = [];
    let depth = 0;
    let k = j;
    for (; k < toks.length; k++) {
      const c = toks[k]!;
      if (c.text === "(") {
        depth++;
        if (depth === 1) continue;
      } else if (c.text === ")") {
        depth--;
        if (depth === 0) {
          raw.push(cur);
          break;
        }
      } else if (c.text === "," && depth === 1) {
        // A variadic macro's trailing parameter swallows the remaining commas.
        if (!(macro.variadic && raw.length >= macro.params.length - 1)) {
          raw.push(cur);
          cur = [];
          continue;
        }
      }
      cur.push(c);
    }
    if (depth !== 0) {
      // Unbalanced - not an invocation after all; emit verbatim.
      out.push(t);
      i++;
      continue;
    }
    // `M()` with one declared parameter passes a single empty argument;
    // with zero declared parameters it passes none.
    if (macro.params.length === 0 && raw.length === 1 && raw[0]!.every((x) => x.ws)) raw.length = 0;
    while (raw.length < macro.params.length) raw.push([]);
    const trimmed = raw.map((a) => {
      let s = 0;
      let e = a.length;
      while (s < e && a[s]!.ws) s++;
      while (e > s && a[e - 1]!.ws) e--;
      return a.slice(s, e);
    });
    const pre = trimmed.map((a) => expand(a, macros, disabled));
    const sub = substitute(macro, trimmed, pre);
    out.push(...expand(sub, macros, new Set([...disabled, t.text])));
    i = k + 1;
  }
  return out;
}

/** Evaluate an `#if` controlling expression.
 *
 * These files only ever combine `defined(X)` with `!`, `&&`, `||` and
 * parentheses (thread.js's `#if !defined(A) && !defined(B) && !defined(C)` is
 * the one that is not a plain disjunction). Every other identifier is 0, as in
 * real CPP. The reduced expression is checked to contain nothing but those
 * operators and 0/1 before it is evaluated. */
function evalIf(expr: string, macros: ReadonlyMap<string, Macro>): boolean {
  const reduced = expr
    .replace(/defined\s*\(\s*(\w+)\s*\)|defined\s+(\w+)/g, (_m, a: string | undefined, b) =>
      macros.has((a ?? b) as string) ? "1" : "0",
    )
    .replace(/[A-Za-z_]\w*/g, "0");
  if (!/^[01!&|()\s]*$/.test(reduced)) return false;
  return Boolean(Function(`"use strict";return (${reduced || "0"})`)());
}

/** Evaluate the CPP subset these files use: `#define` (object-like,
 * function-like, `##`, GNU named variadics, `\` continuations), `#undef`,
 * `#ifdef`, `#ifndef`, `#if defined(A) || defined(B)`, `#else`, `#endif`,
 * plus full macro expansion of the surviving text.
 *
 * `defines` seeds the macro table with valueless object-like macros - the
 * debug and profiling gates - and is not mutated. The
 * `genCommonCppDefs` prelude is prepended here, exactly as GHC's linker does
 * before handing the file to cpp; whether the profiled variant is used is
 * read back off `PROFILING`, so callers only pass one thing.
 *
 * Deliberately unsupported, because these files use none of it: `#elif`,
 * `#include`, `#` stringification, arithmetic in `#if`, and `defined` combined
 * with anything other than `||`. */
export function preprocess(source: string, defines: ReadonlySet<string>): string {
  // GHC only runs cpp over files whose header pragma asks for it
  // (`getOptionsFromJsFile` -> `enableCPP`). The other eight rts/js sources go
  // into lib.js verbatim, keeping their blank lines and column alignment.
  if (!/^\s*\/\/#OPTIONS:.*\bCPP\b/m.test(source.slice(0, 200))) return source;

  const macros = new Map<string, Macro>();
  for (const d of defines) macros.set(d, { params: null, variadic: null, body: [] });
  const text = genCommonCppDefs(defines.has("PROFILING")) + source;

  const out: string[] = [];
  /** Emitted-but-not-yet-expanded lines. Flushed whenever the macro table
   * changes, so a `#define` part way down a file (gc.js does this) does not
   * retroactively apply to the text above it. */
  let pending: string[] = [];
  const flush = () => {
    if (pending.length === 0) return;
    // A directive line yields no output at all, so chunks rejoin with a single
    // newline; blank lines at a chunk's edges must go the same way `-P` sends
    // blank lines everywhere else.
    const text = render(expand(tokenize(pending.join("\n")), macros, new Set()))
      .replace(/^(?:[ \t]*\n)+/, "")
      .replace(/(?:\n[ \t]*)+$/, "");
    pending = [];
    if (text !== "") out.push(text);
  };

  /** For each open conditional: whether its branch is being emitted, and
   * whether any branch of it has been taken (so `#else` knows). */
  const stack: Array<{ emitting: boolean; taken: boolean }> = [];
  const live = () => stack.every((f) => f.emitting);

  // Join backslash continuations first: they are how the multi-line
  // function-like macros (globals.js's GVAR) are written.
  const rawLines = text.split("\n");
  const lines: string[] = [];
  for (const line of rawLines) {
    if (lines.length && /\\$/.test(lines[lines.length - 1]!)) {
      lines[lines.length - 1] = lines[lines.length - 1]!.slice(0, -1) + line;
    } else {
      lines.push(line);
    }
  }

  for (const line of lines) {
    // CPP allows leading whitespace before the `#`, and these sources use it
    // (environment.js and stableptr.js indent theirs to match the surrounding
    // code). Anchoring at column 0 leaves those directives in the output as
    // JavaScript, where `#ifdef` parses as a private field reference.
    const directive = line.match(/^\s*#\s*(\w+)\s*(.*)$/);
    if (!directive) {
      if (live()) pending.push(line);
      continue;
    }
    const [, kind, rest] = directive;
    switch (kind) {
      case "define": {
        if (!live()) break;
        const parsed = parseDefine(rest!);
        if (parsed) {
          flush();
          macros.set(parsed[0], parsed[1]);
        }
        break;
      }
      case "undef":
        if (live()) {
          flush();
          macros.delete(rest!.trim());
        }
        break;
      case "ifdef":
      case "ifndef": {
        const has = macros.has(rest!.trim());
        const on = kind === "ifdef" ? has : !has;
        stack.push({ emitting: on, taken: on });
        break;
      }
      case "if": {
        const on = evalIf(rest!, macros);
        stack.push({ emitting: on, taken: on });
        break;
      }
      case "else": {
        const frame = stack[stack.length - 1];
        if (frame) {
          frame.emitting = !frame.taken;
          frame.taken = true;
        }
        break;
      }
      case "endif":
        stack.pop();
        break;
      default:
        // `//#OPTIONS:` lines and anything else pass through as comments.
        if (live()) pending.push(line);
    }
  }
  flush();
  return out.join("\n");
}

/** CPP symbols a given configuration defines.
 *
 * GHC drives these from its own flags; ghcts models the two that change
 * observable output. The tracing gates stay off - they exist to debug the
 * RTS itself, and turning them on changes what the program prints. */
export function definesFor(cfg: Pick<StgToJSConfig, "prof" | "debugAlloc">): Set<string> {
  const defines = new Set<string>();
  if (cfg.prof) {
    defines.add("GHCJS_PROF");
    defines.add("PROFILING");
  }
  if (cfg.debugAlloc) defines.add("GHCJS_DEBUG_ALLOC");
  return defines;
}

/** The hand-written RTS, preprocessed and concatenated in cabal order. */
export function renderStaticRts(
  cfg: Pick<StgToJSConfig, "prof" | "debugAlloc"> = { prof: false, debugAlloc: false },
): string {
  const defines = definesFor(cfg);
  return rtsJsFiles
    .map((name) => preprocess(readFileSync(join(rtsJsDir, name), "utf8"), defines))
    .join("\n");
}
