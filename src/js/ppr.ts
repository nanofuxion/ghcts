/** Port of GHC.JS.Ppr: renders the final JS AST to concrete JavaScript syntax.
 *
 * GHC's renderer is polymorphic over an output "doc" type via the JsRender
 * class: `SDoc` (human-readable, indented) and `HLine` (minified). The JS
 * backend's linker (GHC.StgToJS.Linker.Opt.pretty) writes rts.js/out.js in
 * HLine mode with `optRenderJs`, so HLine + optRenderJs is what real GHC
 * output looks like, and it is what this module reproduces byte for byte.
 *
 * The HLine instance is what makes this a plain string concatenation:
 *
 *   (<+?>) = (<>)            -- "optional space" is no space
 *   ($$$)  = (<>)            -- "optional newline" is no newline
 *   jcat   = hcat            -- concatenate
 *   jnest  = id              -- no indentation
 *   addSemi x = x <> ";\n"
 *
 * while IsLine's own `<+>` is an *unconditional* space (`f <> char ' ' <> g`)
 * and `hsep`/`fsep` are `foldr (<+>) empty`, which leaves a trailing space
 * before the empty tail - hence `{d1: b, m: 0 }`. */
import type { JStat, JExpr, JVal, UOp, AOp } from "./syntax.js";

const aOpText = (op: AOp): string => (op === "AssignOp" ? "=" : op === "AddAssignOp" ? "+=" : "-=");

const opText: Record<string, string> = {
  EqOp: "==", StrictEqOp: "===", NeqOp: "!=", StrictNeqOp: "!==",
  GtOp: ">", GeOp: ">=", LtOp: "<", LeOp: "<=",
  AddOp: "+", SubOp: "-", MulOp: "*", DivOp: "/", ModOp: "%",
  LeftShiftOp: "<<", RightShiftOp: ">>", ZRightShiftOp: ">>>",
  BAndOp: "&", BOrOp: "|", BXorOp: "^", LAndOp: "&&", LOrOp: "||",
  InstanceofOp: "instanceof", InOp: "in",
};

const uOpText: Record<UOp, string> = {
  NotOp: "!", BNotOp: "~", NegOp: "-", PlusOp: "+", NewOp: "new", TypeofOp: "typeof",
  DeleteOp: "delete", YieldOp: "yield", VoidOp: "void",
  PreIncOp: "++", PostIncOp: "++", PreDecOp: "--", PostDecOp: "--",
};

const isPre = (op: UOp): boolean => op !== "PostIncOp" && op !== "PostDecOp";

/** `foldl' (<+?>) empty . punctuate comma`: in HLine `<+?>` is `<>`. */
const commas = (xs: string[]): string => xs.join(",");

/** `fsep . punctuate comma` in HLine: `foldr (<+>) empty`, so every element -
 * including the last - is followed by a space. */
const fsepCommas = (xs: string[]): string => (xs.length === 0 ? "" : `${xs.join(", ")} `);

/** encodeJsonChar, ported code point by code point (not UTF-16 code unit) so
 * astral characters get the same surrogate-pair escaping GHC produces. */
function pprStringLit(s: string): string {
  let out = "";
  for (const ch of s) {
    const code = ch.codePointAt(0)!;
    switch (ch) {
      case "/": out += "\\/"; continue;
      case "\b": out += "\\b"; continue;
      case "\f": out += "\\f"; continue;
      case "\n": out += "\\n"; continue;
      case "\r": out += "\\r"; continue;
      case "\t": out += "\\t"; continue;
      case '"': out += '\\"'; continue;
      case "\\": out += "\\\\"; continue;
    }
    const isControl = code < 0x20 || code === 0x7f;
    if (!isControl && code <= 127) { out += ch; continue; }
    if (code <= 0xff) { out += `\\x${code.toString(16).padStart(2, "0")}`; continue; }
    if (code <= 0xffff) { out += `\\u${code.toString(16).padStart(4, "0")}`; continue; }
    const cp0 = code - 0x10000;
    out += `\\u${((cp0 >> 10) + 0xd800).toString(16).padStart(4, "0")}`;
    out += `\\u${((cp0 & 0x3ff) + 0xdc00).toString(16).padStart(4, "0")}`;
  }
  return `"${out}"`;
}

/** GHC's `double`: always shows a decimal point, unlike JS's default toString. */
function pprDouble(d: number): string {
  const isNegZero = Object.is(d, -0);
  const text = isNegZero ? "-0.0" : Number.isInteger(d) && Number.isFinite(d) ? `${d}.0` : String(d);
  return d < 0 || isNegZero ? `(${text})` : text;
}

function pprInt(n: bigint): string {
  const text = n.toString();
  return n < 0n ? `(${text})` : text;
}

const isEmptyBlock = (s: JStat): boolean => s.tag === "BlockStat" && s.stats.length === 0;

/** `addSemi` in HLine mode: semicolon plus a line break. */
const addSemi = (x: string): string => `${x};\n`;

/** Remove one Block layering when braces are already supplied by the caller. */
function optBlock(x: JStat): string {
  return x.tag === "BlockStat" ? renderStatList(x.stats) : addSemi(renderStat(x));
}

/** Only parenthesize a unary-expression operand, matching optParens. */
function optParens(x: JExpr): string {
  return x.tag === "UOpExpr" ? `(${renderExpr(x)})` : renderExpr(x);
}

/** `hangBrace hdr body = jcat [hdr <> ' ' <> '{', jnest body, '}']`. */
function hangBrace(hdr: string, body: string): string {
  return `${hdr} {${body}}`;
}

/** The `JsToDoc [JStat]` instance: `jcat . map (addSemi . jsToDocR r)`.
 * Raw (TS-only) nodes are the one exception: they already carry their own
 * termination since they are opaque pre-rendered text. */
function renderStatList(stats: JStat[]): string {
  return stats.map((s) => (s.tag === "RawStat" ? s.source : addSemi(renderStat(s)))).join("");
}

/** `interSemi = foldl ($$$) empty . punctuateFinal semi semi`: every element,
 * the last one included, gets a semicolon; `$$$` adds nothing in HLine. */
function interSemi(stats: JStat[]): string {
  return stats.map((s) => `${renderStat(s)};`).join("");
}

/** Port of GHC.JS.Ppr.defRenderJsS. Returns the statement's own rendering,
 * with no forced trailing semicolon (callers - renderStatList / interSemi -
 * add that), matching the Haskell module's separation of concerns. */
export function renderStat(s: JStat): string {
  switch (s.tag) {
    case "IfStat": {
      const head = hangBrace(`if(${renderExpr(s.cond)})`, optBlock(s.then));
      return isEmptyBlock(s.else) ? head : `${head}${hangBrace("else", optBlock(s.else))}`;
    }
    case "DeclStat":
      if (s.value === undefined) return `var ${s.ident}`;
      if (s.value.tag === "ValExpr" && s.value.value.tag === "JFunc")
        return `var ${s.ident}=${renderValue(s.value.value)}`;
      return `var ${s.ident}=${renderExpr(s.value)}`;
    case "WhileStat":
      return s.isDo
        ? `${hangBrace("do", optBlock(s.body))}while(${renderExpr(s.cond)})`
        : hangBrace(`while(${renderExpr(s.cond)})`, optBlock(s.body));
    case "BreakStat":
      return addSemi(`break${s.label ? ` ${s.label}` : ""}`);
    case "ContinueStat":
      return addSemi(`continue${s.label ? ` ${s.label}` : ""}`);
    case "LabelStat":
      return `${s.label}:${s.body.tag === "BlockStat" ? interSemi(s.body.stats) : renderStat(s.body)}`;
    case "ForStat":
      return hangBrace(
        `for(${renderStat(s.init)};${renderExpr(s.cond)};(${renderStat(s.step)}))`,
        optBlock(s.body),
      );
    case "ForInStat":
      return hangBrace(`${s.isEach ? "for each" : "for"}(${s.ident} in ${renderExpr(s.obj)})`, optBlock(s.body));
    case "SwitchStat": {
      const cases = s.cases.map(([c, cs]) => `case(${renderExpr(c)}):${optBlock(cs)}`);
      return hangBrace(`switch(${renderExpr(s.scrut)})`, `${cases.join("")}default:${optBlock(s.default)}`);
    }
    case "ReturnStat":
      return `return ${renderExpr(s.value)}`;
    case "ApplStat":
      return `${renderExpr(s.fn)}(${commas(s.args.map(renderExpr))})`;
    case "FuncStat":
      return hangBrace(`function ${s.ident}(${commas(s.args)})`, optBlock(s.body));
    case "TryStat": {
      const body = s.body.tag === "BlockStat" ? renderStatList(s.body.stats) : renderStat(s.body);
      const mbCatch = isEmptyBlock(s.catch) ? "" : hangBrace(`catch(${s.ident})`, optBlock(s.catch));
      const mbFinally = isEmptyBlock(s.finally) ? "" : hangBrace("finally", optBlock(s.finally));
      return `${hangBrace("try", body)}${mbCatch}${mbFinally}`;
    }
    case "AssignStat":
      if (s.rhs.tag === "ValExpr" && s.rhs.value.tag === "JFunc")
        return `${renderExpr(s.lhs)}${aOpText(s.op)}${renderValue(s.rhs.value)}`;
      return `${renderExpr(s.lhs)}${aOpText(s.op)}${renderExpr(s.rhs)}`;
    case "UOpStat":
      return isPre(s.op) ? `${uOpText[s.op]} ${optParens(s.value)}` : `${optParens(s.value)} ${uOpText[s.op]}`;
    case "BlockStat":
      return renderStatList(s.stats);
    case "ThrowStat":
      return `throw ${renderExpr(s.value)}`;
    case "RawStat":
      return s.source;
  }
}

/** Port of GHC.JS.Ppr.defRenderJsE. */
export function renderExpr(e: JExpr): string {
  switch (e.tag) {
    case "ValExpr": return renderValue(e.value);
    case "SelExpr": return `${renderExpr(e.obj)}.${e.field}`;
    case "IdxExpr": return `${renderExpr(e.obj)}[${renderExpr(e.index)}]`;
    case "IfExpr": return `(${renderExpr(e.cond)}?${renderExpr(e.then)}:${renderExpr(e.else)})`;
    case "InfixExpr": return `(${renderExpr(e.left)}${opText[e.op]}${renderExpr(e.right)})`;
    case "UOpExpr": return isPre(e.op) ? `${uOpText[e.op]} ${optParens(e.value)}` : `${optParens(e.value)} ${uOpText[e.op]}`;
    case "ApplExpr": return `${renderExpr(e.fn)}(${commas(e.args.map(renderExpr))})`;
    case "RawExpr": return e.source;
  }
}

/** GHC.StgToJS.Linker.Opt.isUnquotedKey: object keys are left bare when they
 * are all digits, or a plain identifier (`_`/`$`/alpha first, then
 * alphanumeric - note `_` and `$` are *not* accepted after the first char). */
function isUnquotedKey(key: string): boolean {
  if (key.length === 0) return false;
  return /^[0-9]+$/.test(key) || /^[_$\p{Alphabetic}][\p{Alphabetic}0-9]*$/u.test(key);
}

/** Port of GHC.JS.Ppr.defRenderJsV, with GHC.StgToJS.Linker.Opt's JHash. */
export function renderValue(v: JVal): string {
  switch (v.tag) {
    case "JVar": return v.ident;
    case "JList": return `[${commas(v.values.map(renderExpr))}]`;
    case "JDouble": return pprDouble(v.value);
    case "JInt": return pprInt(v.value);
    case "JStr": return pprStringLit(v.value);
    case "JRegEx": return `/${v.value}/`;
    case "JBool": return v.value ? "true" : "false";
    case "JHash": {
      if (v.entries.length === 0) return "{}";
      const sorted = [...v.entries].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
      const parts = sorted.map(([k, e]) => `${isUnquotedKey(k) ? k : `'${k}'`}: ${renderExpr(e)}`);
      return `{${fsepCommas(parts)}}`;
    }
    case "JFunc": return `(${hangBrace(`function(${commas(v.args)})`, renderStat(v.body))})`;
  }
}
