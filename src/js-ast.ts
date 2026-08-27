/** A small, lossless counterpart of GHC.JS.Syntax.
 *
 * GHCTS keeps Haskell lowering independent from JavaScript spelling by using
 * the same two-stage shape as GHCJS: JStat/JExpr/JVal, followed by printing.
 * This module intentionally contains no Miso or Lynx knowledge.
 */
export type Ident = string;

export type JStat =
  | { tag: "raw"; source: string }
  | { tag: "decl"; name: Ident; value?: JExpr }
  | { tag: "return"; value: JExpr }
  | { tag: "if"; condition: JExpr; thenBranch: JStat; elseBranch: JStat }
  | { tag: "while"; doWhile: boolean; condition: JExpr; body: JStat }
  | { tag: "for"; init: JStat; condition: JExpr; step: JStat; body: JStat }
  | { tag: "for-in"; declaration: boolean; name: Ident; object: JExpr; body: JStat }
  | { tag: "switch"; value: JExpr; cases: Array<[JExpr, JStat]>; defaultCase: JStat }
  | { tag: "try"; body: JStat; exception: Ident; handler: JStat; finalizer: JStat }
  | { tag: "label"; name: Ident; body: JStat }
  | { tag: "break"; label?: Ident }
  | { tag: "continue"; label?: Ident }
  | { tag: "block"; body: JStat[] }
  | { tag: "apply"; function: JExpr; arguments: JExpr[] }
  | { tag: "unary"; operator: UOp; value: JExpr }
  | { tag: "assign"; left: JExpr; operator: AOp; right: JExpr }
  | { tag: "function"; name: Ident; parameters: Ident[]; body: JStat };

export type JExpr =
  | { tag: "raw"; source: string }
  | { tag: "value"; value: JVal }
  | { tag: "select"; object: JExpr; property: Ident }
  | { tag: "index"; object: JExpr; index: JExpr }
  | { tag: "infix"; operator: Op; left: JExpr; right: JExpr }
  | { tag: "unary"; operator: UOp; value: JExpr }
  | { tag: "if-expr"; condition: JExpr; thenBranch: JExpr; elseBranch: JExpr }
  | { tag: "call"; function: JExpr; arguments: JExpr[] };

export type JVal =
  | { tag: "var"; name: Ident }
  | { tag: "list"; values: JExpr[] }
  | { tag: "number"; value: number | bigint }
  | { tag: "string"; value: string }
  | { tag: "regex"; value: string }
  | { tag: "boolean"; value: boolean }
  | { tag: "object"; fields: Array<[string, JExpr]> }
  | { tag: "function"; parameters: Ident[]; body: JStat };

export type Op = "==" | "===" | "!=" | "!==" | ">" | ">=" | "<" | "<=" |
  "+" | "-" | "*" | "/" | "%" | "<<" | ">>" | ">>>" | "&" | "|" |
  "^" | "&&" | "||" | "instanceof" | "in";
export type UOp = "!" | "~" | "-" | "+" | "new" | "typeof" | "delete" |
  "yield" | "void" | "++" | "--";
export type AOp = "=" | "+=" | "-=";

/** Staged GHCJS syntax.  Staging is intentionally nominal: the constructors
 * are kept separate so lowering cannot accidentally mix builder nodes with
 * final JS nodes, even though both have the same concrete representation. */
export type JStgStat = JStat;
export type JStgExpr = JExpr;
export type JStgVal = JVal;

export const jStgExprToJS = (expr: JStgExpr): JExpr => expr;
export const jStgStatToJS = (stat: JStgStat): JStat => stat;

/** Counterpart of GHC.JS.JStg.Monad's tagged fresh-name supply. */
export class JSM {
  private next = 0;
  constructor(private tag = "js") {}
  withTag<T>(tag: string, action: (scope: JSM) => T): T {
    const previous = this.tag;
    this.tag = tag;
    try { return action(this); } finally { this.tag = previous; }
  }
  newIdent(): Ident { return `${this.tag}_${this.next++}`; }
}

const quote = (value: string): string => JSON.stringify(value);
export const jvar = (name: Ident): JExpr => ({ tag: "value", value: { tag: "var", name } });
export const jraw = (source: string): JExpr => ({ tag: "raw", source });
/** GHC.JS.Make.global: a reference to a linker/runtime global. */
export const global = (name: Ident): JExpr => jvar(name);
export const jstring = (value: string): JExpr => ({ tag: "value", value: { tag: "string", value } });
export const jnumber = (value: number | bigint): JExpr => ({ tag: "value", value: { tag: "number", value } });
export const jblock = (...body: JStat[]): JStat => ({ tag: "block", body });
export const jrawStat = (source: string): JStat => ({ tag: "raw", source });
export const jglobal = (name: Ident): JExpr => global(name);
/** Core GHC.JS.Make expression constructors. */
export const jselect = (object: JExpr, property: Ident): JExpr => ({ tag: "select", object, property });
export const jindex = (object: JExpr, index: JExpr): JExpr => ({ tag: "index", object, index });
export const jcall = (fn: JExpr, ...arguments_: JExpr[]): JExpr => ({ tag: "call", function: fn, arguments: arguments_ });
export const jinfix = (operator: Op, left: JExpr, right: JExpr): JExpr => ({ tag: "infix", operator, left, right });
export const junary = (operator: UOp, value: JExpr): JExpr => ({ tag: "unary", operator, value });
export const jif = (condition: JExpr, thenBranch: JExpr, elseBranch: JExpr): JExpr => ({ tag: "if-expr", condition, thenBranch, elseBranch });

const literal = (expr: JExpr): boolean | number | string | undefined => {
  if (expr.tag !== "value") return undefined;
  if (expr.value.tag === "boolean" || expr.value.tag === "number" || expr.value.tag === "string") return expr.value.value as boolean | number | string;
  return undefined;
};

/** Small native-AST optimizer corresponding to GHC.JS.Optimizer's safe folds. */
export function optimizeExpr(expr: JExpr): JExpr {
  switch (expr.tag) {
    case "infix": {
      const left = optimizeExpr(expr.left), right = optimizeExpr(expr.right);
      const a = literal(left), b = literal(right);
      if (a !== undefined && b !== undefined) {
        let result: boolean | number | string | undefined;
        switch (expr.operator) {
          case "+": result = typeof a === "string" || typeof b === "string" ? String(a) + String(b) : Number(a) + Number(b); break;
          case "-": result = Number(a) - Number(b); break;
          case "*": result = Number(a) * Number(b); break;
          case "/": if (Number(b) !== 0) result = Number(a) / Number(b); break;
          case "==": case "===": result = a === b; break;
          case "!=": case "!==": result = a !== b; break;
          case "&&": result = Boolean(a) && Boolean(b); break;
          case "||": result = Boolean(a) || Boolean(b); break;
        }
        if (result !== undefined) return typeof result === "boolean" ? { tag: "value", value: { tag: "boolean", value: result } } : typeof result === "number" ? jnumber(result) : jstring(result);
      }
      return { ...expr, left, right };
    }
    case "if-expr": {
      const condition = optimizeExpr(expr.condition);
      const value = literal(condition);
      if (typeof value === "boolean") return optimizeExpr(value ? expr.thenBranch : expr.elseBranch);
      return { ...expr, condition, thenBranch: optimizeExpr(expr.thenBranch), elseBranch: optimizeExpr(expr.elseBranch) };
    }
    case "select": return { ...expr, object: optimizeExpr(expr.object) };
    case "index": return { ...expr, object: optimizeExpr(expr.object), index: optimizeExpr(expr.index) };
    case "unary": return { ...expr, value: optimizeExpr(expr.value) };
    case "call": return { ...expr, function: optimizeExpr(expr.function), arguments: expr.arguments.map(optimizeExpr) };
    case "value": return expr.value.tag === "function" ? { ...expr, value: { ...expr.value, body: optimizeStat(expr.value.body) } } : expr;
    case "raw": return expr;
  }
}

export function optimizeStat(stat: JStat): JStat {
  switch (stat.tag) {
    case "if": {
      const condition = optimizeExpr(stat.condition), value = literal(condition);
      if (typeof value === "boolean") return optimizeStat(value ? stat.thenBranch : stat.elseBranch);
      return { ...stat, condition, thenBranch: optimizeStat(stat.thenBranch), elseBranch: optimizeStat(stat.elseBranch) };
    }
    case "block": return { ...stat, body: stat.body.map(optimizeStat) };
    case "decl": return { ...stat, value: stat.value && optimizeExpr(stat.value) };
    case "return": return { ...stat, value: optimizeExpr(stat.value) };
    case "apply": return { ...stat, function: optimizeExpr(stat.function), arguments: stat.arguments.map(optimizeExpr) };
    case "assign": return { ...stat, left: optimizeExpr(stat.left), right: optimizeExpr(stat.right) };
    case "unary": return { ...stat, value: optimizeExpr(stat.value) };
    default: return stat;
  }
}
export const jfunction = (parameters: Ident[], body: JStat): JExpr => ({
  tag: "value", value: { tag: "function", parameters, body },
});

export function printExpr(expr: JExpr): string {
  switch (expr.tag) {
    case "raw": return expr.source;
    case "value": return printValue(expr.value);
    case "select": return `${printExpr(expr.object)}.${expr.property}`;
    case "index": return `${printExpr(expr.object)}[${printExpr(expr.index)}]`;
    case "infix": return `(${printExpr(expr.left)} ${expr.operator} ${printExpr(expr.right)})`;
    case "unary": return expr.operator === "new" ? `new ${printExpr(expr.value)}` : `${expr.operator}${printExpr(expr.value)}`;
    case "if-expr": return `(${printExpr(expr.condition)} ? ${printExpr(expr.thenBranch)} : ${printExpr(expr.elseBranch)})`;
    case "call": return `${printExpr(expr.function)}(${expr.arguments.map(printExpr).join(", ")})`;
  }
}

function printValue(value: JVal): string {
  switch (value.tag) {
    case "var": return value.name;
    case "list": return `[${value.values.map(printExpr).join(", ")}]`;
    case "number": {
      const rendered = typeof value.value === "bigint" ? `${value.value}n` : String(value.value);
      return rendered.startsWith("-") ? `(${rendered})` : rendered;
    }
    case "string": return quote(value.value);
    case "regex": return `/${value.value}/`;
    case "boolean": return value.value ? "true" : "false";
    case "object": return `{${[...value.fields].sort(([a], [b]) => a.localeCompare(b)).map(([name, field]) => `${quote(name)}: ${printExpr(field)}`).join(", ")}}`;
    case "function": return `(function(${value.parameters.join(", ")}) ${printStat(value.body)})`;
  }
}

export function printStat(stat: JStat): string {
  switch (stat.tag) {
    case "raw": return stat.source;
    case "decl": return `var ${stat.name}${stat.value ? ` = ${printExpr(stat.value)}` : ""};`;
    case "return": return `return ${printExpr(stat.value)};`;
    case "if": return `if (${printExpr(stat.condition)}) ${printStat(stat.thenBranch)}${stat.elseBranch.tag === "block" && stat.elseBranch.body.length === 0 ? "" : ` else ${printStat(stat.elseBranch)}`}`;
    case "while": return `${stat.doWhile ? "do " : "while ("}${stat.doWhile ? printStat(stat.body) + ` while (${printExpr(stat.condition)});` : `${printExpr(stat.condition)}) ${printStat(stat.body)}`}`;
    case "for": return `for (${printStat(stat.init)} ${printExpr(stat.condition)}; ${printStat(stat.step)}) ${printStat(stat.body)}`;
    case "for-in": return `for (${stat.declaration ? "var " : ""}${stat.name} in ${printExpr(stat.object)}) ${printStat(stat.body)}`;
    case "switch": return `switch (${printExpr(stat.value)}) {${stat.cases.map(([value, body]) => `case ${printExpr(value)}: ${printStat(body)}`).join(" ")}default: ${printStat(stat.defaultCase)}}`;
    case "try": return `try ${printStat(stat.body)}${stat.handler.tag === "block" && stat.handler.body.length === 0 ? "" : ` catch (${stat.exception}) ${printStat(stat.handler)}`}${stat.finalizer.tag === "block" && stat.finalizer.body.length === 0 ? "" : ` finally ${printStat(stat.finalizer)}`}`;
    case "label": return `${stat.name}: ${printStat(stat.body)}`;
    case "break": return `break${stat.label ? ` ${stat.label}` : ""};`;
    case "continue": return `continue${stat.label ? ` ${stat.label}` : ""};`;
    case "block": return `{ ${stat.body.map(printStat).join("\n")} }`;
    case "apply": return `${printExpr(stat.function)}(${stat.arguments.map(printExpr).join(", ")});`;
    case "unary": return `${stat.operator}${printExpr(stat.value)};`;
    case "assign": return `${printExpr(stat.left)} ${stat.operator} ${printExpr(stat.right)};`;
    case "function": return `function ${stat.name}(${stat.parameters.join(", ")}) ${printStat(stat.body)}`;
  }
}
