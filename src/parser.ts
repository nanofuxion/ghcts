import type {
  CaseAlternative,
  DataDeclaration,
  Declaration,
  DoStatement,
  Expr,
  Guard,
  ImportDeclaration,
  ListQualifier,
  LocalBinding,
  Module,
  Span,
  ValueDeclaration,
} from "./ast.js";
import { error } from "./diagnostics.js";
import { applyLayout, lex, type Token } from "./lexer.js";
import type { Diagnostic } from "./types.js";
export interface ParsedModule {
  ast: Module;
  source: string;
  file: string;
}
// Declarations supplied by imported modules carry the real fixities later in
// the pipeline.  The parser still needs a total, deterministic fallback so a
// symbolic application never leaks out and is misread as another declaration.
type Assoc = "left" | "right";
const operators: Record<string, { prec: number; assoc: Assoc }> = {
  // This table runs one level below Haskell's report fixities, so the monadic
  // operators (`infixl 1`) land at 0 and `$` (`infixr 0`) below everything.
  $: { prec: -1, assoc: "right" },
  ">>=": { prec: 0, assoc: "left" },
  ">>": { prec: 0, assoc: "left" },
  "=<<": { prec: 0, assoc: "right" },
  "<$>": { prec: 3, assoc: "left" },
  "<*>": { prec: 3, assoc: "left" },
  "<*": { prec: 3, assoc: "left" },
  "*>": { prec: 3, assoc: "left" },
  "&": { prec: 1, assoc: "left" },
  "||": { prec: 1, assoc: "right" },
  "&&": { prec: 2, assoc: "right" },
  "==": { prec: 3, assoc: "left" },
  "/=": { prec: 3, assoc: "left" },
  "<": { prec: 3, assoc: "left" },
  ">": { prec: 3, assoc: "left" },
  "<=": { prec: 3, assoc: "left" },
  ">=": { prec: 3, assoc: "left" },
  ":": { prec: 4, assoc: "right" },
  "++": { prec: 4, assoc: "right" },
  "+~": { prec: 4, assoc: "right" },
  "-~": { prec: 4, assoc: "right" },
  "*~": { prec: 4, assoc: "right" },
  "//~": { prec: 4, assoc: "right" },
  "<>~": { prec: 4, assoc: "right" },
  "+": { prec: 5, assoc: "left" },
  "-": { prec: 5, assoc: "left" },
  "+=": { prec: 5, assoc: "left" },
  "-=": { prec: 5, assoc: "left" },
  "*=": { prec: 6, assoc: "left" },
  "*": { prec: 6, assoc: "left" },
  "/": { prec: 6, assoc: "left" },
  ".": { prec: 8, assoc: "right" },
  "^.": { prec: 7, assoc: "left" },
  "^?": { prec: 7, assoc: "left" },
  ".~": { prec: 7, assoc: "right" },
  "%~": { prec: 7, assoc: "right" },
  "?~": { prec: 7, assoc: "right" },
  "!": { prec: 9, assoc: "left" },
  "!!": { prec: 9, assoc: "left" },
  "#": { prec: 2, assoc: "left" },
};
export function parseModule(
  source: string,
  file: string,
  defines: ReadonlySet<string> = new Set(),
): { module?: ParsedModule; diagnostics: Diagnostic[] } {
  const result = lex(source, file, defines);
  const parser = new Parser(
    applyLayout(result.tokens),
    file,
    result.diagnostics,
  );
  const ast = parser.module();
  expandTemplateHaskell(ast);
  return {
    module: result.diagnostics.some((d) => d.severity === "error")
      ? undefined
      : { ast, source, file },
    diagnostics: result.diagnostics,
  };
}
function applyNamed(name: string, args: Expr[], span: Span): Expr {
  return args.reduce<Expr>(
    (fn, arg) => ({ tag: "app", fn, arg, span }),
    { tag: "var", name, span },
  );
}
function lensDeclaration(name: string, field: string, span: Span): ValueDeclaration {
  return {
    tag: "value",
    name,
    equations: [
      {
        patterns: [],
        guards: [
          {
            body: applyNamed(
              "lens",
              [
                { tag: "var", name: field, span },
                {
                  tag: "lambda",
                  parameter: "record",
                  body: {
                    tag: "lambda",
                    parameter: "field",
                    body: {
                      tag: "recordUpdate",
                      base: { tag: "var", name: "record", span },
                      fields: [{ name: field, value: { tag: "var", name: "field", span } }],
                      span,
                    },
                    span,
                  },
                  span,
                },
              ],
              span,
            ),
          },
        ],
        whereBindings: [],
      },
    ],
    span,
  };
}
function expandTemplateHaskell(module: Module): void {
  const data = new Map<string, DataDeclaration>();
  for (const declaration of module.declarations)
    if (declaration.tag === "data") data.set(declaration.name, declaration);
  const expanded: Declaration[] = [];
  let usedMakeLenses = false;
  for (const declaration of module.declarations) {
    if (declaration.tag !== "splice" || declaration.name !== "makeLenses") {
      expanded.push(declaration);
      continue;
    }
    usedMakeLenses = true;
    const record = data.get(declaration.argument);
    if (!record) {
      expanded.push({
        tag: "unsupported",
        feature: `makeLenses ''${declaration.argument}`,
        span: declaration.span,
      });
      continue;
    }
    for (const constructor of record.constructors) {
      if (!constructor.fields) continue;
      for (const field of constructor.fields) {
        if (!field.startsWith("_") || field.length < 2) continue;
        expanded.push(lensDeclaration(field.slice(1), field, declaration.span));
      }
    }
  }
  module.declarations = expanded;
  if (usedMakeLenses)
    for (const imported of module.imports)
      if (imported.exposing?.includes("makeLenses") || imported.module.endsWith(".Lens.TH")) {
        imported.module = imported.module.replace(/\.Lens\.TH$/, ".Lens");
        imported.exposing = [
          ...new Set(
            ["lens", ...(imported.exposing ?? [])].filter((name) => name !== "makeLenses"),
          ),
        ];
      }
  module.imports = module.imports.filter(
    (imported) =>
      imported.module !== "Language.Haskell.TH.Quote" &&
      !imported.module.endsWith(".QQ"),
  );
  module.declarations = module.declarations.map(expandDeclarationQuotes);
}
const jsQuoteKeys = Array.from({ length: 26 }, (_, index) =>
  String.fromCharCode(97 + index),
).flatMap((letter) =>
  Array.from({ length: 10 }, (_, digit) => `${letter}${digit}`),
);
function jsQuoteVariables(body: string): string[] {
  return [...body.matchAll(/\$\{([A-Za-z_][A-Za-z0-9_']*)\}/g)].map(
    (match) => match[1]!,
  );
}
function rewriteJsQuoteBody(
  body: string,
  pairs: Array<[string, string]>,
): string {
  let remaining = pairs;
  let output = "";
  for (let index = 0; index < body.length; ) {
    const next = remaining[0];
    if (body[index] === "$" && next) {
      const needle = `{${next[0]}}`;
      if (body.slice(index + 1).startsWith(needle)) {
        output += next[1];
        index += 1 + needle.length;
        remaining = remaining.slice(1);
        continue;
      }
    }
    output += body[index]!;
    index++;
  }
  return output;
}
function expandJsQuote(expr: Extract<Expr, { tag: "jsQuote" }>): Expr {
  const span = expr.span;
  const pairs = jsQuoteVariables(expr.body).map(
    (name, index) => [name, jsQuoteKeys[index] ?? `k${index}`] as [string, string],
  );
  const body = rewriteJsQuoteBody(expr.body, pairs);
  const object: Expr =
    pairs.length === 0
      ? { tag: "var", name: "create", span }
      : applyNamed(
          "createWith",
          [
            {
              tag: "list",
              items: pairs.map(([name, key]) => ({
                tag: "tuple" as const,
                items: [
                  { tag: "string" as const, value: key, span },
                  { tag: "var" as const, name, span },
                ],
                span,
              })),
              span,
            },
          ],
          span,
        );
  return {
    tag: "do",
    statements: [
      {
        tag: "bind",
        pattern: { tag: "var", name: "__qq_object", span },
        source: object,
      },
      {
        tag: "expr",
        expr: applyNamed(
          "inline",
          [
            { tag: "string", value: body, span },
            { tag: "var", name: "__qq_object", span },
          ],
          span,
        ),
      },
    ],
    span,
  };
}
function expandExprQuotes(expr: Expr): Expr {
  if (expr.tag === "jsQuote" && (expr.quoter ?? "js") === "js")
    return expandJsQuote(expr);
  switch (expr.tag) {
    case "tuple":
      return { ...expr, items: expr.items.map(expandExprQuotes) };
    case "list":
      return { ...expr, items: expr.items.map(expandExprQuotes) };
    case "listComp":
      return {
        ...expr,
        body: expandExprQuotes(expr.body),
        qualifiers: expr.qualifiers.map(expandQualifierQuotes),
      };
    case "record":
      return {
        ...expr,
        fields: expr.fields.map((field) => ({
          ...field,
          value: expandExprQuotes(field.value),
        })),
      };
    case "recordUpdate":
      return {
        ...expr,
        base: expandExprQuotes(expr.base),
        fields: expr.fields.map((field) => ({
          ...field,
          value: expandExprQuotes(field.value),
        })),
      };
    case "app":
      return {
        ...expr,
        fn: expandExprQuotes(expr.fn),
        arg: expandExprQuotes(expr.arg),
      };
    case "lambda":
      return { ...expr, body: expandExprQuotes(expr.body) };
    case "lambdaCase":
      return {
        ...expr,
        alternatives: expr.alternatives.map(expandAlternativeQuotes),
      };
    case "let":
      return {
        ...expr,
        bindings: expr.bindings.map(expandLocalQuotes),
        body: expandExprQuotes(expr.body),
      };
    case "do":
      return { ...expr, statements: expr.statements.map(expandDoQuotes) };
    case "if":
      return {
        ...expr,
        condition: expandExprQuotes(expr.condition),
        thenBranch: expandExprQuotes(expr.thenBranch),
        elseBranch: expandExprQuotes(expr.elseBranch),
      };
    case "case":
      return {
        ...expr,
        subject: expandExprQuotes(expr.subject),
        alternatives: expr.alternatives.map(expandAlternativeQuotes),
      };
    default:
      return expr;
  }
}
function expandQualifierQuotes(qualifier: ListQualifier): ListQualifier {
  return qualifier.tag === "guard"
    ? { ...qualifier, condition: expandExprQuotes(qualifier.condition) }
    : { ...qualifier, source: expandExprQuotes(qualifier.source) };
}
function expandAlternativeQuotes(alternative: CaseAlternative): CaseAlternative {
  return {
    ...alternative,
    guard: alternative.guard && expandExprQuotes(alternative.guard),
    patternGuards: alternative.patternGuards?.map((guard) => ({
      pattern: guard.pattern,
      source: expandExprQuotes(guard.source),
    })),
    body: expandExprQuotes(alternative.body),
  };
}
function expandGuardQuotes(guard: Guard): Guard {
  return {
    ...guard,
    condition: guard.condition && expandExprQuotes(guard.condition),
    source: guard.source && expandExprQuotes(guard.source),
    body: expandExprQuotes(guard.body),
  };
}
function expandDoQuotes(statement: DoStatement): DoStatement {
  if (statement.tag === "expr")
    return { ...statement, expr: expandExprQuotes(statement.expr) };
  if (statement.tag === "bind")
    return { ...statement, source: expandExprQuotes(statement.source) };
  return { ...statement, bindings: statement.bindings.map(expandLocalQuotes) };
}
function expandLocalQuotes(binding: LocalBinding): LocalBinding {
  return {
    ...binding,
    value: expandExprQuotes(binding.value),
    guards: binding.guards?.map(expandGuardQuotes),
    whereBindings: binding.whereBindings?.map(expandLocalQuotes),
  };
}
function expandDeclarationQuotes(declaration: Declaration): Declaration {
  if (declaration.tag === "value")
    return {
      ...declaration,
      equations: declaration.equations.map((equation) => ({
        ...equation,
        guards: equation.guards.map(expandGuardQuotes),
        whereBindings: equation.whereBindings.map(expandLocalQuotes),
      })),
    };
  if (declaration.tag === "class" || declaration.tag === "instance")
    return {
      ...declaration,
      members: declaration.members.map(expandDeclarationQuotes),
    };
  return declaration;
}
function tokenSpelling(token: Token): string {
  if (token.kind === "string") return JSON.stringify(token.text);
  if (token.kind === "char") {
    if (token.text === "'") return "'\\''";
    if (token.text === "\\") return "'\\\\'";
    if (token.text === "\n") return "'\\n'";
    if (token.text === "\t") return "'\\t'";
    if (token.text === "\r") return "'\\r'";
    return `'${token.text}'`;
  }
  if (token.kind === "quasiquote")
    return `[${token.quoter ?? "js"}|${token.text}|]`;
  return token.text;
}
class Parser {
  private index = 0;
  /** Exclusive token boundary used while parsing the operand of `(expr op)`. */
  private expressionStop = -1;
  constructor(
    private readonly tokens: Token[],
    private readonly file: string,
    private readonly diagnostics: Diagnostic[],
  ) {}
  private current() {
    return this.tokens[this.index] ?? this.tokens[this.tokens.length - 1];
  }
  private take() {
    return this.tokens[this.index++] ?? this.tokens[this.tokens.length - 1];
  }
  private skipLines() {
    while (
      this.current().kind === "newline" ||
      this.current().text === ";"
    )
      this.take();
  }
  private acceptLayoutOpen() {
    return this.current().text === "{" ? !!this.take() : false;
  }
  private acceptLayoutClose() {
    return this.current().text === "}" ? !!this.take() : false;
  }
  private accept(text: string) {
    if (this.current().text === text) {
      this.take();
      return true;
    }
    return false;
  }
  private acceptTypeSignature() {
    if (this.current().text === "::") {
      this.take();
      return true;
    }
    if (
      this.current().text === ":" &&
      this.tokens[this.index + 1]?.text === ":"
    ) {
      this.take();
      this.take();
      return true;
    }
    return false;
  }
  private expect(text: string) {
    if (!this.accept(text)) {
      const t = this.current();
      this.diagnostics.push(
        error(
          "E_PARSE",
          `Expected ${text}, found ${t.text || "end of input"}`,
          this.file,
          t.span.line,
          t.span.column,
        ),
      );
    }
  }
  module(): Module {
    this.skipLines();
    let name = "Main";
    const imports: ImportDeclaration[] = [];
    const exports: string[] = [];
    const reexports: string[] = [];
    const declarations: Declaration[] = [];
    if (this.current().text === "module") {
      this.take();
      name = this.take().text;
      // Export lists are an interface concern; retain module identity now and
      // leave export filtering to resolution.  They may span many layout
      // lines, unlike the old `module X where` assumption.
      if (this.accept("(")) {
        let depth = 1;
        let sawModule = false;
        while (depth && this.current().kind !== "eof") {
          const token = this.take();
          if (token.text === "(") {
            depth++;
            continue;
          }
          if (token.text === ")") {
            depth--;
            continue;
          }
          if (token.text === "module") {
            sawModule = true;
            continue;
          }
          if (sawModule && token.kind === "ident") {
            reexports.push(token.text);
            sawModule = false;
            continue;
          }
          if (token.text === ",") {
            sawModule = false;
            continue;
          }
          if (
            !sawModule &&
            (token.kind === "ident" || token.kind === "symbol") &&
            !["..", "(", ")", "[", "]", "{", "}"].includes(token.text)
          )
            exports.push(token.text);
        }
      }
      this.expect("where");
      this.acceptLayoutOpen();
      this.skipLines();
    }
    while (this.current().kind !== "eof") {
      this.skipLines();
      if (this.current().kind === "eof") break;
      if (this.acceptLayoutClose()) {
        this.skipLines();
        continue;
      }
      if (this.current().text === "import") {
        imports.push(this.importDeclaration());
        continue;
      }
      const declarationStart = this.index;
      const declaration = this.declaration();
      if (declaration) declarations.push(declaration);
      // A type signature is deliberately not yet represented in the small
      // runtime AST, but it has still been consumed successfully.  Do not
      // discard the following value declaration as if signature parsing had
      // failed.
      else if (this.index === declarationStart) this.lineEnd();
    }
    return {
      name,
      imports,
      exports: [...new Set(exports)],
      reexports: [...new Set(reexports)],
      declarations,
    };
  }
  private importDeclaration(): ImportDeclaration {
    const start = this.take().span;
    const qualified = this.accept("qualified");
    const imported = this.take().text;
    let alias: string | undefined;
    if (this.accept("as")) alias = this.take().text;
    const hiding = this.accept("hiding");
    const names = this.current().text === "(" ? this.importNames() : undefined;
    this.lineEnd();
    return {
      module: imported,
      qualified,
      alias,
      ...(names
        ? hiding
          ? { hiding: names.names, hidingConstructors: names.constructors }
          : { exposing: names.names, exposingConstructors: names.constructors }
        : {}),
      span: start,
    };
  }
  /** Import lists have namespace syntax such as `T(..)` and `(+)`.  The
   * resolver currently operates on exported value/constructor names, so keep
   * each actual binder while discarding punctuation and the `..` marker. */
  private importNames(): { names: string[]; constructors: string[] } {
    this.expect("(");
    const names: string[] = [];
    const constructors: string[] = [];
    let depth = 1;
    while (depth && this.current().kind !== "eof") {
      const token = this.take();
      if (token.text === "(") {
        depth++;
        continue;
      }
      if (token.text === ")") {
        depth--;
        continue;
      }
      // Operators in an import list are parenthesized themselves, e.g.
      // `import Data.Function ((.))`; retain their binder token at nested depth.
      if (
        token.text !== "," &&
        token.text !== ".." &&
        (token.kind === "ident" || token.kind === "symbol") &&
        !["(", ")", "[", "]", "{", "}"].includes(token.text)
      ) {
        names.push(token.text);
        // At the outer import-list level, `T (..)` carries a namespace
        // wildcard.  Record it separately so `T` and `T(..)` do not become
        // indistinguishable during resolution.
        if (
          depth === 1 &&
          this.current().text === "(" &&
          this.tokens[this.index + 1]?.text === ".." &&
          this.tokens[this.index + 2]?.text === ")"
        ) {
          constructors.push(token.text);
          this.take();
          this.take();
          this.take();
        }
      }
    }
    return {
      names: [...new Set(names)],
      constructors: [...new Set(constructors)],
    };
  }
  private declaration(): Declaration | undefined {
    if (
      this.current().text === "makeLenses" &&
      this.tokens[this.index + 1]?.text === "''"
    ) {
      const start = this.take().span;
      this.take();
      const argument = this.take().text;
      this.skipLines();
      return { tag: "splice", name: "makeLenses", argument, span: start };
    }
    if (this.current().text === "data" || this.current().text === "newtype")
      return this.data();
    if (this.current().text === "type") {
      const start = this.take().span;
      const name = this.take().text;
      const parameters: string[] = [];
      while (this.current().kind === "ident" && this.current().text !== "=")
        parameters.push(this.take().text);
      this.expect("=");
      const target: string[] = [];
      while (
        this.current().text !== ";" &&
        this.current().text !== "}" &&
        this.current().kind !== "eof"
      )
        target.push(this.take().text);
      this.skipLines();
      return {
        tag: "typeAlias",
        name,
        parameters,
        target: target.join(" "),
        equations: [],
        span: start,
      };
    }
    if (["infix", "infixl", "infixr"].includes(this.current().text)) {
      this.take();
      while (
        this.current().text !== ";" &&
        this.current().text !== "}" &&
        this.current().kind !== "eof"
      )
        this.take();
      this.skipLines();
      return undefined;
    }
    if (this.current().text === "class") return this.classDeclaration();
    if (this.current().text === "instance") return this.instanceDeclaration();
    if (this.current().text === "foreign") return this.foreign();
    // Haskell permits one type signature for a comma-separated binder group.
    // Retain the first name in the current AST (which has one signature node
    // per declaration) while consuming the entire group without cascading.
    if (this.current().kind === "ident") {
      let probe = this.index;
      const names = [this.tokens[probe].text];
      while (
        this.tokens[probe + 1]?.text === "," &&
        this.tokens[probe + 2]?.kind === "ident"
      ) {
        probe += 2;
        names.push(this.tokens[probe].text);
      }
      if (
        this.tokens[probe + 1]?.text === "::" ||
        (this.tokens[probe + 1]?.text === ":" &&
          this.tokens[probe + 2]?.text === ":")
      ) {
        const start = this.current().span;
        while (this.index <= probe) this.take();
        this.acceptTypeSignature();
        const type: string[] = [];
        while (
          this.current().text !== ";" &&
          this.current().text !== "}" &&
          this.current().kind !== "eof"
        )
          type.push(this.take().text);
        this.skipLines();
        return {
          tag: "signature",
          name: names[0],
          type: type.join(" "),
          span: start,
        };
      }
    }
    // A top-level tuple pattern binding is valid (`(x, y) = action`).  It
    // needs Core pattern-binding support later, but parsing it as a synthetic
    // zero-argument value keeps following declarations recoverable.
    if (this.current().text === "(") {
      const start = this.current().span;
      let probe = this.index;
      let depth = 0;
      do {
        const text = this.tokens[probe++]?.text;
        if (text === "(") depth++;
        else if (text === ")") depth--;
      } while (depth && probe < this.tokens.length);
      const isTuple = this.tokens
        .slice(this.index, probe)
        .some((token) => token.text === ",");
      if (isTuple && this.tokens[probe]?.text === "=") {
        const pattern = this.pattern();
        this.expect("=");
        const value = this.expression();
        this.skipLines();
        return {
          tag: "value",
          name: `__pattern_${start.start}`,
          equations: [
            {
              patterns: [pattern],
              guards: [{ body: value }],
              whereBindings: [],
            },
          ],
          span: start,
        };
      }
    }
    if (
      this.current().kind !== "ident" &&
      this.current().kind !== "symbol" &&
      this.current().text !== "("
    ) {
      const t = this.take();
      this.diagnostics.push(
        error(
          "E_PARSE",
          `Expected declaration, found ${t.text}`,
          this.file,
          t.span.line,
          t.span.column,
        ),
      );
      return undefined;
    }
    const start = this.current().span;
    let name: string;
    let infixLeft: import("./ast.js").Pattern | undefined;
    // Parenthesized operators are ordinary value binders in Haskell.  Keeping
    // their spelling here also makes their signatures and implementations
    // join correctly across CPP-selected lines.
    if (this.accept("(")) {
      name = this.take().text;
      this.expect(")");
    } else name = this.take().text;
    if (this.acceptTypeSignature()) {
      const type: string[] = [];
      while (
        this.current().text !== ";" &&
        this.current().text !== "}" &&
        this.current().kind !== "eof"
      )
        type.push(this.take().text);
      this.skipLines();
      return { tag: "signature", name, type: type.join(" "), span: start };
    }
    if (
      this.current().kind === "symbol" &&
      !["=", "|", ";", "}", "(", "[", "{"].includes(this.current().text)
    ) {
      const operator = this.take();
      infixLeft = { tag: "var", name, span: start };
      name = operator.text;
    }
    const equation = (): {
      patterns: import("./ast.js").Pattern[];
      guards: import("./ast.js").Guard[];
      whereBindings: import("./ast.js").LocalBinding[];
    } => {
      const patterns: import("./ast.js").Pattern[] = infixLeft
        ? [infixLeft]
        : [];
      while (
        !["=", "|"].includes(this.current().text) &&
        this.current().kind !== "eof"
      )
        patterns.push(this.lambdaPattern());
      const guards: import("./ast.js").Guard[] = [];
      const finishLine = () => this.skipLines();
      const guarded = this.accept("|");
      if (guarded) {
        do {
          const guard = this.guard();
          this.expect("=");
          guards.push({ ...guard, body: this.expression() });
          this.skipLines();
        } while (this.accept("|"));
      } else {
        this.expect("=");
        guards.push({ body: this.expression() });
      }
      const whereBindings = this.accept("where") ? this.localBindings() : [];
      finishLine();
      return { patterns, guards, whereBindings };
    };
    const equations = [equation()];
    while (this.current().text === name) {
      this.take();
      equations.push(equation());
    }
    return {
      tag: "value",
      name,
      equations,
      span: start,
    } satisfies ValueDeclaration;
  }
  private data(): DataDeclaration {
    const isNewtype = this.current().text === "newtype";
    const start = this.take().span;
    const name = this.take().text;
    // Declaration heads may contain kind signatures/applications, as in
    // `newtype Path (path :: Symbol) = ...`; find the top-level equals.
    let headerDepth = 0;
    const parameters: string[] = [];
    while (this.current().kind !== "eof") {
      const token = this.current();
      if (token.text === "=" && headerDepth === 0) break;
      // Only lower-case identifiers in the declaration head are ordinary
      // type parameters.  Kind annotations are retained by the lossless
      // token stream for a later kind phase, but do not become parameters.
      if (
        headerDepth === 0 &&
        token.kind === "ident" &&
        /^[a-z]/.test(token.text)
      )
        parameters.push(token.text);
      if (token.kind === "symbol" && (token.text === "(" || token.text === "["))
        headerDepth++;
      if (token.kind === "symbol" && (token.text === ")" || token.text === "]"))
        headerDepth = Math.max(0, headerDepth - 1);
      this.take();
    }
    this.expect("=");
    const constructors: DataDeclaration["constructors"] = [];
    do {
      // Existential and constrained constructors can appear after any `|`,
      // not only at the beginning of a declaration:
      //   `forall a. C a` and `(Eq a, Show a) => C a`.
      // Skip that type-level prefix without allowing its punctuation or class
      // name to become a bogus constructor binder.
      if (this.current().text === "forall") {
        this.take();
        // The lexer keeps qualified identifiers intact and consequently also
        // represents `result.` (the common no-space forall spelling) as one
        // token. Accept either spelling of the quantifier terminator.
        while (this.current().kind !== "eof") {
          const variable = this.take();
          if (variable.text === "." || variable.text.endsWith(".")) break;
        }
      }
      if (this.current().text === "(") {
        let probe = this.index;
        let depth = 0;
        do {
          const token = this.tokens[probe++];
          if (token?.text === "(") depth++;
          else if (token?.text === ")") depth--;
        } while (depth > 0 && probe < this.tokens.length);
        if (this.tokens[probe]?.text === "=>") {
          while (this.index < probe) this.take();
          this.take();
        }
      } else {
        let probe = this.index;
        while (
          probe < this.tokens.length &&
          !["=>", "|", ";", "deriving"].includes(this.tokens[probe]?.text ?? "")
        )
          probe++;
        if (this.tokens[probe]?.text === "=>")
          while (this.index <= probe) this.take();
      }
      const constructor = this.take().text;
      let arity = 0;
      let fields: string[] | undefined;
      let fieldTypes: string[] | undefined;
      if (this.accept("{")) {
        fields = [];
        fieldTypes = [];
        while (this.current().text !== "}" && this.current().kind !== "eof") {
          const field = this.take();
          if (field.kind === "ident") {
            fields.push(field.text);
            arity++;
          }
          this.acceptTypeSignature();
          const type: string[] = [];
          let depth = 0;
          while (this.current().kind !== "eof") {
            const token = this.current();
            if (depth === 0 && (token.text === "}" || token.text === ","))
              break;
            if (token.text === "(" || token.text === "[") depth++;
            if (token.text === ")" || token.text === "]")
              depth = Math.max(0, depth - 1);
            type.push(this.take().text);
          }
          fieldTypes.push(type.join(" "));
          this.accept(",");
        }
        this.expect("}");
      } else {
        // Constructor fields are Haskell `atype`s: each ident, list, or
        // parenthesized type is one field.  `CrossThread Thread action` is
        // two fields; type application must be written `(Maybe a)`.
        // Stop only at a declaration-level constructor separator/deriving/layout.
        while (
          this.current().kind !== "eof" &&
          this.current().text !== "|" &&
          this.current().text !== "deriving" &&
          this.current().text !== ";" &&
          !(this.current().text === "}" && this.current().virtual)
        ) {
          if (this.current().text === "!") {
            this.take();
            continue;
          }
          if (this.current().text === "(" || this.current().text === "[") {
            const spelling: string[] = [];
            let depth = 0;
            do {
              const token = this.take();
              if (token.text === "(" || token.text === "[") depth++;
              if (token.text === ")" || token.text === "]") depth--;
              spelling.push(token.text);
            } while (depth > 0 && this.current().kind !== "eof");
            arity++;
            // A positional field's type matters as much as a record field's:
            // it is what ties `Just`'s argument to `Maybe a`'s parameter.
            (fieldTypes ??= []).push(spelling.join(" "));
            continue;
          }
          if (this.current().kind === "ident") {
            (fieldTypes ??= []).push(this.take().text);
            arity++;
            continue;
          }
          // Preserve progress for uncommon quantified/kind syntax; later
          // typed-Core validation owns any unsupported feature diagnostic.
          this.take();
        }
      }
      constructors.push({ name: constructor, arity, fields, fieldTypes });
    } while (this.accept("|"));
    const deriving: string[] = [];
    let inDeriving = false;
    while (
      this.current().text !== ";" &&
      !(this.current().text === "}" && this.current().virtual) &&
      this.current().kind !== "eof"
    ) {
      const token = this.take();
      if (token.text === "deriving") {
        inDeriving = true;
        continue;
      }
      if (inDeriving && token.kind === "ident" && /^[A-Z]/.test(token.text))
        deriving.push(token.text);
    }
    this.skipLines();
    return {
      tag: "data",
      name,
      parameters: [...new Set(parameters)],
      constructors,
      deriving: [...new Set(deriving)],
      ...(isNewtype ? { newtype: true } : {}),
      span: start,
    };
  }
  private foreign():
    | import("./ast.js").ForeignDeclaration
    | import("./ast.js").UnsupportedDeclaration {
    const start = this.take().span;
    if (!this.accept("import")) {
      while (this.current().text !== ";" && this.current().kind !== "eof")
        this.take();
      this.skipLines();
      return { tag: "unsupported", feature: "foreign export", span: start };
    }
    const callingConvention = this.take();
    if (callingConvention.text !== "javascript") {
      while (
        this.current().text !== ";" &&
        this.current().text !== "}" &&
        this.current().kind !== "eof"
      )
        this.take();
      this.skipLines();
      return {
        tag: "unsupported",
        feature: `foreign import ${callingConvention.text}`,
        span: start,
      };
    }
    if (["unsafe", "safe", "interruptible"].includes(this.current().text))
      this.take();
    const javascript = this.take();
    let name = this.take();
    // Foreign imports use the same parenthesized spelling for symbolic
    // binders as ordinary declarations (`foreign import ... (<|>) :: ...`).
    if (name.text === "(") {
      name = this.take();
      this.expect(")");
    }
    if (!this.acceptTypeSignature()) {
      const token = this.current();
      this.diagnostics.push(
        error(
          "E_PARSE",
          "Foreign imports require a Haskell type signature",
          this.file,
          token.span.line,
          token.span.column,
        ),
      );
    }
    const signature: string[] = [];
    let current: string[] = [];
    let depth = 0;
    while (
      this.current().kind !== "newline" &&
      this.current().text !== ";" &&
      this.current().text !== "}" &&
      this.current().kind !== "eof"
    ) {
      const token = this.take();
      if (token.text === "(" || token.text === "[") depth++;
      else if (token.text === ")" || token.text === "]")
        depth = Math.max(0, depth - 1);
      if (token.text === "->" && depth === 0) {
        signature.push(current.join(" "));
        current = [];
      } else current.push(token.text);
    }
    if (current.length) signature.push(current.join(" "));
    this.lineEnd();
    if (javascript.kind !== "string")
      this.diagnostics.push(
        error(
          "E_PARSE",
          "Expected JavaScript string in foreign import",
          this.file,
          javascript.span.line,
          javascript.span.column,
        ),
      );
    if (signature.length < 1)
      this.diagnostics.push(
        error(
          "E_PARSE",
          "Foreign imports require a result type",
          this.file,
          name.span.line,
          name.span.column,
        ),
      );
    return {
      tag: "foreign",
      name: name.text,
      javascript: javascript.text,
      signature,
      arity: Math.max(0, signature.length - 1),
      span: start,
    };
  }
  private classDeclaration(): import("./ast.js").ClassDeclaration {
    const start = this.take().span;
    const header: Token[] = [];
    while (
      !["where", ";"].includes(this.current().text) &&
      this.current().kind !== "eof"
    )
      header.push(this.take());
    // The superclass context is part of the class's meaning - it decides the
    // dictionary's first fields - so it is kept rather than skipped.
    const arrow = header.findIndex((token) => token.text === "=>");
    const context =
      arrow < 0
        ? []
        : header
            .slice(0, arrow)
            .map((token) => token.text)
            .join(" ")
            .replace(/^\s*\(|\)\s*$/g, "")
            .split(",")
            .map((item) => item.trim())
            .filter(Boolean);
    const rest = arrow < 0 ? header : header.slice(arrow + 1);
    const uppercase = rest.filter(
      (token) => token.kind === "ident" && /^[A-Z]/.test(token.text),
    );
    const name = uppercase.at(-1)?.text ?? "<anonymous class>";
    const classIndex = rest.findIndex((token) => token.text === name);
    const parameters = rest
      .slice(classIndex + 1)
      .filter((token) => token.kind === "ident" && /^[a-z]/.test(token.text))
      .map((token) => token.text);
    const body = this.membersAfterWhere();
    return {
      tag: "class",
      name,
      context,
      parameters: [...new Set(parameters)],
      members: body.members,
      rawMembers: body.rawMembers,
      span: start,
    };
  }
  private instanceDeclaration(): import("./ast.js").InstanceDeclaration {
    const start = this.take().span;
    const header: Token[] = [];
    while (
      !["where", ";"].includes(this.current().text) &&
      this.current().kind !== "eof"
    )
      header.push(this.take());
    const body = this.membersAfterWhere();
    return {
      tag: "instance",
      head: header.map((token) => token.text).join(" "),
      members: body.members,
      rawMembers: body.rawMembers,
      span: start,
    };
  }
  private membersAfterWhere(): {
    members: Declaration[];
    rawMembers: import("./ast.js").ClassMemberSlice[];
  } {
    if (!this.accept("where")) {
      this.skipLines();
      return { members: [], rawMembers: [] };
    }
    this.skipLines();
    if (!this.acceptLayoutOpen()) {
      this.lineEnd();
      return { members: [], rawMembers: [] };
    }
    // Class and instance bodies may contain associated type families and
    // infix pattern equations. Preserve their enclosing token-delimited
    // region until the dictionary parser owns those member forms; trying to
    // parse every segment as a top-level declaration produces false syntax
    // failures on valid Miso source.
    let depth = 1;
    const members: Declaration[] = [];
    const rawMembers: import("./ast.js").ClassMemberSlice[] = [];
    let segment: Token[] = [];
    const finish = () => {
      if (!segment.length) return;
      rawMembers.push({
        tokens: segment.map(tokenSpelling),
        span: segment[0].span,
      });
      const signatureAt = segment.findIndex((token) => token.text === "::");
      if (signatureAt > 0) {
        const candidate =
          segment[0].text === "(" && segment[2]?.text === ")"
            ? segment[1]?.text
            : segment[0].text;
        const typeStart = signatureAt + 1;
        if (candidate && typeStart < segment.length)
          members.push({
            tag: "signature",
            name: candidate,
            type: segment
              .slice(typeStart)
              .map((token) => token.text)
              .join(" "),
            span: segment[0].span,
          });
      }
      segment = [];
    };
    while (depth && this.current().kind !== "eof") {
      const token = this.take();
      if (token.text === "{" && token.virtual) {
        depth++;
        if (depth > 1) segment.push(token);
        continue;
      }
      if (token.text === "}" && token.virtual) {
        depth--;
        if (depth === 0) finish();
        else segment.push(token);
        continue;
      }
      if (depth === 1 && token.text === ";" && token.virtual) {
        finish();
        continue;
      }
      segment.push(token);
    }
    return { members, rawMembers };
  }
  private lineEnd() {
    while (
      this.current().kind !== "newline" &&
      this.current().text !== ";" &&
      this.current().text !== "}" &&
      this.current().kind !== "eof"
    )
      this.take();
    this.skipLines();
  }
  private expression(min = -1): Expr {
    let left = this.application();
    let operator =
      this.index === this.expressionStop ? undefined : this.currentOperator();
    let fixity = operator && this.operatorFixity(operator);
    while (operator && fixity && fixity.prec >= min) {
      const op = this.takeOperator()!;
      const right = this.expression(
        fixity.prec + (fixity.assoc === "right" ? 0 : 1),
      );
      const fn: Expr = { tag: "var", name: op.text, span: op.span };
      left = {
        tag: "app",
        fn: { tag: "app", fn, arg: left, span: left.span },
        arg: right,
        span: op.span,
      };
      operator =
        this.index === this.expressionStop ? undefined : this.currentOperator();
      fixity = operator && this.operatorFixity(operator);
    }
    if (this.acceptTypeSignature()) this.skipTypeAnnotation();
    return left;
  }
  /** `S.|>` lexes as ident `S.` plus symbol `|>`. Treat that pair as one operator. */
  private qualifiedOperator(): Token | undefined {
    const qualifier = this.current();
    const operator = this.tokens[this.index + 1];
    if (
      qualifier.kind !== "ident" ||
      !qualifier.text.endsWith(".") ||
      !operator ||
      this.operatorPrecedence(operator) === undefined
    )
      return undefined;
    return {
      ...operator,
      kind: "symbol",
      text: `${qualifier.text}${operator.text}`,
      span: {
        start: qualifier.span.start,
        end: operator.span.end,
        line: qualifier.span.line,
        column: qualifier.span.column,
      },
    };
  }
  private currentOperator(): Token | undefined {
    const qualified = this.qualifiedOperator();
    if (qualified) return qualified;
    if (
      this.current().text === "`" &&
      this.tokens[this.index + 1]?.kind === "ident" &&
      this.tokens[this.index + 2]?.text === "`"
    )
      return { ...this.tokens[this.index + 1]!, kind: "symbol" };
    return this.current();
  }
  private takeOperator(): Token | undefined {
    const qualified = this.qualifiedOperator();
    if (qualified) {
      this.take();
      this.take();
      return qualified;
    }
    if (this.current().text === "`") {
      this.take();
      const name = this.take();
      this.expect("`");
      return { ...name, kind: "symbol" };
    }
    return this.take();
  }
  private operatorFixity(
    token: Token,
  ): { prec: number; assoc: Assoc } | undefined {
    if (
      token.kind !== "symbol" ||
      [
        "=",
        "|",
        "->",
        "<-",
        "::",
        "=>",
        ",",
        ";",
        "(",
        ")",
        "[",
        "]",
        "{",
        "}",
        "@",
        "..",
      ].includes(token.text)
    )
      return undefined;
    return operators[token.text] ?? { prec: 4, assoc: "left" };
  }
  private operatorPrecedence(token: Token): number | undefined {
    return this.operatorFixity(token)?.prec;
  }
  // Haskell's grammar gives `-` a special prefix-negation reading only at
  // the start of an expression (`lexp -> "-" exp10`), never as a later
  // application argument - `f -5` means `f - 5` (subtraction), not `f
  // (negate 5)`, which is why this lives in `application()`'s own base
  // term, not inside `atom()` (called for every later argument too).
  // Without this, a bare `-5` outside parens fell through atom()'s
  // catch-all `{ tag: "var", name: "-" }` and silently became a partially
  // applied `(-)` section instead of `negate 5` - already handled correctly
  // for the parenthesized `(-5)` case above, just missing here.
  private negativeLiteral(): Expr | undefined {
    if (this.current().text !== "-") return undefined;
    const saved = this.index;
    const minus = this.take();
    if (this.startsAtom()) {
      const operand = this.recordUpdates(this.atom());
      return {
        tag: "app",
        fn: { tag: "var", name: "negate", span: minus.span },
        arg: operand,
        span: minus.span,
      };
    }
    this.index = saved;
    return undefined;
  }
  // Layout separators, not physical newlines, delimit expressions.  This is
  // what lets an application such as `vfrag` followed by a list on the next
  // line retain its ordinary Haskell meaning.
  private application(): Expr {
    let value = this.negativeLiteral() ?? this.recordUpdates(this.atom());
    this.skipVisibleTypeApplications();
    while (this.startsAtom()) {
      const arg = this.recordUpdates(this.atom());
      value = { tag: "app", fn: value, arg, span: value.span };
      this.skipVisibleTypeApplications();
    }
    return value;
  }
  private recordUpdates(base: Expr): Expr {
    while (
      this.current().kind === "symbol" &&
      this.current().text === "{" &&
      !this.current().virtual
    ) {
      this.take();
      const record = this.recordFields();
      base = {
        tag: "recordUpdate",
        base,
        fields: record.fields,
        span: base.span,
      };
    }
    return base;
  }
  private skipVisibleTypeApplications() {
    while (this.current().text === "@") {
      this.take();
      if (this.current().text === "'") this.take();
      const open = this.current().text;
      if (open === "(" || open === "[") {
        const close = open === "(" ? ")" : "]";
        this.take();
        let depth = 1;
        while (depth && this.current().kind !== "eof") {
          if (this.current().text === open) depth++;
          else if (this.current().text === close) depth--;
          this.take();
        }
        continue;
      }
      if (this.current().kind === "ident") this.take();
    }
  }
  private startsAtom() {
    const t = this.current();
    return (
      (t.kind === "ident" &&
        !["then", "else", "of", "where", "in"].includes(t.text) &&
        !this.qualifiedOperator()) ||
      t.kind === "int" ||
      t.kind === "float" ||
      t.kind === "string" ||
      t.kind === "char" ||
      t.kind === "quasiquote" ||
      t.text === "(" ||
      t.text === "[" ||
      t.text === "\\"
    );
  }
  private atom(): Expr {
    const t = this.take();
    if (t.kind === "int")
      return { tag: "int", value: Number(t.text), span: t.span };
    if (t.kind === "float")
      return { tag: "double", value: Number(t.text), span: t.span };
    if (t.kind === "string" || t.kind === "char")
      return { tag: "string", value: t.text, span: t.span };
    if (t.kind === "quasiquote")
      return { tag: "jsQuote", body: t.text, quoter: t.quoter, span: t.span };
    if (t.kind === "ident" && t.text === "if") {
      const condition = this.expression();
      this.expect("then");
      const thenBranch = this.expression();
      this.expect("else");
      return {
        tag: "if",
        condition,
        thenBranch,
        elseBranch: this.expression(),
        span: t.span,
      };
    }
    if (t.kind === "ident" && t.text === "let") {
      const bindings = this.localBindings("in");
      if (!bindings.length)
        this.diagnostics.push(
          error(
            "E_PARSE",
            "Expected at least one let binding",
            this.file,
            t.span.line,
            t.span.column,
          ),
        );
      this.expect("in");
      return { tag: "let", bindings, body: this.expression(), span: t.span };
    }
    if (t.kind === "ident" && t.text === "do") {
      this.skipLines();
      this.acceptLayoutOpen();
      const statements: import("./ast.js").DoStatement[] = [];
      while (
        this.current().kind !== "eof" &&
        this.current().text !== "where" &&
        this.current().text !== "}"
      ) {
        // Unlike an expression-level `let`, a do-statement binding has no
        // `in`: its scope is the rest of the block.
        if (this.accept("let"))
          statements.push({ tag: "let", bindings: this.localBindings() });
        else if (
          !["case", "if", "do", "let"].includes(this.current().text) &&
          this.hasDoBind()
        ) {
          const pattern = this.pattern();
          // Pattern signatures (`x :: T <- action`) constrain the binder but
          // do not change the do-statement delimiter.
          if (this.acceptTypeSignature())
            while (
              this.current().text !== "<-" &&
              this.current().kind !== "eof"
            )
              this.take();
          this.expect("<-");
          statements.push({ tag: "bind", pattern, source: this.expression() });
        } else statements.push({ tag: "expr", expr: this.expression() });
        this.skipLines();
      }
      // A `where` after a do RHS belongs to the enclosing equation/case
      // alternative.  Layout nevertheless leaves the do block open until
      // that declaration group ends, so consume the group here and retain it
      // as a lexical let around the finished do expression.
      const whereBindings = this.accept("where") ? this.localBindings() : [];
      this.acceptLayoutClose();
      if (!statements.length)
        this.diagnostics.push(
          error(
            "E_PARSE",
            "Expected at least one statement in do block",
            this.file,
            t.span.line,
            t.span.column,
          ),
        );
      const block: Expr = { tag: "do", statements, span: t.span };
      return whereBindings.length
        ? { tag: "let", bindings: whereBindings, body: block, span: t.span }
        : block;
    }
    if (t.kind === "ident" && t.text === "case") {
      const subject = this.expression();
      this.expect("of");
      return {
        tag: "case",
        subject,
        alternatives: this.caseAlternatives(t),
        span: t.span,
      };
    }
    if (t.text === "\\") {
      if (this.current().text === "case") {
        this.take();
        return {
          tag: "lambdaCase",
          alternatives: this.caseAlternatives(t),
          span: t.span,
        };
      }
      const parameters: import("./ast.js").Pattern[] = [];
      while (this.current().text !== "->" && this.current().kind !== "eof")
        parameters.push(this.lambdaPattern());
      this.expect("->");
      let body = this.expression();
      for (let index = parameters.length - 1; index >= 0; index--)
        body = this.lambdaFromPattern(parameters[index]!, body);
      return body;
    }
    if (t.text === "[") {
      if (this.accept("]")) return { tag: "list", items: [], span: t.span };
      const body = this.expression();
      if (this.accept("|")) {
        const qualifiers: import("./ast.js").ListQualifier[] = [];
        do {
          if (this.hasPatternGuard()) {
            const pattern = this.pattern();
            this.expect("<-");
            qualifiers.push({
              tag: "generator",
              pattern,
              source: this.expression(),
            });
          } else
            qualifiers.push({ tag: "guard", condition: this.expression() });
        } while (this.accept(","));
        this.expect("]");
        return { tag: "listComp", body, qualifiers, span: t.span };
      }
      if (this.accept("..")) {
        if (this.accept("]")) return applyNamed("enumFrom", [body], t.span);
        const end = this.expression();
        this.expect("]");
        return applyNamed("enumFromTo", [body, end], t.span);
      }
      const items = [body];
      if (this.accept(",")) {
        const second = this.expression();
        if (this.accept("..")) {
          if (this.accept("]"))
            return applyNamed("enumFromThen", [body, second], t.span);
          const end = this.expression();
          this.expect("]");
          return applyNamed("enumFromThenTo", [body, second, end], t.span);
        }
        items.push(second);
        while (this.accept(",")) items.push(this.expression());
      }
      this.expect("]");
      return { tag: "list", items, span: t.span };
    }
    if (t.text === "(") {
      if (this.accept(")")) return { tag: "unit", span: t.span };
      // Tuple constructors are ordinary Haskell values: `(,)`, `(,,)`, etc.
      // Keep them as constructor names so typechecking and lowering can use
      // the same representation as tuple patterns and literals.
      if (this.current().text === ",") {
        let commas = 0;
        while (this.accept(",")) commas++;
        this.expect(")");
        return { tag: "var", name: `(${",".repeat(commas)})`, span: t.span };
      }
      if (this.current().text === "-") {
        const saved = this.index;
        this.take();
        if (this.startsAtom()) {
          const operand = this.recordUpdates(this.atom());
          if (this.current().text === ")") {
            this.expect(")");
            return {
              tag: "app",
              fn: { tag: "var", name: "negate", span: t.span },
              arg: operand,
              span: t.span,
            };
          }
        }
        this.index = saved;
      }
      if (
        this.operatorPrecedence(this.current()) !== undefined &&
        this.current().text !== "-" &&
        this.current().text !== "\\" &&
        this.current().text !== "`" &&
        this.tokens[this.index + 1]?.text !== ")"
      ) {
        const operator = this.take();
        const operand = this.expression();
        this.expect(")");
        const parameter = `__ghctsSection${t.span.start}`;
        const argument: Expr = {
          tag: "var",
          name: parameter,
          span: operator.span,
        };
        return {
          tag: "lambda",
          parameter,
          body: {
            tag: "app",
            fn: {
              tag: "app",
              fn: { tag: "var", name: operator.text, span: operator.span },
              arg: argument,
              span: operator.span,
            },
            arg: operand,
            span: operand.span,
          },
          span: t.span,
        };
      }
      // A parenthesized backticked operator with its right operand is a left
      // section: `(`S.member` set)` means `\\value -> value `S.member` set`.
      // This form is common in parser combinators and cannot be treated as a
      // parenthesized ordinary expression because the opening backtick is not
      // itself an atom.
      if (this.qualifiedOperator()) {
        const operator = this.takeOperator()!;
        const operand = this.expression();
        this.expect(")");
        const parameter = `__ghctsSection${t.span.start}`;
        const argument: Expr = {
          tag: "var",
          name: parameter,
          span: operator.span,
        };
        return {
          tag: "lambda",
          parameter,
          body: {
            tag: "app",
            fn: {
              tag: "app",
              fn: { tag: "var", name: operator.text, span: operator.span },
              arg: argument,
              span: operator.span,
            },
            arg: operand,
            span: operand.span,
          },
          span: t.span,
        };
      }
      if (
        this.current().text === "`" &&
        this.tokens[this.index + 1]?.kind === "ident" &&
        this.tokens[this.index + 2]?.text === "`"
      ) {
        const operator = this.takeOperator()!;
        const operand = this.expression();
        this.expect(")");
        const parameter = `__ghctsSection${t.span.start}`;
        const argument: Expr = {
          tag: "var",
          name: parameter,
          span: operator.span,
        };
        return {
          tag: "lambda",
          parameter,
          body: {
            tag: "app",
            fn: {
              tag: "app",
              fn: { tag: "var", name: operator.text, span: operator.span },
              arg: argument,
              span: operator.span,
            },
            arg: operand,
            span: operand.span,
          },
          span: t.span,
        };
      }
      const sectionOperator = this.rightSectionOperator();
      if (sectionOperator !== undefined) {
        const previousStop = this.expressionStop;
        this.expressionStop = sectionOperator;
        const operand = this.expression();
        this.expressionStop = previousStop;
        const operator = this.take();
        this.expect(")");
        const parameter = `__ghctsSection${t.span.start}`;
        const argument: Expr = {
          tag: "var",
          name: parameter,
          span: operator.span,
        };
        return {
          tag: "lambda",
          parameter,
          body: {
            tag: "app",
            fn: {
              tag: "app",
              fn: { tag: "var", name: operator.text, span: operator.span },
              arg: operand,
              span: operand.span,
            },
            arg: argument,
            span: operator.span,
          },
          span: t.span,
        };
      }
      const first = this.expression();
      // Right sections are parsed from the token stream, rather than being
      // rewritten by CPP preprocessing.  The lambda is ordinary AST-level
      // desugaring and preserves lazy application semantics.
      if (
        this.operatorPrecedence(this.current()) !== undefined &&
        this.tokens[this.index + 1]?.text === ")"
      ) {
        const operator = this.take();
        this.expect(")");
        const parameter = `__ghctsSection${t.span.start}`;
        const argument: Expr = {
          tag: "var",
          name: parameter,
          span: operator.span,
        };
        return {
          tag: "lambda",
          parameter,
          body: {
            tag: "app",
            fn: {
              tag: "app",
              fn: { tag: "var", name: operator.text, span: operator.span },
              arg: first,
              span: first.span,
            },
            arg: argument,
            span: operator.span,
          },
          span: t.span,
        };
      }
      if (this.acceptTypeSignature()) {
        while (this.current().text !== ")" && this.current().kind !== "eof")
          this.take();
        this.expect(")");
        return first;
      }
      if (!this.accept(",")) {
        this.expect(")");
        return first;
      }
      const items = [first];
      do {
        items.push(this.expression());
      } while (this.accept(","));
      this.expect(")");
      return { tag: "tuple", items, span: t.span };
    }
    // A char literal token can contain `{`; record syntax requires a source
    // punctuation token, never merely matching token text.
    if (
      t.kind === "ident" &&
      this.current().kind === "symbol" &&
      this.accept("{")
    ) {
      const record = this.recordFields();
      const fields = record.fields;
      return /^[A-Z]/.test(t.text)
        ? { tag: "record", constructor: t.text, fields, wildcard: record.wildcard, span: t.span }
        : {
            tag: "recordUpdate",
            base: { tag: "var", name: t.text, span: t.span },
            fields,
            span: t.span,
          };
    }
    if (t.kind === "ident" || t.kind === "symbol")
      return { tag: "var", name: t.text, span: t.span };
    this.diagnostics.push(
      error(
        "E_PARSE",
        `Expected expression, found ${t.text || "end of input"}`,
        this.file,
        t.span.line,
        t.span.column,
      ),
    );
    return { tag: "var", name: "undefined", span: t.span };
  }
  private pattern(): import("./ast.js").Pattern {
    const token = this.take();
    if (token.text === "!") return this.pattern();
    if (token.text === "(") {
      if (this.accept(")"))
        return { tag: "con", name: "()", args: [], span: token.span };
      const left = this.pattern();
      if (this.acceptTypeSignature()) this.skipTypeAnnotation();
      if (
        this.current().kind === "ident" &&
        this.current().text.endsWith(".") &&
        this.tokens[this.index + 1]?.kind === "symbol"
      ) {
        const qualifier = this.take();
        const operator = this.take();
        const right = this.pattern();
        this.expect(")");
        return {
          tag: "con",
          name: `${qualifier.text}${operator.text}`,
          args: [left, right],
          span: token.span,
        };
      }
      if (this.accept(":")) {
        const parts = [left];
        do {
          parts.push(this.pattern());
        } while (this.accept(":"));
        this.expect(")");
        let tail = parts.at(-1)!;
        for (let index = parts.length - 2; index >= 0; index--)
          tail = {
            tag: "con",
            name: ":",
            args: [parts[index], tail],
            span: parts[index].span,
          };
        return tail;
      }
      if (this.accept(",")) {
        const args = [left];
        do {
          args.push(this.pattern());
        } while (this.accept(","));
        this.expect(")");
        return {
          tag: "con",
          name: `(${",".repeat(args.length - 1)})`,
          args,
          span: token.span,
        };
      }
      this.expect(")");
      return left;
    }
    if (token.text === "[") {
      const patterns: import("./ast.js").Pattern[] = [];
      if (!this.accept("]")) {
        do {
          patterns.push(this.pattern());
        } while (this.accept(","));
        this.expect("]");
      }
      return patterns
        .reverse()
        .reduce<import("./ast.js").Pattern>(
          (tail, head) => ({
            tag: "con",
            name: ":",
            args: [head, tail],
            span: head.span,
          }),
          { tag: "con", name: "[]", args: [], span: token.span },
        );
    }
    if (token.kind === "int")
      return { tag: "int", value: Number(token.text), span: token.span };
    if (token.kind === "string" || token.kind === "char")
      return { tag: "string", value: token.text, span: token.span };
    if (token.kind === "ident") {
      if (token.text === "_") return { tag: "wild", span: token.span };
      if (this.accept("@"))
        return {
          tag: "as",
          name: token.text,
          pattern: this.pattern(),
          span: token.span,
        };
      if (/^[A-Z]/.test(token.text)) {
        const args: import("./ast.js").Pattern[] = [];
        // Constructor arguments are `apat`s: `CrossThread BTS True` is two
        // fields, not `BTS True`. Nested constructors need parentheses.
        while (this.startsPattern()) args.push(this.lambdaPattern());
        if (this.accept("{")) {
          const fields: Array<{ name: string; pattern: import("./ast.js").Pattern }> = [];
          let wildcard = false;
          while (this.current().kind !== "eof" && this.current().text !== "}") {
            if (this.accept("..")) wildcard = true;
            else {
              const field = this.take();
              if (this.accept("=")) fields.push({ name: field.text, pattern: this.pattern() });
              else fields.push({ name: field.text, pattern: { tag: "var", name: field.text, span: field.span } });
            }
            this.accept(",");
          }
          this.expect("}");
          return { tag: "record", name: token.text, fields, wildcard, span: token.span };
        }
        return { tag: "con", name: token.text, args, span: token.span };
      }
      return { tag: "var", name: token.text, span: token.span };
    }
    this.diagnostics.push(
      error(
        "E_PARSE",
        `Expected pattern, found ${token.text}`,
        this.file,
        token.span.line,
        token.span.column,
      ),
    );
    return { tag: "wild", span: token.span };
  }
  private recordFields(): { fields: Array<{ name: string; value: Expr }>; wildcard: boolean } {
    const fields: Array<{ name: string; value: Expr }> = [];
    let wildcard = false;
    while (this.current().text !== "}" && this.current().kind !== "eof") {
      if (this.accept("..")) {
        wildcard = true;
        break;
      }
      const name = this.take();
      this.expect("=");
      fields.push({ name: name.text, value: this.expression() });
      if (!this.accept(",")) break;
    }
    this.expect("}");
    return { fields, wildcard };
  }
  private rightSectionOperator(): number | undefined {
    let depth = 0;
    for (let cursor = this.index; cursor < this.tokens.length; cursor++) {
      const token = this.tokens[cursor];
      if (token.kind !== "symbol") continue;
      if (token.text === "(" || token.text === "[" || token.text === "{") {
        depth++;
        continue;
      }
      if (token.text === ")" || token.text === "]" || token.text === "}") {
        if (token.text === ")" && depth === 0) {
          const operatorIndex = cursor - 1;
          return operatorIndex > this.index &&
            this.operatorPrecedence(this.tokens[operatorIndex]!) !== undefined
            ? operatorIndex
            : undefined;
        }
        depth = Math.max(0, depth - 1);
      }
    }
    return undefined;
  }
  private skipTypeAnnotation() {
    let depth = 0;
    while (this.current().kind !== "eof") {
      const token = this.current();
      if (token.text === "(" || token.text === "[") {
        depth++;
        this.take();
        continue;
      }
      if (token.text === ")" || token.text === "]") {
        if (!depth) return;
        depth--;
        this.take();
        continue;
      }
      if (
        !depth &&
        (token.text === "," ||
          token.text === ";" ||
          token.text === "}" ||
          token.text === "of" ||
          token.text === "then" ||
          token.text === "else" ||
          token.text === "in" ||
          token.text === "where")
      )
        return;
      this.take();
    }
  }
  private lambdaPattern(): import("./ast.js").Pattern {
    const token = this.current();
    if (token.text === "(" || token.text === "[" || token.text === "!")
      return this.pattern();
    if (token.kind === "int" || token.kind === "float" || token.kind === "string" || token.kind === "char")
      return this.pattern();
    if (token.kind === "ident") {
      this.take();
      if (token.text === "_") return { tag: "wild", span: token.span };
      if (this.accept("@"))
        return {
          tag: "as",
          name: token.text,
          pattern: this.lambdaPattern(),
          span: token.span,
        };
      if (/^[A-Z]/.test(token.text)) {
        if (this.accept("{")) {
          const fields: Array<{ name: string; pattern: import("./ast.js").Pattern }> = [];
          let wildcard = false;
          while (this.current().kind !== "eof" && this.current().text !== "}") {
            if (this.accept("..")) wildcard = true;
            else {
              const field = this.take();
              if (this.accept("="))
                fields.push({ name: field.text, pattern: this.pattern() });
              else
                fields.push({
                  name: field.text,
                  pattern: { tag: "var", name: field.text, span: field.span },
                });
            }
            this.accept(",");
          }
          this.expect("}");
          return { tag: "record", name: token.text, fields, wildcard, span: token.span };
        }
        return { tag: "con", name: token.text, args: [], span: token.span };
      }
      return { tag: "var", name: token.text, span: token.span };
    }
    return this.pattern();
  }
  private lambdaFromPattern(
    pattern: import("./ast.js").Pattern,
    body: Expr,
  ): Expr {
    if (pattern.tag === "var")
      return {
        tag: "lambda",
        parameter: pattern.name,
        body,
        span: pattern.span,
      };
    if (pattern.tag === "wild")
      return { tag: "lambda", parameter: "_", body, span: pattern.span };
    const parameter = `__pat${pattern.span.start}`;
    return {
      tag: "lambda",
      parameter,
      body: {
        tag: "case",
        subject: { tag: "var", name: parameter, span: pattern.span },
        alternatives: [{ pattern, body }],
        span: pattern.span,
      },
      span: pattern.span,
    };
  }
  private startsPattern() {
    const token = this.current();
    return (
      token.kind === "ident" ||
      token.kind === "int" ||
      token.kind === "float" ||
      token.kind === "string" ||
      token.kind === "char" ||
      token.text === "(" ||
      token.text === "[" ||
      token.text === "!"
    );
  }
  private skipBalanced(open: string, close: string) {
    let depth = 1;
    while (depth && this.current().kind !== "eof") {
      const token = this.take();
      if (token.text === open) depth++;
      else if (token.text === close) depth--;
    }
  }
  private unsupportedBlock(): import("./ast.js").UnsupportedDeclaration {
    const start = this.take().span;
    const feature = this.tokens[this.index - 1].text;
    while (
      !["where", ";"].includes(this.current().text) &&
      this.current().kind !== "eof"
    )
      this.take();
    if (this.accept("where")) {
      this.acceptLayoutOpen();
      let depth = 1;
      while (depth && this.current().kind !== "eof") {
        if (this.current().text === "{" && this.current().virtual) depth++;
        else if (this.current().text === "}" && this.current().virtual) depth--;
        this.take();
      }
    } else this.skipLines();
    return { tag: "unsupported", feature, span: start };
  }
  private localBindings(
    terminator?: string,
  ): import("./ast.js").LocalBinding[] {
    this.skipLines();
    this.acceptLayoutOpen();
    const bindings: import("./ast.js").LocalBinding[] = [];
    while (
      this.startsPattern() &&
      this.current().text !== terminator &&
      this.current().text !== "}"
    ) {
      if (this.current().text === "(" || this.current().text === "[") {
        const start = this.current().span;
        const pattern = this.pattern();
        this.expect("=");
        const value = this.expression();
        bindings.push({
          name: `__pattern_${start.start}`,
          patterns: [pattern],
          value,
          guards: [{ body: value }],
          span: start,
        });
        this.skipLines();
        continue;
      }
      const name = this.take();
      // Constructor patterns are not function binders (`let ComponentState {..} =`,
      // `let Just x =`). Bind the matched names from the right-hand side.
      if (/^[A-Z]/.test(name.text)) {
        this.index--;
        const pattern = this.pattern();
        this.expect("=");
        const value = this.expression();
        bindings.push({
          name: `__pattern_${name.span.start}`,
          patterns: [pattern],
          value,
          guards: [{ body: value }],
          span: name.span,
        });
        this.skipLines();
        continue;
      }
      if (this.acceptTypeSignature()) {
        while (
          this.current().text !== ";" &&
          this.current().text !== "}" &&
          this.current().kind !== "eof"
        )
          this.take();
        this.skipLines();
        continue;
      }
      const patterns: import("./ast.js").Pattern[] = [];
      while (
        !["=", "|"].includes(this.current().text) &&
        this.current().kind !== "eof"
      )
        patterns.push(this.lambdaPattern());
      const guards: import("./ast.js").Guard[] = [];
      if (this.accept("|")) {
        do {
          const guard = this.guard();
          this.expect("=");
          guards.push({ ...guard, body: this.expression() });
          this.skipLines();
        } while (this.accept("|"));
      } else {
        this.expect("=");
        guards.push({ body: this.expression() });
      }
      const whereBindings = this.accept("where")
        ? this.localBindings()
        : undefined;
      bindings.push({
        name: name.text,
        patterns,
        value: guards[0].body,
        guards,
        whereBindings,
        span: name.span,
      });
      this.skipLines();
    }
    this.acceptLayoutClose();
    return bindings;
  }
  private guard(): Omit<import("./ast.js").Guard, "body"> {
    if (this.hasPatternGuard()) {
      const pattern = this.pattern();
      this.expect("<-");
      return { pattern, source: this.expression() };
    }
    let condition = this.expression();
    while (this.accept(",")) {
      const right = this.expression();
      condition = {
        tag: "app",
        fn: {
          tag: "app",
          fn: { tag: "var", name: "&&", span: condition.span },
          arg: condition,
          span: condition.span,
        },
        arg: right,
        span: right.span,
      };
    }
    return { condition };
  }
  private hasPatternGuard() {
    let delimiters = 0;
    for (let cursor = this.index; cursor < this.tokens.length; cursor++) {
      const token = this.tokens[cursor];
      if (
        token.kind === "symbol" &&
        (token.text === "(" ||
          token.text === "[" ||
          (token.text === "{" && !token.virtual))
      ) {
        delimiters++;
        continue;
      }
      if (
        token.kind === "symbol" &&
        (token.text === ")" ||
          token.text === "]" ||
          (token.text === "}" && !token.virtual))
      ) {
        delimiters = Math.max(0, delimiters - 1);
        continue;
      }
      if (!delimiters && token.text === "<-") return true;
      if (
        !delimiters &&
        (["=", "|", ",", ";", "}", "->"].includes(token.text) || token.kind === "eof")
      )
        return false;
    }
    return false;
  }
  private hasDoBind() {
    // `<-` inside a list comprehension, tuple, or function argument is not
    // the delimiter for the surrounding do-statement.
    let delimiters = 0;
    for (let cursor = this.index; cursor < this.tokens.length; cursor++) {
      const token = this.tokens[cursor];
      if (
        token.kind === "symbol" &&
        (token.text === "(" ||
          token.text === "[" ||
          (token.text === "{" && !token.virtual))
      ) {
        delimiters++;
        continue;
      }
      if (
        token.kind === "symbol" &&
        (token.text === ")" ||
          token.text === "]" ||
          (token.text === "}" && !token.virtual))
      ) {
        delimiters = Math.max(0, delimiters - 1);
        continue;
      }
      if (!delimiters && token.text === "<-") return true;
      if (
        !delimiters &&
        (token.text === "do" ||
          token.text === "->" ||
          (token.text === ";" && token.virtual) ||
          (token.text === "}" && token.virtual) ||
          token.kind === "eof")
      )
        return false;
    }
    return false;
  }
  private caseAlternatives(token: Token): import("./ast.js").CaseAlternative[] {
    this.skipLines();
    this.acceptLayoutOpen();
    const alternatives: import("./ast.js").CaseAlternative[] = [];
    while (
      this.current().kind !== "eof" &&
      this.current().text !== "}"
    ) {
      let pattern = this.pattern();
      while (this.accept(":"))
        pattern = {
          tag: "con",
          name: ":",
          args: [pattern, this.pattern()],
          span: pattern.span,
        };
      const addGuardedBody = (
        guard?: Expr,
        patternGuards?: Array<{ pattern: import("./ast.js").Pattern; source: Expr }>,
      ) => {
        this.expect("->");
        const result = this.expression();
        const bindings = this.accept("where") ? this.localBindings() : [];
        alternatives.push({
          pattern,
          guard,
          patternGuards,
          body: bindings.length
            ? { tag: "let", bindings, body: result, span: result.span }
            : result,
        });
        this.skipLines();
      };
      if (this.accept("|")) {
        if (this.hasPatternGuard()) {
          const patternGuards: Array<{
            pattern: import("./ast.js").Pattern;
            source: Expr;
          }> = [];
          while (true) {
            const guarded = this.pattern();
            this.expect("<-");
            patternGuards.push({ pattern: guarded, source: this.expression() });
            if (!this.accept("|")) {
              addGuardedBody(undefined, patternGuards);
              break;
            }
            if (!this.hasPatternGuard()) {
              addGuardedBody(this.expression(), patternGuards);
              break;
            }
          }
        } else {
          addGuardedBody(this.expression());
          while (this.accept("|")) addGuardedBody(this.expression());
        }
      } else addGuardedBody(undefined);
    }
    this.acceptLayoutClose();
    if (!alternatives.length)
      this.diagnostics.push(
        error(
          "E_PARSE",
          "Expected at least one case alternative",
          this.file,
          token.span.line,
          token.span.column,
        ),
      );
    return alternatives;
  }
}
