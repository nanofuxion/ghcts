import type {
  CaseAlternative,
  DataDeclaration,
  Declaration,
  DoStatement,
  Expr,
  Guard,
  GuardQualifier,
  ImportDeclaration,
  ListQualifier,
  LocalBinding,
  Module,
  Pattern,
  Span,
  ValueDeclaration,
} from "./ast.js";
import { createHash } from "node:crypto";
import { error } from "./diagnostics.js";
import { applyLayout, lex, type Token } from "./lexer.js";
import type { Diagnostic } from "./types.js";
export interface ParsedModule {
  ast: Module;
  source: string;
  file: string;
}

function declaredExtensions(source: string): Set<string> {
  const out = new Set<string>();
  for (const m of source.matchAll(/\{-#\s*LANGUAGE\s+([\s\S]*?)#-\}/g))
    for (const name of m[1]!.split(/[,(\s]+/).map((x) => x.trim()).filter(Boolean)) out.add(name);
  return out;
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
  // `infixl 3` in base. Left to the fallback it tied with `.:`, so
  // `o .: "keyCode" <|> o .: "which"` parsed as `((o .: "keyCode") <|> o) .: "which"`.
  "<|>": { prec: 2, assoc: "left" },
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
  // `GHC.Generics` declares `infixr 5 :+:` and `infixr 6 :*:`. The *type*
  // parser gives every type operator right-associativity outright, so without
  // these two the same `a :*: b :*: c` associated one way in a type and the
  // other in the expression it was the type of.
  ":+:": { prec: 4, assoc: "right" },
  ":*:": { prec: 5, assoc: "right" },
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
  const tokens = applyLayout(result.tokens);
  let parser = new Parser(tokens, file, result.diagnostics);
  let ast = parser.module();
  // A pattern binding is split into selectors as it is read, so `let C {..} = e`
  // has to know C's fields *then* - and a `data` declaration below it in the
  // file has not been read yet (miso's `let ComponentState {..} = ...` is 350
  // lines above the record). Parse the module again, seeded with the fields the
  // first pass found, but only when the first pass actually hit that case.
  if (parser.wildcardBindingUnresolved) {
    const fields = parser.recordFieldsByCon;
    result.diagnostics.length = 0;
    parser = new Parser(tokens, file, result.diagnostics, fields);
    ast = parser.module();
  }
  expandTemplateHaskell(ast);
  const inlineNames = [...source.matchAll(/\{-#\s*INLINE\s+([^\s#}]+)\s*#-\}/g)].map((m) => m[1]!);
  if (inlineNames.length) {
    for (const declaration of ast.declarations) {
      if (declaration.tag !== "instance") continue;
      const methodNames = new Set(declaration.rawMembers.flatMap((member) => member.tokens));
      const names = inlineNames.filter((name) => methodNames.has(name));
      if (names.length) declaration.inlineNames = names;
    }
  }
  const extensions = declaredExtensions(source);
  const usesStaticPointer = tokens.some((token) => token.kind === "ident" && token.text === "static");
  if (usesStaticPointer && !extensions.has("StaticPointers"))
    result.diagnostics.push(error("E_EXTENSION", "Static pointer syntax requires the StaticPointers extension", file));
  return {
    module: result.diagnostics.some((d) => d.severity === "error")
      ? undefined
      : { ast: inlineNames.length ? { ...ast, inlineNames } : ast, source, file },
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
    case "annot":
    case "typeApp":
      return { ...expr, expr: expandExprQuotes(expr.expr) };
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
function expandQualifiersQuotes(qualifiers: GuardQualifier[] | undefined): GuardQualifier[] | undefined {
  return qualifiers?.map((q) =>
    q.tag === "bool" ? { ...q, condition: expandExprQuotes(q.condition) } : { ...q, source: expandExprQuotes(q.source) },
  );
}
function expandAlternativeQuotes(alternative: CaseAlternative): CaseAlternative {
  return {
    ...alternative,
    qualifiers: expandQualifiersQuotes(alternative.qualifiers),
    body: expandExprQuotes(alternative.body),
  };
}
function expandGuardQuotes(guard: Guard): Guard {
  return {
    ...guard,
    qualifiers: expandQualifiersQuotes(guard.qualifiers),
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
/** One string per constraint of a `(C a, D b) =>` context.  The count is what
 * fixes how many dictionary fields the constructor gains, so the split has to
 * be exactly at the context's own commas and nowhere inside a nested type. */
function splitConstraints(tokens: readonly string[]): string[] {
  const inner = tokens[0] === "(" && tokens[tokens.length - 1] === ")" ? tokens.slice(1, -1) : tokens;
  const parts: string[][] = [[]];
  let depth = 0;
  for (const token of inner) {
    if (token === "(" || token === "[") depth++;
    else if (token === ")" || token === "]") depth--;
    else if (depth === 0 && token === ",") {
      parts.push([]);
      continue;
    }
    parts[parts.length - 1]!.push(token);
  }
  return parts.map((part) => part.join(" ")).filter((part) => part.length > 0);
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
/** GHC's `mkStaticPtrFingerprint`: `fingerprintString "unit:module:index"`.
 *
 * The key has to be a *function of the source*, not of anything that happens at
 * run time. A `static` form is looked up from a JavaScript context other than
 * the one that built it - miso's main-thread scheduler derefs a pointer the
 * worker only ever names - and the two contexts share nothing but the program
 * text, so an allocation counter would give them two different keys for one
 * value.
 *
 * `fingerprintString` hashes each `Char` as four big-endian bytes (not UTF-8),
 * and `peekFingerprint` reads the 16-byte digest as two big-endian `Word64`s.
 * Splitting those into four 32-bit words is what `h$hs_spt_insert` takes, and
 * is the same order GHC's own `StgToJS.StaticPtr` passes them in. */
function staticPtrFingerprint(unit: string, moduleName: string, index: number): [number, number, number, number] {
  const text = `${unit}:${moduleName}:${index}`;
  const bytes = new Uint8Array(text.length * 4);
  for (let i = 0; i < text.length; i++) {
    const c = text.charCodeAt(i);
    bytes[i * 4] = (c >>> 24) & 0xff;
    bytes[i * 4 + 1] = (c >>> 16) & 0xff;
    bytes[i * 4 + 2] = (c >>> 8) & 0xff;
    bytes[i * 4 + 3] = c & 0xff;
  }
  const digest = createHash("md5").update(bytes).digest();
  return [digest.readUInt32BE(0), digest.readUInt32BE(4), digest.readUInt32BE(8), digest.readUInt32BE(12)];
}

class Parser {
  private index = 0;
  /** Exclusive token boundary used while parsing the operand of `(expr op)`. */
  private expressionStop = -1;
  /** `static e` bindings floated out of this module's expressions, in source
   * order - the order that fixes each one's fingerprint. */
  private readonly staticForms: ValueDeclaration[] = [];
  private moduleName = "Main";
  /** Declarations a single top-level declaration expanded into - the selectors
   * of a pattern binding - drained by the module loop after each one. */
  private readonly queued: Declaration[] = [];
  /** Record fields per constructor, for the module being parsed. A pattern
   * *binding* is split into selectors here, before any cross-module resolution
   * has happened, so `let C {..} = e` can only name what it binds from a
   * declaration this module has already read. That covers the wildcard
   * pattern bindings that exist (miso's `let ComponentState {..} = ...` sits
   * in the module that declares it); a wildcard over an imported constructor
   * still binds nothing, which is what it did for every constructor before. */
  readonly recordFieldsByCon = new Map<string, readonly string[]>();
  /** Set when a `{..}` pattern binding named a constructor this pass had not
   * read yet, so `parseModule` knows a second pass would bind more. */
  wildcardBindingUnresolved = false;
  constructor(
    private readonly tokens: Token[],
    private readonly file: string,
    private readonly diagnostics: Diagnostic[],
    /** Record fields carried over from a first parse of this same module. */
    private readonly seededFields: ReadonlyMap<string, readonly string[]> = new Map(),
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
      this.at(";")
    )
      this.take();
  }
  private acceptLayoutOpen() {
    return this.at("{") ? !!this.take() : false;
  }
  private acceptLayoutClose() {
    return this.at("}") ? !!this.take() : false;
  }
  /** A token *is* the given punctuation or keyword. A string or character
   * literal is not: `("," ++ xs)` holds a string whose text is a comma, and
   * matching it as the tuple separator turns a legal expression into a syntax
   * error. Only symbols and identifiers can be punctuation. */
  private at(text: string, offset = 0): boolean {
    const token = this.tokens[this.index + offset];
    return token !== undefined && token.text === text && (token.kind === "symbol" || token.kind === "ident");
  }
  private accept(text: string) {
    if (this.at(text)) {
      this.take();
      return true;
    }
    return false;
  }
  private acceptTypeSignature() {
    if (this.at("::")) {
      this.take();
      return true;
    }
    if (
      this.at(":") &&
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
    // No `module X where` header: the lexer still opens an implicit
    // top-level context around every declaration (the Haskell report's own
    // rule), so it must be entered here the same way the header branch below
    // enters its own `where`-opened one.
    if (!this.at("module")) {
      this.acceptLayoutOpen();
      this.skipLines();
    }
    if (this.at("module")) {
      this.take();
      name = this.take().text;
      this.moduleName = name;
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
      if (this.at("import")) {
        imports.push(this.importDeclaration());
        continue;
      }
      const declarationStart = this.index;
      const declaration = this.declaration();
      if (declaration) declarations.push(declaration, ...this.queued.splice(0));
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
      // The floated `static` bindings belong to this module, so they are
      // renamed and scoped with it (see src/modules.ts) - which is what keeps
      // the closed expression's names resolving where they were written.
      declarations: [...declarations, ...this.staticForms],
    };
  }
  private importDeclaration(): ImportDeclaration {
    const start = this.take().span;
    const qualified = this.accept("qualified");
    const imported = this.take().text;
    let alias: string | undefined;
    if (this.accept("as")) alias = this.take().text;
    const hiding = this.accept("hiding");
    const names = this.at("(") ? this.importNames() : undefined;
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
          this.at("(") &&
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
      this.at("makeLenses") &&
      this.tokens[this.index + 1]?.text === "''"
    ) {
      const start = this.take().span;
      this.take();
      const argument = this.take().text;
      this.skipLines();
      return { tag: "splice", name: "makeLenses", argument, span: start };
    }
    if (this.at("data") || this.at("newtype"))
      return this.data();
    if (this.at("type")) {
      const start = this.take().span;
      const name = this.take().text;
      const parameters: string[] = [];
      while (this.current().kind === "ident" && !this.at("="))
        parameters.push(this.take().text);
      this.expect("=");
      const target: string[] = [];
      while (
        !this.at(";") &&
        !this.at("}") &&
        this.current().kind !== "eof"
      )
        // `type Foo = "foo"`: a type-level string literal is spelled with its
        // quotes everywhere else a type is written, and `KnownSymbol` solving
        // keys on them (see `elaborate.ts`). Taking `.text` here dropped them,
        // so the synonym expanded to a bare `foo` no symbol could match.
        target.push(tokenSpelling(this.take()));
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
        !this.at(";") &&
        !this.at("}") &&
        this.current().kind !== "eof"
      )
        this.take();
      this.skipLines();
      return undefined;
    }
    if (this.at("class")) return this.classDeclaration();
    if (this.at("instance")) return this.instanceDeclaration();
    if (this.at("foreign")) return this.foreign();
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
          !this.at(";") &&
          !this.at("}") &&
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
    // A top-level tuple pattern binding is valid (`(x, y) = action`).
    if (this.at("(")) {
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
        const [first, ...rest] = this.patternBindingParts(pattern, value, start);
        const declaration = (part: { name: string; body: Expr }): ValueDeclaration => ({
          tag: "value",
          name: part.name,
          equations: [{ patterns: [], guards: [{ body: part.body }], whereBindings: [] }],
          span: start,
        });
        this.queued.push(...rest.map(declaration));
        return declaration(first!);
      }
    }
    if (
      this.current().kind !== "ident" &&
      this.current().kind !== "symbol" &&
      !this.at("(")
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
        !this.at(";") &&
        !this.at("}") &&
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
          const qualifiers = this.guard();
          this.expect("=");
          guards.push({ qualifiers, body: this.expression() });
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
  /** A type or data constructor name, which may be an operator in parentheses:
   * `data (:*:) f g p = (:*:) (f p) (g p)` declares both. */
  private conName(): string {
    if (this.at("(") && /^:/.test(this.tokens[this.index + 1]?.text ?? "") && this.tokens[this.index + 2]?.text === ")") {
      this.take();
      const operator = this.take().text;
      this.take();
      return operator;
    }
    return this.take().text;
  }
  private data(): DataDeclaration {
    const isNewtype = this.at("newtype");
    const start = this.take().span;
    const name = this.conName();
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
      //
      // A *kinded* binder is written parenthesised - `(path :: Symbol)` - and
      // the variable it binds is as much a parameter as a bare one. Counting
      // only the bare spelling gave `newtype Path (path :: Symbol)` arity 0,
      // so `Path "users"` in a signature and the `Path` an instance was
      // derived for were different types, and the arity showed up as
      // "guarded bodies have different types" a phase later.
      const binder =
        headerDepth === 0
          ? token
          : headerDepth === 1 && this.tokens[this.index - 1]?.text === "(" && this.tokens[this.index + 1]?.text === "::"
            ? token
            : undefined;
      if (binder && binder.kind === "ident" && /^[a-z]/.test(binder.text)) parameters.push(binder.text);
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
      if (this.at("forall")) {
        this.take();
        // The lexer keeps qualified identifiers intact and consequently also
        // represents `result.` (the common no-space forall spelling) as one
        // token. Accept either spelling of the quantifier terminator.
        while (this.current().kind !== "eof") {
          const variable = this.take();
          if (variable.text === "." || variable.text.endsWith(".")) break;
        }
      }
      // A constructor's context is not decoration: each constraint becomes a
      // dictionary field of the constructor, so the spelling is kept rather
      // than skipped.  `probe` lands on the `=>` if there is one.
      let context: string[] | undefined;
      let probe = this.index;
      if (this.at("(")) {
        let depth = 0;
        do {
          const token = this.tokens[probe++];
          if (token?.text === "(") depth++;
          else if (token?.text === ")") depth--;
        } while (depth > 0 && probe < this.tokens.length);
      } else {
        while (
          probe < this.tokens.length &&
          !["=>", "|", ";", "deriving"].includes(this.tokens[probe]?.text ?? "")
        )
          probe++;
      }
      if (this.tokens[probe]?.text === "=>") {
        const spelling: string[] = [];
        while (this.index < probe) spelling.push(this.take().text);
        this.take();
        context = splitConstraints(spelling);
      }
      const constructor = this.conName();
      let arity = 0;
      let fields: string[] | undefined;
      let fieldTypes: string[] | undefined;
      if (this.accept("{")) {
        fields = [];
        fieldTypes = [];
        while (!this.at("}") && this.current().kind !== "eof") {
          // `deltaX, deltaY :: Double` declares two fields of one type, and
          // miso's records use the form freely. Read every name up to the
          // `::`, then give the one type that follows to all of them.
          const group: string[] = [];
          while (this.current().kind !== "eof" && !this.at("}")) {
            const field = this.take();
            if (field.kind === "ident") group.push(field.text);
            if (!this.accept(",")) break;
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
          for (const name of group) {
            fields.push(name);
            fieldTypes.push(type.join(" "));
            arity++;
          }
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
          !this.at("|") &&
          !this.at("deriving") &&
          !this.at(";") &&
          !(this.at("}") && this.current().virtual)
        ) {
          if (this.at("!")) {
            this.take();
            continue;
          }
          if (this.at("(") || this.at("[")) {
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
      constructors.push({ name: constructor, arity, fields, fieldTypes, context });
      if (fields) this.recordFieldsByCon.set(constructor, fields);
    } while (this.accept("|"));
    // The three GHC deriving strategies build three different instances, so
    // they are kept apart: `stock` (and a strategy-less clause) is the one the
    // compiler writes, `anyclass` is an empty instance, `newtype` lifts the
    // wrapped type's.
    const deriving: string[] = [];
    const derivingAnyclass: string[] = [];
    const derivingNewtype: string[] = [];
    let bucket: string[] | undefined;
    while (
      !this.at(";") &&
      !(this.at("}") && this.current().virtual) &&
      this.current().kind !== "eof"
    ) {
      const token = this.take();
      if (token.text === "deriving") {
        const strategy = this.current().text;
        bucket =
          strategy === "anyclass" ? derivingAnyclass : strategy === "newtype" ? derivingNewtype : deriving;
        if (strategy === "anyclass" || strategy === "newtype" || strategy === "stock") this.take();
        continue;
      }
      if (bucket && token.kind === "ident" && /^[A-Z]/.test(token.text))
        bucket.push(token.text);
    }
    this.skipLines();
    return {
      tag: "data",
      name,
      parameters: [...new Set(parameters)],
      constructors,
      deriving: [...new Set(deriving)],
      ...(derivingAnyclass.length ? { derivingAnyclass: [...new Set(derivingAnyclass)] } : {}),
      ...(derivingNewtype.length ? { derivingNewtype: [...new Set(derivingNewtype)] } : {}),
      ...(isNewtype ? { newtype: true } : {}),
      span: start,
    };
  }
  private foreign():
    | import("./ast.js").ForeignDeclaration
    | import("./ast.js").UnsupportedDeclaration {
    const start = this.take().span;
    if (!this.accept("import")) {
      while (!this.at(";") && this.current().kind !== "eof")
        this.take();
      this.skipLines();
      return { tag: "unsupported", feature: "foreign export", span: start };
    }
    const callingConvention = this.take();
    if (!["javascript", "ccall", "capi", "prim"].includes(callingConvention.text)) {
      while (
        !this.at(";") &&
        !this.at("}") &&
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
    // GHC's JS backend gives a C symbol its JavaScript name by prefixing `h$`
    // (`GHC.StgToJS.FFI`), so a `foreign import ccall "miso_x_store"` is the
    // function `h$miso_x_store` - which is exactly the shape GHC 9.12 wants
    // from a `javascript` import string too. Whether that function exists is
    // the linker's business, as it is for `javascript`.
    const isC = callingConvention.text !== "javascript";
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
      !this.at(";") &&
      !this.at("}") &&
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
    const arity = Math.max(0, signature.length - 1);
    return {
      tag: "foreign",
      name: name.text,
      javascript: isC ? `h$${javascript.text}` : javascript.text,
      signature,
      arity,
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
    const afterContext = arrow < 0 ? header : header.slice(arrow + 1);
    // `class MonadState s m | m -> s where`: everything after the bar is the
    // functional dependencies, and only what precedes it names parameters.
    const bar = afterContext.findIndex((token) => token.text === "|");
    const rest = bar < 0 ? afterContext : afterContext.slice(0, bar);
    // The class name is the *first* uppercase identifier, not the last: a
    // kind-annotated parameter such as `class GToFields (f :: Type -> Type)`
    // puts `Type` after it, and taking the last one named the class `Type`
    // with no parameters at all.
    const classIndex = rest.findIndex(
      (token) => token.kind === "ident" && /^[A-Z]/.test(token.text),
    );
    const name = classIndex < 0 ? "<anonymous class>" : rest[classIndex]!.text;
    // Each parameter is one lowercase identifier, but a kind signature adds
    // more after `::` that name kinds rather than parameters - so within a
    // parenthesised group only the first identifier is the parameter.
    const parameters: string[] = [];
    let depth = 0;
    let takenInGroup = false;
    for (const token of rest.slice(classIndex + 1)) {
      if (token.text === "(") {
        depth++;
        takenInGroup = false;
        continue;
      }
      if (token.text === ")") {
        depth = Math.max(0, depth - 1);
        continue;
      }
      if (token.kind !== "ident" || !/^[a-z]/.test(token.text)) continue;
      if (depth > 0) {
        if (takenInGroup) continue;
        takenInGroup = true;
      }
      parameters.push(token.text);
    }
    const fundeps =
      bar < 0
        ? []
        : afterContext
            .slice(bar + 1)
            .map((token) => token.text)
            .join(" ")
            .split(",")
            .flatMap((item) => {
              const sides = item.split("->");
              if (sides.length !== 2) return [];
              const names = (side: string): string[] =>
                side.split(/\s+/).filter((word) => /^[a-z][A-Za-z0-9_']*$/.test(word));
              return [{ from: names(sides[0]!), to: names(sides[1]!) }];
            });
    const body = this.membersAfterWhere();
    return {
      tag: "class",
      name,
      associatedTypes: body.associated,
      context,
      parameters: [...new Set(parameters)],
      fundeps,
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
      associatedTypes: body.associated,
      members: body.members,
      rawMembers: body.rawMembers,
      span: start,
    };
  }
  private membersAfterWhere(): {
    members: Declaration[];
    rawMembers: import("./ast.js").ClassMemberSlice[];
    associated: import("./ast.js").AssociatedType[];
  } {
    if (!this.accept("where")) {
      this.skipLines();
      return { members: [], rawMembers: [], associated: [] };
    }
    this.skipLines();
    if (!this.acceptLayoutOpen()) {
      this.lineEnd();
      return { members: [], rawMembers: [], associated: [] };
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
    const associated: import("./ast.js").AssociatedType[] = [];
    const finish = () => {
      if (!segment.length) return;
      // An associated type is neither a method signature nor an equation:
      // `type family Index at :: Type` in a class body, `type Index (Map k v)
      // = k` in an instance's. Read as a member it invented a method called
      // `type` that every instance was then missing.
      if (segment[0]!.text === "type") {
        const head = segment[1]?.text === "family" ? segment.slice(2) : segment.slice(1);
        const name = head[0]?.text;
        const equals = head.findIndex((t) => t.text === "=");
        if (name && /^[A-Z]/.test(name)) {
          associated.push({
            name,
            ...(equals > 0
              ? { rhs: head.slice(equals + 1).map((t) => t.text).join(" ") }
              : {}),
          });
          segment = [];
          return;
        }
      }
      rawMembers.push({
        tokens: segment.map(tokenSpelling),
        span: segment[0].span,
      });
      // GHC's DefaultSignatures: `default f :: ty` gives the class's *default
      // implementation* of `f` its own, more constrained type. Reading the
      // `default` keyword as the binder's name loses that type and, worse,
      // invents a method called `default` that every instance is then missing.
      const isDefault = segment[0]?.text === "default" && segment[1]?.kind === "ident";
      const head = isDefault ? segment.slice(1) : segment;
      const signatureAt = head.findIndex((token) => token.text === "::");
      if (signatureAt > 0) {
        const candidate =
          head[0].text === "(" && head[2]?.text === ")" ? head[1]?.text : head[0].text;
        const typeStart = signatureAt + 1;
        if (candidate && typeStart < head.length)
          members.push({
            tag: "signature",
            name: candidate,
            type: head
              .slice(typeStart)
              .map((token) => token.text)
              .join(" "),
            ...(isDefault ? { isDefault: true as const } : {}),
            span: head[0].span,
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
    return { members, rawMembers, associated };
  }
  private lineEnd() {
    while (
      this.current().kind !== "newline" &&
      !this.at(";") &&
      !this.at("}") &&
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
    // `::` binds looser than every operator, so an ascription is only taken at
    // the outermost call - otherwise `a + b :: T` would ascribe `b`.
    if (min === -1 && this.acceptTypeSignature()) {
      const type = this.typeAnnotation();
      if (type) return { tag: "annot", expr: left, type, span: left.span };
    }
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
      this.at("`") &&
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
    if (this.at("`")) {
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
    if (!this.at("-")) return undefined;
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
    value = this.visibleTypeApplications(value);
    while (this.startsAtom()) {
      const arg = this.recordUpdates(this.atom());
      value = { tag: "app", fn: value, arg, span: value.span };
      value = this.visibleTypeApplications(value);
    }
    return value;
  }
  private recordUpdates(base: Expr): Expr {
    while (
      this.current().kind === "symbol" &&
      this.at("{") &&
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
  /** `e @T @U`, in an *expression*.  The `@` of an as-pattern is never seen
   * here: patterns are parsed by `pattern()`, and this runs only between the
   * atoms of an application, where a bare `@` can only be a type argument.
   *
   * Each argument is kept as source text and re-lexed by `src/elaborate.ts`,
   * the way `annot` already is; the outermost wrapper is the *last* written
   * argument, so the elaborator peels the chain to recover the written order. */
  private visibleTypeApplications(value: Expr): Expr {
    while (this.at("@")) {
      this.take();
      // A promoted constructor, `@'Just`: the tick is not part of the name.
      if (this.at("'")) this.take();
      const open = this.current().text;
      if (open === "(" || open === "[") {
        const close = open === "(" ? ")" : "]";
        const parts: string[] = [];
        this.take();
        let depth = 1;
        while (depth && this.current().kind !== "eof") {
          if (this.current().text === open) depth++;
          else if (this.current().text === close) depth--;
          const token = this.take();
          if (depth) parts.push(tokenSpelling(token));
        }
        // `@[a]` is a list type; `@(...)` is only grouping, so its brackets
        // are dropped and the list's are kept.
        const text = open === "[" ? `[ ${parts.join(" ")} ]` : parts.join(" ");
        value = { tag: "typeApp", expr: value, type: text, span: value.span };
        continue;
      }
      // `@"users"` is a type-level string. `tokenSpelling` re-quotes it: the
      // lexer hands back the *decoded* value, and `Path users` would read back
      // as a type variable rather than the symbol it is.
      if (this.current().kind === "ident" || this.current().kind === "string")
        value = { tag: "typeApp", expr: value, type: tokenSpelling(this.take()), span: value.span };
    }
    return value;
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
  /** `static e` becomes a reference to a fresh top-level `StaticPtr` binding.
   *
   * Floating it out is not tidiness: the pointer must be *one* value with one
   * identity, and an inline `StaticPtr key e` inside a function would allocate
   * a fresh one on every call, so the table would hold whichever copy was
   * registered last while `deRefStaticPtr` handed back another. */
  private floatStaticForm(body: Expr, span: Span): Expr {
    const name = `$static${this.staticForms.length}`;
    const [k1, k2, k3, k4] = staticPtrFingerprint("main", this.moduleName, this.staticForms.length);
    // `Fingerprint` is two `Word64` halves and `word64FromHalves` takes the
    // two 32-bit words `md5` produced for each, so the four numbers reach the
    // key in the same order and mean the same bits they always did. They are
    // `IntPrim` arguments, so the literals stay raw machine integers rather
    // than being boxed and re-read.
    const half = (hi: number, lo: number): Expr =>
      [hi, lo].reduce<Expr>(
        (fn, value) => ({ tag: "app", fn, arg: { tag: "int", value, span }, span }),
        { tag: "var", name: "word64FromHalves", span },
      );
    const key: Expr = {
      tag: "app",
      fn: { tag: "app", fn: { tag: "var", name: "Fingerprint", span }, arg: half(k1, k2), span },
      arg: half(k3, k4),
      span,
    };
    const ptr: Expr = {
      tag: "app",
      fn: { tag: "app", fn: { tag: "var", name: "StaticPtr", span }, arg: key, span },
      arg: body,
      span,
    };
    this.staticForms.push({
      tag: "value",
      name,
      sptFingerprint: [k1, k2, k3, k4],
      equations: [{ patterns: [], guards: [{ body: ptr }], whereBindings: [] }],
      span,
    });
    return { tag: "var", name, span };
  }
  private atom(): Expr {
    const t = this.take();
    if (t.kind === "int")
      return { tag: "int", value: Number(t.text), span: t.span };
    if (t.kind === "float")
      return { tag: "double", value: Number(t.text), span: t.span };
    if (t.kind === "char") return { tag: "char", value: t.text, span: t.span };
    if (t.kind === "string")
      return { tag: "string", value: t.text, span: t.span };
    if (t.kind === "quasiquote")
      return { tag: "jsQuote", body: t.text, quoter: t.quoter, span: t.span };
    // `static aexp`, the StaticPointers form. GHC floats each one to its own
    // top-level binding before the body is ever looked at, and so does this:
    // the fingerprint is the *position* of the form, so it must be fixed here,
    // where the source order is, and not by anything downstream.
    if (t.kind === "ident" && t.text === "static" && this.startsAtom())
      return this.floatStaticForm(this.recordUpdates(this.atom()), t.span);
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
        !this.at("where") &&
        !this.at("}")
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
              !this.at("<-") &&
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
      if (this.at("case")) {
        this.take();
        return {
          tag: "lambdaCase",
          alternatives: this.caseAlternatives(t),
          span: t.span,
        };
      }
      const parameters: import("./ast.js").Pattern[] = [];
      while (!this.at("->") && this.current().kind !== "eof")
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
      if (this.at(",")) {
        let commas = 0;
        while (this.accept(",")) commas++;
        this.expect(")");
        return { tag: "var", name: `(${",".repeat(commas)})`, span: t.span };
      }
      if (this.at("-")) {
        const saved = this.index;
        this.take();
        if (this.startsAtom()) {
          const operand = this.recordUpdates(this.atom());
          if (this.at(")")) {
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
        !this.at("-") &&
        !this.at("\\") &&
        !this.at("`") &&
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
        this.at("`") &&
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
        while (!this.at(")") && this.current().kind !== "eof")
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
    // Literals first: a string pattern may *contain* punctuation, and `"("` is
    // a pattern matching one character, not an open parenthesis.
    if (token.kind === "int") return { tag: "int", value: Number(token.text), span: token.span };
    if (token.kind === "float") return { tag: "double", value: Number(token.text), span: token.span };
    if (token.kind === "char") return { tag: "char", value: token.text, span: token.span };
    if (token.kind === "string") return { tag: "string", value: token.text, span: token.span };
    if (token.text === "!") return this.pattern();
    if (token.text === "(") {
      if (this.accept(")"))
        return { tag: "con", name: "()", args: [], span: token.span };
      let left = this.pattern();
      // `(comp_ :: Component context props model action)` is not decoration:
      // the variables it writes scope over the body, and a later
      // `fromJSON m :: Result model` names *that* `model`. Kept for `wild` and
      // `var`, the two shapes a signature can usefully bind through.
      if (this.acceptTypeSignature()) {
        const annotation = this.typeAnnotation();
        if (left.tag === "wild" || left.tag === "var") left = { ...left, signature: annotation };
      }
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
      // Any constructor operator, not only `:`: `GHC.Generics` matches
      // `(x :*: y)`, and a constructor written infix binds exactly as the
      // prefix `(:*:) x y` it stands for.
      if (this.current().kind === "symbol" && /^:.+/.test(this.current().text)) {
        const operator = this.take().text;
        const right = this.pattern();
        this.expect(")");
        return { tag: "con", name: operator, args: [left, right], span: token.span };
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
          while (this.current().kind !== "eof" && !this.at("}")) {
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
    while (!this.at("}") && this.current().kind !== "eof") {
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
  /** The tokens of a type annotation, as source text. Joined with spaces: the
   * type parser re-lexes, so only token boundaries matter. */
  private typeAnnotation(): string {
    const parts: string[] = [];
    let depth = 0;
    while (this.current().kind !== "eof") {
      const token = this.current();
      if (token.text === "(" || token.text === "[") {
        depth++;
        parts.push(this.take().text);
        continue;
      }
      if (token.text === ")" || token.text === "]") {
        if (!depth) return parts.join(" ");
        depth--;
        parts.push(this.take().text);
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
        return parts.join(" ");
      parts.push(tokenSpelling(this.take()));
    }
    return parts.join(" ");
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
          while (this.current().kind !== "eof" && !this.at("}")) {
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
        if (this.at("{") && this.current().virtual) depth++;
        else if (this.at("}") && this.current().virtual) depth--;
        this.take();
      }
    } else this.skipLines();
    return { tag: "unsupported", feature, span: start };
  }
  private patternBinders(p: Pattern, into: string[]): void {
    switch (p.tag) {
      case "var":
        into.push(p.name);
        return;
      case "as":
        into.push(p.name);
        this.patternBinders(p.pattern, into);
        return;
      case "con":
        for (const arg of p.args) this.patternBinders(arg, into);
        return;
      case "record": {
        for (const field of p.fields) this.patternBinders(field.pattern, into);
        // `C {..}` also binds every field the pattern did not write, under the
        // field's own name.
        if (p.wildcard) {
          const written = new Set(p.fields.map((f) => f.name));
          const known = this.recordFieldsByCon.get(p.name) ?? this.seededFields.get(p.name);
          if (known === undefined) this.wildcardBindingUnresolved = true;
          for (const field of known ?? []) if (!written.has(field)) into.push(field);
        }
        return;
      }
      default:
        return;
    }
  }

  /** GHC's pattern-binding desugaring: `p = e` becomes one binding for `e`
   * plus one *selector* per variable `p` binds, each `case e' of p -> v`.
   *
   * The shape is what makes it lazy, and laziness is the whole point: miso's
   * `(mts, bts, web) = unsafePerformIO FFI.getThreads` is a top-level binding
   * whose right-hand side must not run until one of the three is demanded, and
   * `let (_, remaining) = S.spanl ...` must not force the pair when the other
   * branch is taken.  Matching the pattern eagerly at the binding site would
   * be a different program. */
  private patternBindingParts(
    pattern: Pattern,
    value: Expr,
    span: Span,
  ): Array<{ name: string; body: Expr }> {
    const scrutinee = `__pattern_${span.start}`;
    const binders: string[] = [];
    this.patternBinders(pattern, binders);
    return [
      { name: scrutinee, body: value },
      ...binders.map((name) => ({
        name,
        body: {
          tag: "case" as const,
          subject: { tag: "var" as const, name: scrutinee, span },
          alternatives: [
            { pattern, body: { tag: "var" as const, name, span } },
          ],
          span,
        },
      })),
    ];
  }

  private localBindings(
    terminator?: string,
  ): import("./ast.js").LocalBinding[] {
    this.skipLines();
    this.acceptLayoutOpen();
    const bindings: import("./ast.js").LocalBinding[] = [];
    const signatures = new Map<string, string>();
    while (
      this.startsPattern() &&
      this.current().text !== terminator &&
      !this.at("}")
    ) {
      // BangPatterns: `let !x = e`. Read as a binder named `!` with `x` for a
      // parameter, this used to leave `x` unbound at every use.
      const strict = this.at("!") && this.tokens[this.index + 1]?.kind === "ident" ? (this.take(), true) : false;
      if (this.at("(") || this.at("[")) {
        const start = this.current().span;
        const pattern = this.pattern();
        this.expect("=");
        const value = this.expression();
        for (const part of this.patternBindingParts(pattern, value, start))
          bindings.push({
            name: part.name,
            patterns: [],
            value: part.body,
            guards: [{ body: part.body }],
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
        for (const part of this.patternBindingParts(pattern, value, name.span))
          bindings.push({
            name: part.name,
            patterns: [],
            value: part.body,
            guards: [{ body: part.body }],
            span: name.span,
          });
        this.skipLines();
        continue;
      }
      if (this.acceptTypeSignature()) {
        // A local signature is kept, not skipped. `src/elaborate.ts` checks the
        // binding against it, which is what ties a `where` helper's variables
        // to the enclosing signature's - miso's `Miso.Runtime` reads a global
        // `IORef` whose own type variables are universally quantified, and only
        // the local signature says which types the read is at.
        const parts: string[] = [];
        while (
          !this.at(";") &&
          !this.at("}") &&
          this.current().kind !== "eof"
        )
          parts.push(tokenSpelling(this.take()));
        signatures.set(name.text, parts.join(" "));
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
          const qualifiers = this.guard();
          this.expect("=");
          guards.push({ qualifiers, body: this.expression() });
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
        ...(strict && patterns.length === 0 ? { strict: true as const } : {}),
        span: name.span,
      });
      this.skipLines();
    }
    this.acceptLayoutClose();
    // A signature may be written above or below the equations it belongs to,
    // so they are matched by name once the whole group is read.
    for (const binding of bindings) {
      const signature = signatures.get(binding.name);
      if (signature !== undefined) binding.signature = signature;
    }
    return bindings;
  }
  /** The qualifiers of one `|` guard: comma-separated, evaluated left to
   * right, each a boolean or a `p <- e` whose bindings are in scope for every
   * qualifier to its right and for the body.  `Right x <- a, Just y <- f x` is
   * two of them, and reading only the first loses `x`. */
  private guard(): import("./ast.js").GuardQualifier[] {
    const qualifiers: import("./ast.js").GuardQualifier[] = [];
    do {
      if (this.hasPatternGuard()) {
        const pattern = this.pattern();
        this.expect("<-");
        qualifiers.push({ tag: "pattern", pattern, source: this.expression() });
      } else qualifiers.push({ tag: "bool", condition: this.expression() });
    } while (this.accept(","));
    return qualifiers;
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
      // A `;` or `}` at depth zero ends this statement, written or virtual.
      // An instance method is re-lexed from tokens whose virtual punctuation
      // has already been printed as ordinary `{`/`;`/`}` (see
      // `instanceMethodValues` in `src/dictionary.ts`), so requiring the
      // virtual flag let the scan run on into the *next* statement and read
      // its `<-` as this one's. `instance FromJSVal Closed` in miso's
      // `Miso.Runtime` failed to parse for exactly that reason, and a method
      // that fails to parse is silently dropped - the instance then took the
      // class's `Generic` default instead of the body it was given.
      if (!delimiters && (token.text === ";" || token.text === "}")) return false;
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
      !this.at("}")
    ) {
      let pattern = this.pattern();
      while (this.accept(":"))
        pattern = {
          tag: "con",
          name: ":",
          args: [pattern, this.pattern()],
          span: pattern.span,
        };
      const addGuardedBody = (qualifiers?: import("./ast.js").GuardQualifier[]) => {
        this.expect("->");
        const result = this.expression();
        const bindings = this.accept("where") ? this.localBindings() : [];
        alternatives.push({
          pattern,
          qualifiers,
          body: bindings.length
            ? { tag: "let", bindings, body: result, span: result.span }
            : result,
        });
        this.skipLines();
      };
      if (this.accept("|")) {
        do addGuardedBody(this.guard());
        while (this.accept("|"));
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
