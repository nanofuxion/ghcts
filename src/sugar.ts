/** Purely syntactic desugarings that need the module's data declarations but
 * no types at all: `do` notation, record construction/update/patterns, record
 * field selectors and `deriving Eq`.
 *
 * Everything here produces ordinary surface AST, so `src/elaborate.ts` only
 * ever sees `>>=`, `pure` and plain constructor applications; it does not have
 * to know these forms exist, and neither does `src/desugar.ts`.
 *
 * `do` is expanded here rather than in the elaborator because the expansion is
 * type-independent: which `>>=` runs is settled later, by the same instance
 * selection every other class method goes through.
 */
import type {
  CaseAlternative,
  DataDeclaration,
  DoStatement,
  Expr,
  Guard,
  ListQualifier,
  LocalBinding,
  Pattern,
  Span,
  ValueDeclaration,
} from "./ast.js";

export interface ConInfo {
  name: string;
  arity: number;
  fields?: string[];
  typeName: string;
}

export type ConTable = ReadonlyMap<string, ConInfo>;
export type Report = (message: string, span: Span) => void;

export function constructorTable(datas: readonly DataDeclaration[]): ConTable {
  const table = new Map<string, ConInfo>();
  for (const decl of datas) {
    for (const con of decl.constructors) {
      table.set(con.name, { name: con.name, arity: con.arity, fields: con.fields, typeName: decl.name });
    }
  }
  return table;
}

const variable = (name: string, span: Span): Expr => ({ tag: "var", name, span });
const apply2 = (fn: string, a: Expr, b: Expr, span: Span): Expr => ({
  tag: "app",
  fn: { tag: "app", fn: variable(fn, span), arg: a, span },
  arg: b,
  span,
});
const applyAll = (fn: Expr, args: Expr[]): Expr =>
  args.reduce((acc, arg) => ({ tag: "app", fn: acc, arg, span: acc.span }), fn);

class Sugar {
  private counter = 0;
  constructor(
    private readonly cons: ConTable,
    private readonly report: Report,
  ) {}

  private fresh(prefix: string): string {
    return `$${prefix}${this.counter++}`;
  }

  decl(decl: ValueDeclaration): ValueDeclaration {
    return {
      ...decl,
      equations: decl.equations.map((equation) => ({
        patterns: equation.patterns.map((p) => this.pattern(p)),
        guards: equation.guards.map((g) => this.guard(g)),
        whereBindings: equation.whereBindings.map((b) => this.local(b)),
      })),
    };
  }

  private guard(g: Guard): Guard {
    return {
      ...g,
      condition: g.condition ? this.expr(g.condition) : undefined,
      pattern: g.pattern ? this.pattern(g.pattern) : undefined,
      source: g.source ? this.expr(g.source) : undefined,
      body: this.expr(g.body),
    };
  }

  private local(b: LocalBinding): LocalBinding {
    return {
      ...b,
      patterns: b.patterns.map((p) => this.pattern(p)),
      value: this.expr(b.value),
      guards: b.guards?.map((g) => this.guard(g)),
      whereBindings: b.whereBindings?.map((w) => this.local(w)),
    };
  }

  private alt(a: CaseAlternative): CaseAlternative {
    return {
      ...a,
      pattern: this.pattern(a.pattern),
      guard: a.guard ? this.expr(a.guard) : undefined,
      body: this.expr(a.body),
    };
  }

  /** `Con { a = p }` and `Con {..}` become the ordinary positional pattern;
   * a wildcard binds each unmentioned field to a variable of its own name,
   * which is exactly what `RecordWildCards` means. */
  pattern(p: Pattern): Pattern {
    switch (p.tag) {
      case "as":
        return { ...p, pattern: this.pattern(p.pattern) };
      case "con":
        return { ...p, args: p.args.map((arg) => this.pattern(arg)) };
      case "record": {
        const info = this.cons.get(p.name);
        if (!info?.fields) {
          this.report(`\`${p.name}\` has no record fields`, p.span);
          return { tag: "wild", span: p.span };
        }
        const given = new Map(p.fields.map((f) => [f.name, this.pattern(f.pattern)]));
        const args = info.fields.map((field): Pattern => {
          const bound = given.get(field);
          if (bound) return bound;
          return p.wildcard ? { tag: "var", name: field, span: p.span } : { tag: "wild", span: p.span };
        });
        return { tag: "con", name: p.name, args, span: p.span };
      }
      default:
        return p;
    }
  }

  expr(e: Expr): Expr {
    switch (e.tag) {
      case "app":
        return { ...e, fn: this.expr(e.fn), arg: this.expr(e.arg) };
      case "lambda":
        return { ...e, body: this.expr(e.body) };
      case "lambdaCase":
        return { ...e, alternatives: e.alternatives.map((a) => this.alt(a)) };
      case "if":
        return {
          ...e,
          condition: this.expr(e.condition),
          thenBranch: this.expr(e.thenBranch),
          elseBranch: this.expr(e.elseBranch),
        };
      case "case":
        return { ...e, subject: this.expr(e.subject), alternatives: e.alternatives.map((a) => this.alt(a)) };
      case "let":
        return { ...e, bindings: e.bindings.map((b) => this.local(b)), body: this.expr(e.body) };
      case "tuple":
      case "list":
        return { ...e, items: e.items.map((item) => this.expr(item)) };
      case "do":
        return this.doBlock(e.statements, e.span);
      case "listComp":
        return this.comprehension(e.body, e.qualifiers, e.span);
      case "record":
        return this.construct(e);
      case "recordUpdate":
        return this.update(e);
      default:
        return e;
    }
  }

  private doBlock(statements: readonly DoStatement[], span: Span): Expr {
    const head = statements[0];
    if (!head) {
      this.report("empty `do` block", span);
      return variable("$emptyDo", span);
    }
    const rest = statements.slice(1);
    if (rest.length === 0) {
      if (head.tag !== "expr") {
        this.report("the last statement in a `do` block must be an expression", span);
        return variable("$badDo", span);
      }
      return this.expr(head.expr);
    }
    const tail = this.doBlock(rest, span);
    if (head.tag === "let") return { tag: "let", bindings: head.bindings.map((b) => this.local(b)), body: tail, span };
    if (head.tag === "expr") return apply2(">>", this.expr(head.expr), tail, span);
    // A refutable binder cannot fall through to `fail` here - there is no
    // MonadFail - so it becomes a `case` whose non-match raises, which is what
    // the pattern-match compiler already emits for every other partial match.
    const pattern = this.pattern(head.pattern);
    const name = pattern.tag === "var" ? pattern.name : this.fresh("bind");
    const body: Expr =
      pattern.tag === "var" || pattern.tag === "wild"
        ? tail
        : { tag: "case", subject: variable(name, span), alternatives: [{ pattern, body: tail }], span };
    return apply2(">>=", this.expr(head.source), { tag: "lambda", parameter: name, body, span }, span);
  }

  /** The report's own translation:
   *
   *   [e | ]          = [e]
   *   [e | b, Q]      = if b then [e | Q] else []
   *   [e | p <- l, Q] = concatMap (\p -> [e | Q]) l
   *
   * A *refutable* generator pattern skips the elements it does not match, so
   * it becomes a two-alternative `\case` rather than a lambda - dropping that
   * would turn `[x | Just x <- xs]` into a pattern-match failure. */
  private comprehension(body: Expr, qualifiers: readonly ListQualifier[], span: Span): Expr {
    const nil: Expr = { tag: "list", items: [], span };
    const head = qualifiers[0];
    if (!head) return { tag: "list", items: [this.expr(body)], span };
    const tail = this.comprehension(body, qualifiers.slice(1), span);
    if (head.tag === "guard")
      return { tag: "if", condition: this.expr(head.condition), thenBranch: tail, elseBranch: nil, span };
    const pattern = this.pattern(head.pattern);
    const step: Expr =
      pattern.tag === "var"
        ? { tag: "lambda", parameter: pattern.name, body: tail, span }
        : pattern.tag === "wild"
          ? { tag: "lambda", parameter: this.fresh("lc"), body: tail, span }
          : {
              tag: "lambdaCase",
              alternatives: [
                { pattern, body: tail },
                { pattern: { tag: "wild", span }, body: nil },
              ],
              span,
            };
    return apply2("concatMap", step, this.expr(head.source), span);
  }

  private construct(e: Extract<Expr, { tag: "record" }>): Expr {
    const info = this.cons.get(e.constructor);
    if (!info?.fields) {
      this.report(`\`${e.constructor}\` has no record fields`, e.span);
      return variable(e.constructor, e.span);
    }
    const given = new Map(e.fields.map((f) => [f.name, this.expr(f.value)]));
    const args = info.fields.map((field) => {
      const value = given.get(field);
      if (value) return value;
      if (e.wildcard) return variable(field, e.span);
      this.report(`field \`${field}\` of \`${e.constructor}\` is missing`, e.span);
      return variable("$missingField", e.span);
    });
    return applyAll(variable(e.constructor, e.span), args);
  }

  /** `r { f = v }` scrutinises `r` and rebuilds every constructor that has all
   * the updated fields; one that does not is a match failure, exactly as in
   * GHC. */
  private update(e: Extract<Expr, { tag: "recordUpdate" }>): Expr {
    const updated = e.fields.map((f) => f.name);
    const candidates = [...this.cons.values()].filter(
      (info) => info.fields && updated.every((field) => info.fields!.includes(field)),
    );
    if (candidates.length === 0) {
      this.report(`no constructor has all of the fields ${updated.join(", ")}`, e.span);
      return this.expr(e.base);
    }
    const given = new Map(e.fields.map((f) => [f.name, this.expr(f.value)]));
    const alternatives = candidates.map((info): CaseAlternative => {
      const names = info.fields!.map((field) => `$u${field}`);
      return {
        pattern: {
          tag: "con",
          name: info.name,
          args: names.map((name): Pattern => ({ tag: "var", name, span: e.span })),
          span: e.span,
        },
        body: applyAll(
          variable(info.name, e.span),
          info.fields!.map((field, i) => given.get(field) ?? variable(names[i]!, e.span)),
        ),
      };
    });
    return { tag: "case", subject: this.expr(e.base), alternatives, span: e.span };
  }
}

export function expandSugar(decl: ValueDeclaration, cons: ConTable, report: Report): ValueDeclaration {
  return new Sugar(cons, report).decl(decl);
}

/** One selector per record field, as an ordinary multi-equation function: one
 * equation per constructor that has the field, so a selector on the wrong
 * constructor raises rather than reading a neighbouring slot. */
export function fieldSelectors(datas: readonly DataDeclaration[], taken: ReadonlySet<string>): ValueDeclaration[] {
  const equations = new Map<string, ValueDeclaration["equations"]>();
  for (const decl of datas) {
    for (const con of decl.constructors) {
      con.fields?.forEach((field, at) => {
        const args = con.fields!.map((_, i): Pattern =>
          i === at ? { tag: "var", name: "$field", span: decl.span } : { tag: "wild", span: decl.span },
        );
        const list = equations.get(field) ?? [];
        list.push({
          patterns: [{ tag: "con", name: con.name, args, span: decl.span }],
          guards: [{ body: variable("$field", decl.span) }],
          whereBindings: [],
        });
        equations.set(field, list);
      });
    }
  }
  return [...equations]
    .filter(([name]) => !taken.has(name))
    .map(([name, eqs]) => ({ tag: "value", name, equations: eqs, span: eqs[0]!.patterns[0]!.span }));
}

/** The `==` of a `deriving Eq` instance: constructors must agree, then every
 * field pair must, left to right. */
export function derivedEqMethod(decl: DataDeclaration): ValueDeclaration {
  const span = decl.span;
  const many = decl.constructors.length > 1;
  const alternatives = decl.constructors.map((con): CaseAlternative => {
    const xs = Array.from({ length: con.arity }, (_, i) => `$x${i}`);
    const ys = Array.from({ length: con.arity }, (_, i) => `$y${i}`);
    const conPattern = (names: string[]): Pattern => ({
      tag: "con",
      name: con.name,
      args: names.map((name): Pattern => ({ tag: "var", name, span })),
      span,
    });
    const inner = xs.reduceRight<Expr>(
      (rest, x, i) => ({
        tag: "if",
        condition: apply2("==", variable(x, span), variable(ys[i]!, span), span),
        thenBranch: rest,
        elseBranch: variable("False", span),
        span,
      }),
      variable("True", span),
    );
    const branches: CaseAlternative[] = [{ pattern: conPattern(ys), body: inner }];
    if (many) branches.push({ pattern: { tag: "wild", span }, body: variable("False", span) });
    return {
      pattern: conPattern(xs),
      body: { tag: "case", subject: variable("$b", span), alternatives: branches, span },
    };
  });
  return {
    tag: "value",
    name: "==",
    equations: [
      {
        patterns: [
          { tag: "var", name: "$a", span },
          { tag: "var", name: "$b", span },
        ],
        guards: [
          {
            body: { tag: "case", subject: variable("$a", span), alternatives, span },
          },
        ],
        whereBindings: [],
      },
    ],
    span,
  };
}
