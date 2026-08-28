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
  GuardQualifier,
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

  /** Can this pattern fail to match?  GHC asks exactly this before deciding
   * that a `do` bind needs `MonadFail`: `(a, b) <- m` and `Model n <- m` match
   * whatever they are given, so requiring `MonadFail` for them would reject
   * programs GHC accepts.  A constructor this pass has never seen - a list
   * cell, a literal - is refutable, which is the safe direction. */
  private refutable(pattern: Pattern): boolean {
    switch (pattern.tag) {
      case "wild":
      case "var":
        return false;
      case "as":
        return this.refutable(pattern.pattern);
      case "con":
        return this.soleConstructor(pattern.name)
          ? pattern.args.some((a) => this.refutable(a))
          : true;
      case "record":
        return this.soleConstructor(pattern.name)
          ? pattern.fields.some((f) => this.refutable(f.pattern))
          : true;
      default:
        return true;
    }
  }

  private soleConstructor(name: string): boolean {
    if (/^\(,+\)$/.test(name)) return true;
    const info = this.cons.get(name);
    if (!info) return false;
    let siblings = 0;
    for (const other of this.cons.values()) if (other.typeName === info.typeName) siblings++;
    return siblings === 1;
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

  private qualifiers(qs: GuardQualifier[] | undefined): GuardQualifier[] | undefined {
    return qs?.map((q) =>
      q.tag === "bool"
        ? { ...q, condition: this.expr(q.condition) }
        : { ...q, pattern: this.pattern(q.pattern), source: this.expr(q.source) },
    );
  }

  private guard(g: Guard): Guard {
    return {
      ...g,
      qualifiers: this.qualifiers(g.qualifiers),
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
      qualifiers: this.qualifiers(a.qualifiers),
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
      // A `String` pattern is the list of `Char` patterns it denotes, exactly
      // as a `String` *expression* is the list it denotes. Left as a literal it
      // reaches pattern-match compilation as a refutable pattern nothing tests,
      // and the alternative silently never fires.
      case "string":
        return [...p.value].reduceRight<Pattern>(
          (tail, character) => ({ tag: "con", name: ":", args: [{ tag: "char", value: character, span: p.span }, tail], span: p.span }),
          { tag: "con", name: "[]", args: [], span: p.span },
        );
      case "record": {
        const info = this.cons.get(p.name);
        // `Con {}` names a constructor and binds nothing, so it is legal for a
        // constructor declared *without* record syntax too - miso writes
        // `IndexToken {}` and `VText {}` exactly to test the tag and ignore
        // however many arguments the constructor happens to have.
        if (info && !p.wildcard && p.fields.length === 0)
          return { tag: "con", name: p.name, args: Array.from({ length: info.arity }, () => ({ tag: "wild", span: p.span }) as const), span: p.span };
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
      case "annot":
      case "typeApp":
        return { ...e, expr: this.expr(e.expr) };
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
    // A refutable binder falls through to `fail`, as the report says it must.
    // That is not cosmetic: `fail` in `Maybe` and `MaybeT` is `Nothing`, so
    // `Just x <- decodeField` is how a decoder gives up on a field. Raising
    // instead - which is what this did while the Prelude had no `MonadFail` -
    // turned a recoverable miss into an uncatchable pattern-match failure.
    const pattern = this.pattern(head.pattern);
    const name = pattern.tag === "var" ? pattern.name : this.fresh("bind");
    const onFailure: CaseAlternative[] = this.refutable(pattern)
      ? [
          {
            pattern: { tag: "wild", span },
            body: {
              tag: "app",
              fn: variable("fail", span),
              arg: { tag: "string", value: "Pattern match failure in do expression", span },
              span,
            },
          },
        ]
      : [];
    const body: Expr =
      pattern.tag === "var" || pattern.tag === "wild"
        ? tail
        : {
            tag: "case",
            subject: variable(name, span),
            alternatives: [{ pattern, body: tail }, ...onFailure],
            span,
          };
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

/** `deriving Show`, as Haskell source, in GHC's own shape: a nullary
 * constructor is its bare name, a prefix one is `showParen (d > 10)` over the
 * name and each field at precedence 11, and a record one is
 * `C {f = v, g = w}` with every field at precedence 0.
 *
 * The names printed are the *surface* ones - `URI`, not `Miso_Types_URI` -
 * which is why `src/modules.ts` keeps them on the declaration.
 *
 * A constructor written infix is skipped rather than printed prefix: GHC uses
 * its declared fixity, this pass does not track one, and a plausible guess
 * would print a value that does not read back. */
export function derivedShowSource(datas: readonly DataDeclaration[]): string {
  const out: string[] = ["module GHCTS.DerivedShow where"];
  let derived = 0;
  for (const decl of datas) {
    if (!decl.deriving.includes("Show")) continue;
    if (decl.constructors.some((c) => c.arity > 0 && /^[:(]/.test(c.surface?.name ?? c.name))) continue;
    derived++;
    const applied = decl.parameters.length ? `(${[decl.name, ...decl.parameters].join(" ")})` : decl.name;
    const context = decl.parameters.map((p) => `Show ${p}`).join(", ");
    out.push(`instance ${context ? `(${context}) => ` : ""}Show ${applied} where`);
    if (decl.constructors.length === 0) {
      // No constructors: nothing can be shown, but the instance must exist.
      out.push(`  showsPrec d x s = s`);
      continue;
    }
    for (const con of decl.constructors) {
      const name = con.surface?.name ?? con.name;
      const xs = Array.from({ length: con.arity }, (_, i) => `sA${i}`);
      const pattern = con.arity === 0 ? con.name : `(${con.name}${xs.map((x) => ` ${x}`).join("")})`;
      if (con.arity === 0) {
        out.push(`  showsPrec d ${pattern} s = showString ${JSON.stringify(name)} s`);
        continue;
      }
      const fields = con.surface?.fields ?? con.fields;
      // Each piece takes the rest of the output as its last argument, so the
      // chain is built by nesting them - which is what `.`-composed `ShowS`
      // functions come to once written out.
      const pieces: string[] = [];
      if (fields) {
        pieces.push(`showString ${JSON.stringify(`${name} {${fields[0]} = `)}`);
        xs.forEach((x, i) => {
          pieces.push(`showsPrec 0 ${x}`);
          if (i + 1 < xs.length) pieces.push(`showString ${JSON.stringify(`, ${fields[i + 1]} = `)}`);
        });
        pieces.push(`showString "}"`);
      } else {
        pieces.push(`showString ${JSON.stringify(`${name} `)}`);
        xs.forEach((x, i) => {
          if (i > 0) pieces.push(`showString " "`);
          pieces.push(`showsPrec 11 ${x}`);
        });
      }
      const body = pieces.reduceRight((rest, piece) => `${piece} (${rest})`, "sRest");
      out.push(`  showsPrec d ${pattern} s = showParen (d > 10) (\\sRest -> ${body}) s`);
    }
  }
  return derived === 0 ? "" : out.join("\n") + "\n";
}

/** `deriving Generic`, as Haskell source.
 *
 * GHC's deriving builds the `Rep` from the shape of the declaration and
 * nothing else, so it is generated the same way here - as text, parsed with
 * everything else, because every name it uses is a *data constructor* or a
 * type, and both live in one global namespace whatever module the type came
 * from. There is nothing to rename and therefore no scope to carry.
 *
 * The metadata is where this and GHC part company. GHC's `MetaData`/`MetaCons`
 * /`MetaSel` are type-level *strings*, and there is no `Symbol` kind here, so
 * each datatype, constructor and selector gets a nullary type of its own with
 * a `Datatype`/`Constructor`/`Selector` instance whose method returns the
 * name. Generic code reads those names through exactly the same class methods,
 * which is the part that has to agree.
 *
 * The sum and product trees are balanced, as GHC's are. Only self-consistency
 * is load-bearing - `from` and `to` are generated from the same tree - but
 * matching GHC costs nothing.
 */
export function derivedGenericSource(datas: readonly DataDeclaration[]): string {
  const out: string[] = ["module GHCTS.Derived where"];
  let derived = 0;
  for (const decl of datas) {
    if (!decl.deriving.includes("Generic")) continue;
    // A constructor whose field types the parser did not capture cannot be
    // given a `Rep`: `Rec0` needs the type. Better no instance than one whose
    // fields are silently the wrong types.
    if (decl.constructors.some((c) => (c.fieldTypes?.length ?? 0) !== c.arity)) continue;
    derived++;
    const meta = decl.name.replace(/[^A-Za-z0-9_]/g, "_");
    const applied = decl.parameters.length ? `(${[decl.name, ...decl.parameters].join(" ")})` : decl.name;
    out.push(`data Meta_D_${meta} = Meta_D_${meta}`);
    out.push(`instance Datatype Meta_D_${meta} where`);
    out.push(`  datatypeName x = ${JSON.stringify(decl.surfaceName ?? decl.name)}`);
    out.push(`  isNewtype x = ${decl.newtype === true ? "True" : "False"}`);

    /** One constructor: its `C1` type, and how a value of it is wrapped and
     * unwrapped. `$g<n>` names the fields; the same names appear in the
     * pattern and in the expression on the other side. */
    const conParts = decl.constructors.map((con, i) => {
      const tag = `Meta_C_${meta}_${i}`;
      out.push(`data ${tag} = ${tag}`);
      out.push(`instance Constructor ${tag} where`);
      out.push(`  conName x = ${JSON.stringify(con.surface?.name ?? con.name)}`);
      out.push(`  conIsRecord x = ${con.fields ? "True" : "False"}`);
      const fields = Array.from({ length: con.arity }, (_, j) => {
        const sel = `Meta_S_${meta}_${i}_${j}`;
        out.push(`data ${sel} = ${sel}`);
        out.push(`instance Selector ${sel} where`);
        // GHC's `selName` on a positional field is the empty string, and
        // generic code tests exactly that to tell a record from a tuple.
        out.push(`  selName x = ${JSON.stringify(con.surface?.fields?.[j] ?? con.fields?.[j] ?? "")}`);
        const type = (con.fieldTypes?.[j] ?? "").replace(/^\s*!/, "").trim();
        return { type: `S1 ${sel} (Rec0 (${type}))`, wrap: `M1 (K1 gRep${j})`, name: `gRep${j}` };
      });
      const body = fields.length === 0 ? { type: "U1", term: "U1" } : balance(fields.map((f) => ({ type: f.type, term: f.wrap })), ":*:");
      return {
        type: `C1 ${tag} (${body.type})`,
        term: `M1 (${body.term})`,
        pattern: `${con.name}${fields.map((f) => ` ${f.name}`).join("")}`,
      };
    });

    if (conParts.length === 0) {
      out.push(`instance Generic ${applied} (D1 Meta_D_${meta} V1) where`);
      out.push(`  from x = case x of`);
      out.push(`    _ -> error "Generic: uninhabited"`);
      out.push(`  to x = error "Generic: uninhabited"`);
      continue;
    }
    // The sum tree decides each constructor's `L1`/`R1` path, so it is walked
    // once and both directions read off the same walk.
    const arms: Array<{ term: string; pattern: string; con: number }> = [];
    const sum = balanceSum(conParts.map((_, i) => i), (i, path) => {
      const wrapped = path.reduceRight((inner, side) => `${side} (${inner})`, conParts[i]!.term);
      arms.push({ term: wrapped, pattern: wrapped, con: i });
      return conParts[i]!.type;
    });
    out.push(`instance Generic ${applied} (D1 Meta_D_${meta} (${sum})) where`);
    out.push(`  from x = case x of`);
    for (const arm of arms) out.push(`    ${conParts[arm.con]!.pattern} -> M1 (${arm.term})`);
    out.push(`  to x = case x of`);
    for (const arm of arms) out.push(`    M1 (${arm.pattern}) -> ${conParts[arm.con]!.pattern}`);
  }
  return derived === 0 ? "" : out.join("\n") + "\n";
}

/** A balanced tree of `op` over `items`, with the type and the term built
 * together so a `:*:` in one is a `:*:` in the other. */
function balance(items: ReadonlyArray<{ type: string; term: string }>, op: string): { type: string; term: string } {
  if (items.length === 1) return items[0]!;
  const half = Math.floor(items.length / 2);
  const left = balance(items.slice(0, half), op);
  const right = balance(items.slice(half), op);
  return { type: `${left.type} ${op} (${right.type})`, term: `${left.term} ${op} (${right.term})` };
}

/** The balanced `:+:` tree, handing each leaf the `L1`/`R1` path that reaches
 * it so the caller can build the two directions from one shape. */
function balanceSum(items: readonly number[], leaf: (item: number, path: string[]) => string, path: string[] = []): string {
  if (items.length === 1) return leaf(items[0]!, path);
  const half = Math.floor(items.length / 2);
  const left = balanceSum(items.slice(0, half), leaf, [...path, "L1"]);
  const right = balanceSum(items.slice(half), leaf, [...path, "R1"]);
  return `${left} :+: (${right})`;
}
