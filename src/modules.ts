/** The module system for the new frontend: import resolution, dependency
 * ordering and renaming.
 *
 * `src/elaborate.ts` works on one flat pile of declarations, so a program of
 * several modules is compiled by *renaming* every non-root module's top-level
 * values to a unique flat name (`Data.Counter.bump` -> `Data_Counter_bump`)
 * and rewriting each module's uses through its own scope.  A name that is not
 * in a module's scope is left exactly as written, so it either resolves to the
 * Prelude (which is never renamed) or reaches the elaborator as the honest
 * "unresolved name" it is - which is precisely what makes `hiding` and
 * unexported names observable rather than silently global.
 *
 * The root module is deliberately *not* renamed, so `main` stays `main`.
 *
 * Types, classes, data constructors and record selectors stay in one global
 * namespace; only values are module-scoped.  Instances are global by
 * construction: every module of the transitive import closure contributes its
 * instances whether or not any of its names were imported, which is Haskell's
 * rule.
 */
import type {
  CaseAlternative,
  DoStatement,
  Expr,
  Guard,
  ImportDeclaration,
  ListQualifier,
  LocalBinding,
  Module,
  Pattern,
  ValueDeclaration,
  Declaration,
} from "./ast.js";
import { error } from "./diagnostics.js";
import type { Diagnostic } from "./types.js";

/** Surface name (bare or qualified) -> flat name. */
export type Scope = ReadonlyMap<string, string>;

export interface ResolvedProgram {
  /** Modules in dependency order; the root is last. */
  order: Module[];
  /** Per-module scope, keyed by module name. */
  scopes: Map<string, Scope>;
  diagnostics: Diagnostic[];
}

const flatName = (module: string, name: string): string =>
  `${module.replace(/\./g, "_")}_${name}`;

/** Values a module defines at the top level.  Record selectors are not here:
 * they are synthesised from data declarations inside the elaborator and stay
 * global, along with constructors and class methods. */
function ownValues(module: Module): string[] {
  return module.declarations.flatMap((d) =>
    d.tag === "value" || d.tag === "foreign" ? [d.name] : [],
  );
}

function topologicalOrder(
  modules: ReadonlyMap<string, Module>,
  root: string,
  diagnostics: Diagnostic[],
): Module[] {
  const order: Module[] = [];
  const visiting: string[] = [];
  const done = new Set<string>();
  const visit = (name: string, from?: string): void => {
    if (done.has(name)) return;
    const cycle = visiting.indexOf(name);
    if (cycle >= 0) {
      diagnostics.push(
        error(
          "E_MODULE_CYCLE",
          `Module import cycle: ${[...visiting.slice(cycle), name].join(" -> ")}`,
          `${name}.hs`,
        ),
      );
      return;
    }
    const module = modules.get(name);
    if (!module) {
      // Missing modules are a warning-shaped fact of this frontend: the
      // Prelude and every unimplemented library module are "missing" too.  A
      // use of one of its names still fails, as an unresolved name.
      if (from === undefined)
        diagnostics.push(error("E_MODULE_MISSING", `Cannot find module ${name}`, `${name}.hs`));
      return;
    }
    visiting.push(name);
    for (const imported of module.imports) visit(imported.module, name);
    visiting.pop();
    done.add(name);
    order.push(module);
  };
  visit(root);
  return order;
}

/** The names an import declaration lets through, before qualification. */
function selected(imported: ImportDeclaration, exported: Scope): Array<[string, string]> {
  const entries = [...exported];
  if (imported.exposing) {
    const wanted = new Set([...imported.exposing, ...(imported.exposingConstructors ?? [])]);
    return entries.filter(([name]) => wanted.has(name));
  }
  if (imported.hiding) {
    const banned = new Set([...imported.hiding, ...(imported.hidingConstructors ?? [])]);
    return entries.filter(([name]) => !banned.has(name));
  }
  return entries;
}

export function resolveProgram(
  modules: ReadonlyMap<string, Module>,
  root: string,
): ResolvedProgram {
  const diagnostics: Diagnostic[] = [];
  const order = topologicalOrder(modules, root, diagnostics);
  const scopes = new Map<string, Scope>();
  const exports = new Map<string, Scope>();

  for (const module of order) {
    const isRoot = module.name === root;
    const scope = new Map<string, string>();
    const own = new Map<string, string>();
    for (const name of ownValues(module))
      own.set(name, isRoot ? name : flatName(module.name, name));
    // Imports first, own definitions last: a local binding shadows an
    // imported name of the same name, which is what GHC does for a use that
    // would otherwise be ambiguous only in the report.
    const fromModule = new Map<string, Scope>();
    for (const imported of module.imports) {
      const exported = exports.get(imported.module);
      if (!exported) continue; // not one of ours; names stay as written
      const visible = selected(imported, exported);
      const qualifier = imported.alias ?? imported.module;
      for (const [name, flat] of visible) {
        if (!imported.qualified) scope.set(name, flat);
        scope.set(`${qualifier}.${name}`, flat);
      }
      fromModule.set(qualifier, new Map(visible));
    }
    for (const [name, flat] of own) scope.set(name, flat);

    const exported = new Map<string, string>();
    if (module.exports.length === 0 && module.reexports.length === 0) {
      for (const [name, flat] of own) exported.set(name, flat);
    } else {
      for (const name of module.exports) {
        const flat = own.get(name) ?? scope.get(name);
        if (flat !== undefined) exported.set(name, flat);
      }
      for (const name of module.reexports) {
        if (name === module.name) for (const [n, f] of own) exported.set(n, f);
        for (const [n, f] of fromModule.get(name) ?? []) exported.set(n, f);
      }
    }
    scopes.set(module.name, scope);
    exports.set(module.name, exported);
  }
  return { order, scopes, diagnostics };
}

// ------------------------------------------------------------- renaming ---

/** Rewrite every value use in `decl` through `scope`, respecting local
 * binders: a lambda, `let`, `where`, `do` bind or pattern variable of the same
 * name shadows whatever the scope says. */
export function renameValue(decl: ValueDeclaration, scope: Scope, flat = decl.name): ValueDeclaration {
  const r = new Renamer(scope);
  return {
    ...decl,
    name: flat,
    equations: decl.equations.map((eq) => {
      const shadow = new Set<string>();
      for (const p of eq.patterns) r.patternBinders(p, shadow);
      for (const b of eq.whereBindings) shadow.add(b.name);
      return {
        patterns: eq.patterns.map((p) => r.pattern(p, shadow)),
        guards: eq.guards.map((g) => r.guard(g, shadow)),
        whereBindings: eq.whereBindings.map((b) => r.binding(b, shadow)),
      };
    }),
  };
}

/** Top-level declarations of one module, renamed for the flat pile. */
export function renameDeclarations(module: Module, scope: Scope, root: boolean): Declaration[] {
  const flatOf = (name: string): string => (root ? name : flatName(module.name, name));
  return module.declarations.map((decl) => {
    if (decl.tag === "value") return renameValue(decl, scope, flatOf(decl.name));
    if (decl.tag === "foreign" || decl.tag === "signature")
      return { ...decl, name: flatOf(decl.name) };
    return decl;
  });
}

class Renamer {
  constructor(private readonly scope: Scope) {}

  private lookup(name: string, shadow: ReadonlySet<string>): string {
    if (shadow.has(name)) return name;
    const flat = this.scope.get(name);
    if (flat !== undefined) return flat;
    // `M.Just`, `T.Text`: a qualified constructor or type lives in the one
    // global namespace, so the qualifier is simply dropped.
    const dot = name.lastIndexOf(".");
    if (dot > 0) {
      const tail = name.slice(dot + 1);
      if (/^[A-Z]/.test(tail)) return tail;
    }
    return name;
  }

  patternBinders(pattern: Pattern, into: Set<string>): void {
    switch (pattern.tag) {
      case "var":
        into.add(pattern.name);
        return;
      case "as":
        into.add(pattern.name);
        this.patternBinders(pattern.pattern, into);
        return;
      case "con":
        for (const a of pattern.args) this.patternBinders(a, into);
        return;
      case "record":
        for (const f of pattern.fields) this.patternBinders(f.pattern, into);
        return;
      default:
        return;
    }
  }

  pattern(pattern: Pattern, shadow: ReadonlySet<string>): Pattern {
    if (pattern.tag === "con")
      return {
        ...pattern,
        name: this.lookup(pattern.name, shadow),
        args: pattern.args.map((a) => this.pattern(a, shadow)),
      };
    if (pattern.tag === "as") return { ...pattern, pattern: this.pattern(pattern.pattern, shadow) };
    if (pattern.tag === "record")
      return {
        ...pattern,
        name: this.lookup(pattern.name, shadow),
        fields: pattern.fields.map((f) => ({ ...f, pattern: this.pattern(f.pattern, shadow) })),
      };
    return pattern;
  }

  binding(binding: LocalBinding, outer: ReadonlySet<string>): LocalBinding {
    const shadow = new Set(outer);
    for (const p of binding.patterns) this.patternBinders(p, shadow);
    for (const b of binding.whereBindings ?? []) shadow.add(b.name);
    return {
      ...binding,
      patterns: binding.patterns.map((p) => this.pattern(p, shadow)),
      value: this.expr(binding.value, shadow),
      guards: binding.guards?.map((g) => this.guard(g, shadow)),
      whereBindings: binding.whereBindings?.map((b) => this.binding(b, shadow)),
    };
  }

  guard(guard: Guard, outer: ReadonlySet<string>): Guard {
    // `| Just y <- f x = ...`: the pattern binds in the body only.
    const shadow = new Set(outer);
    if (guard.pattern) this.patternBinders(guard.pattern, shadow);
    return {
      condition: guard.condition ? this.expr(guard.condition, outer) : undefined,
      pattern: guard.pattern ? this.pattern(guard.pattern, outer) : undefined,
      source: guard.source ? this.expr(guard.source, outer) : undefined,
      body: this.expr(guard.body, shadow),
    };
  }

  alternative(alt: CaseAlternative, outer: ReadonlySet<string>): CaseAlternative {
    const shadow = new Set(outer);
    this.patternBinders(alt.pattern, shadow);
    const patternGuards = alt.patternGuards?.map((g) => {
      const source = this.expr(g.source, new Set(shadow));
      const pattern = this.pattern(g.pattern, shadow);
      this.patternBinders(g.pattern, shadow);
      return { pattern, source };
    });
    return {
      pattern: this.pattern(alt.pattern, outer),
      guard: alt.guard ? this.expr(alt.guard, shadow) : undefined,
      patternGuards,
      body: this.expr(alt.body, shadow),
    };
  }

  expr(expr: Expr, shadow: ReadonlySet<string>): Expr {
    switch (expr.tag) {
      case "var":
        return { ...expr, name: this.lookup(expr.name, shadow) };
      case "int":
      case "double":
      case "string":
      case "char":
      case "unit":
      case "jsQuote":
        return expr;
      case "tuple":
        return { ...expr, items: expr.items.map((e) => this.expr(e, shadow)) };
      case "list":
        return { ...expr, items: expr.items.map((e) => this.expr(e, shadow)) };
      case "listComp": {
        const inner = new Set(shadow);
        const qualifiers: ListQualifier[] = expr.qualifiers.map((q) => {
          if (q.tag === "guard") return { tag: "guard", condition: this.expr(q.condition, inner) };
          const source = this.expr(q.source, inner);
          const pattern = this.pattern(q.pattern, inner);
          this.patternBinders(q.pattern, inner);
          return { tag: "generator", pattern, source };
        });
        return { ...expr, qualifiers, body: this.expr(expr.body, inner) };
      }
      case "record":
        return {
          ...expr,
          constructor: this.lookup(expr.constructor, shadow),
          fields: expr.fields.map((f) => ({ ...f, value: this.expr(f.value, shadow) })),
        };
      case "recordUpdate":
        return {
          ...expr,
          base: this.expr(expr.base, shadow),
          fields: expr.fields.map((f) => ({ ...f, value: this.expr(f.value, shadow) })),
        };
      // Only the expression is renamed: types live in one global namespace
      // here, so the written type needs no qualification.
      case "annot":
        return { ...expr, expr: this.expr(expr.expr, shadow) };
      case "app":
        return { ...expr, fn: this.expr(expr.fn, shadow), arg: this.expr(expr.arg, shadow) };
      case "lambda": {
        const inner = new Set(shadow);
        inner.add(expr.parameter);
        return { ...expr, body: this.expr(expr.body, inner) };
      }
      case "lambdaCase":
        return { ...expr, alternatives: expr.alternatives.map((a) => this.alternative(a, shadow)) };
      case "let": {
        const inner = new Set(shadow);
        for (const b of expr.bindings) inner.add(b.name);
        return {
          ...expr,
          bindings: expr.bindings.map((b) => this.binding(b, inner)),
          body: this.expr(expr.body, inner),
        };
      }
      case "do": {
        const inner = new Set(shadow);
        const statements: DoStatement[] = expr.statements.map((s) => {
          if (s.tag === "expr") return { tag: "expr", expr: this.expr(s.expr, inner) };
          if (s.tag === "bind") {
            const source = this.expr(s.source, inner);
            const pattern = this.pattern(s.pattern, inner);
            this.patternBinders(s.pattern, inner);
            return { tag: "bind", pattern, source };
          }
          for (const b of s.bindings) inner.add(b.name);
          return { tag: "let", bindings: s.bindings.map((b) => this.binding(b, inner)) };
        });
        return { ...expr, statements };
      }
      case "if":
        return {
          ...expr,
          condition: this.expr(expr.condition, shadow),
          thenBranch: this.expr(expr.thenBranch, shadow),
          elseBranch: this.expr(expr.elseBranch, shadow),
        };
      case "case":
        return {
          ...expr,
          subject: this.expr(expr.subject, shadow),
          alternatives: expr.alternatives.map((a) => this.alternative(a, shadow)),
        };
    }
  }
}
