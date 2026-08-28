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
 * Values, data constructors, record selectors, class methods and type
 * constructors are all module-scoped.  *Class* names stay global, because
 * nothing declares two classes of one name and because a global class name is
 * what lets an instance head, a `deriving` clause and a constraint name the
 * same class from anywhere.  Instances are global by construction: every
 * module of the transitive import closure contributes its instances whether or
 * not any of its names were imported, which is Haskell's rule.
 */
import type {
  AssociatedType,
  CaseAlternative,
  ClassDeclaration,
  DoStatement,
  Expr,
  Guard,
  GuardQualifier,
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

/** The two namespaces a module resolves names in.  They are separate maps
 * because Haskell's are: `newtype Object = Object JSVal` puts one `Object` in
 * each, and miso's `Miso.JSON.Types` puts a *third*, unrelated one in the type
 * namespace alone. */
export interface Scopes {
  values: Scope;
  types: Scope;
}

/** A record field, in the two spellings a `{..}` wildcard needs at once: the
 * label it sets, and the variable name it reads. */
export interface RecordField {
  /** As written in the declaring module - the name a wildcard binds or reads. */
  surface: string;
  /** After renaming - the label the constructor's argument list is keyed by. */
  flat: string;
}

export interface ResolvedProgram {
  /** Modules in dependency order; the root is last. */
  order: Module[];
  /** Per-module value scope, keyed by module name. */
  scopes: Map<string, Scope>;
  /** Per-module *type constructor* scope, keyed by module name. */
  typeScopes: Map<string, Scope>;
  /** Record fields of each constructor, keyed by its *renamed* name. */
  fields: Map<string, RecordField[]>;
  diagnostics: Diagnostic[];
}

const flatName = (module: string, name: string): string =>
  `${module.replace(/\./g, "_")}_${name}`;

/** The method names a class declares. */
export function classMethodNames(decl: ClassDeclaration): string[] {
  return decl.members.flatMap((m) => (m.tag === "signature" && m.isDefault !== true ? [m.name] : []));
}

/** Values a module defines at the top level: its bindings, its foreign
 * imports, its class methods, and - because miso declares `MTS`, `Options`,
 * `ScrollEvent` and `errorCode` more than once across its modules - its data
 * constructors and record fields.  Type and class names stay global.
 *
 * Class methods are scoped for the same reason values are: `Control.Category`
 * declares `id` and `(.)`, and a global method of those names would capture
 * every `.` in the program.  A module sees the method only by importing the
 * class, which is what `import Prelude hiding ((.))` next to
 * `import Control.Category ((.))` asks for. */
function ownValues(module: Module, withConstructors: boolean): string[] {
  return module.declarations.flatMap((d) => {
    if (d.tag === "value" || d.tag === "foreign") return [d.name];
    if (d.tag === "class") return classMethodNames(d);
    if (d.tag === "data" && withConstructors)
      return d.constructors.flatMap((c) => [c.name, ...(c.fields ?? [])]);
    return [];
  });
}

/** Type constructors a module defines: its `data`/`newtype` declarations and
 * its type synonyms.  miso declares `Object`, `Parser`, `Options`, `Event`,
 * `Token`, `ScrollEvent` and `SelectionEvent` in two modules each - and two of
 * those pairs are a `type` against a `data`, which no arity rule can tell
 * apart. */
function ownTypes(module: Module): string[] {
  return module.declarations.flatMap((d) => (d.tag === "data" || d.tag === "typeAlias" ? [d.name] : []));
}

/** Rewrite the type constructors named in a written type through `scope`.
 *
 * A type reaches the elaborator as source text, so this is a splice over the
 * identifier tokens of that text: arrows, brackets, commas and spacing are
 * left exactly as written.  A type variable is lower case and a class name is
 * never in a type scope, so neither can be captured by this. */
export function renameTypeText(text: string, scope: Scope): string {
  if (scope.size === 0) return text;
  return text.replace(/[A-Za-z_][A-Za-z0-9_'.]*/g, (name) => scope.get(name) ?? name);
}

/** Constructors and record fields, indexed by the type that declares them,
 * plus methods indexed by the class that declares them.  `T(..)`/`C(..)` in an
 * export or import list is one name in the surface list, and it has to carry
 * these with it. */
function typeMembers(module: Module): Map<string, string[]> {
  const out = new Map<string, string[]>();
  for (const decl of module.declarations) {
    if (decl.tag === "data")
      out.set(decl.name, decl.constructors.flatMap((c) => [c.name, ...(c.fields ?? [])]));
    if (decl.tag === "class") out.set(decl.name, classMethodNames(decl));
  }
  return out;
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

/** The names an import declaration lets through, before qualification.
 * `members` maps a type of the imported module to its constructors and record
 * fields, so naming the type in the list brings them too. */
function selected(
  imported: ImportDeclaration,
  exported: Scope,
  members: ReadonlyMap<string, string[]>,
): Array<[string, string]> {
  const entries = [...exported];
  // Only `T(..)`/`C(..)` carries the members. `import Miso.Types (Attribute)`
  // names the type and nothing else - miso relies on that, because `Miso.CSS`
  // imports it beside its own `Styles` constructor and means its own.
  const expand = (names: readonly string[], wildcards: readonly string[]): Set<string> => {
    const out = new Set<string>(names);
    for (const name of wildcards) for (const member of members.get(name) ?? []) out.add(member);
    return out;
  };
  if (imported.exposing) {
    const wanted = expand(imported.exposing, imported.exposingConstructors ?? []);
    return entries.filter(([name]) => wanted.has(name));
  }
  if (imported.hiding) {
    const banned = expand(imported.hiding, imported.hidingConstructors ?? []);
    return entries.filter(([name]) => !banned.has(name));
  }
  return entries;
}

export function resolveProgram(
  modules: ReadonlyMap<string, Module>,
  root: string,
  /** Modules whose data constructors stay global - see `libraryModuleNames`. */
  globalConstructors: ReadonlySet<string> = new Set(),
): ResolvedProgram {
  const diagnostics: Diagnostic[] = [];
  const order = topologicalOrder(modules, root, diagnostics);
  const scopes = new Map<string, Scope>();
  const typeScopes = new Map<string, Scope>();
  const exports = new Map<string, Scope>();
  const typeExports = new Map<string, Scope>();
  const membersByModule = new Map<string, Map<string, string[]>>();
  const fields = new Map<string, RecordField[]>();
  const noMembers = new Map<string, string[]>();

  for (const module of order) {
    const isRoot = module.name === root;
    const scoped = !isRoot && !globalConstructors.has(module.name);
    const flatOf = (name: string): string => (isRoot ? name : flatName(module.name, name));
    for (const decl of module.declarations)
      if (decl.tag === "data")
        for (const con of decl.constructors)
          if (con.fields)
            fields.set(
              scoped ? flatOf(con.name) : con.name,
              con.fields.map((f) => ({ surface: f, flat: scoped ? flatOf(f) : f })),
            );
    const scope = new Map<string, string>();
    const typeScope = new Map<string, string>();
    const own = new Map<string, string>();
    const ownType = new Map<string, string>();
    for (const name of ownValues(module, scoped))
      own.set(name, isRoot ? name : flatName(module.name, name));
    // A library module's types stay global for the same reason its
    // constructors do: the Prelude and this compiler's own passes name
    // `MisoString`, `JSVal` and `Result` as written.
    for (const name of ownTypes(module)) ownType.set(name, scoped ? flatName(module.name, name) : name);
    // The types whose constructors and fields this module can name: its own,
    // plus every one an import let through.  `Miso.Runtime` writes
    // `Result(..)` in an import list and `Miso.JSON` only re-exports it, so a
    // module's index has to carry what it imported as well as what it declared.
    const visibleMembers = new Map<string, string[]>(
      [...typeMembers(module)].map(([type, names]) => [type, names.filter((n) => own.has(n))]),
    );
    // Imports first, own definitions last: a local binding shadows an
    // imported name of the same name, which is what GHC does for a use that
    // would otherwise be ambiguous only in the report.
    const fromModule = new Map<string, Scope>();
    const typeFromModule = new Map<string, Scope>();
    for (const imported of module.imports) {
      const exported = exports.get(imported.module);
      if (!exported) continue; // not one of ours; names stay as written
      const theirs = membersByModule.get(imported.module) ?? new Map<string, string[]>();
      const visible = selected(imported, exported, theirs);
      const qualifier = imported.alias ?? imported.module;
      for (const [name, flat] of visible) {
        if (!imported.qualified) scope.set(name, flat);
        scope.set(`${qualifier}.${name}`, flat);
      }
      // A type is named in an import list by itself, so the `T(..)` expansion
      // that carries constructors has nothing to add here.
      const visibleTypes = selected(imported, typeExports.get(imported.module) ?? new Map(), noMembers);
      for (const [name, flat] of visibleTypes) {
        if (!imported.qualified) typeScope.set(name, flat);
        typeScope.set(`${qualifier}.${name}`, flat);
      }
      typeFromModule.set(qualifier, new Map(visibleTypes));
      const let_ = new Set(visible.map(([name]) => name));
      for (const [type, names] of theirs) {
        const kept = names.filter((n) => let_.has(n));
        if (kept.length) visibleMembers.set(type, [...new Set([...(visibleMembers.get(type) ?? []), ...kept])]);
      }
      fromModule.set(qualifier, new Map(visible));
    }
    for (const [name, flat] of own) scope.set(name, flat);
    for (const [name, flat] of ownType) typeScope.set(name, flat);

    const exported = new Map<string, string>();
    const typeExported = new Map<string, string>();
    if (module.exports.length === 0 && module.reexports.length === 0) {
      for (const [name, flat] of own) exported.set(name, flat);
      for (const [name, flat] of ownType) typeExported.set(name, flat);
    } else {
      for (const name of module.exports) {
        const flat = own.get(name) ?? scope.get(name);
        if (flat !== undefined) exported.set(name, flat);
        const typeFlat = ownType.get(name) ?? typeScope.get(name);
        if (typeFlat !== undefined) typeExported.set(name, typeFlat);
        // `T(..)` reaches here as the single name `T`; its constructors and
        // record fields are exported with it.
        for (const member of visibleMembers.get(name) ?? []) {
          const memberFlat = own.get(member) ?? scope.get(member);
          if (memberFlat !== undefined) exported.set(member, memberFlat);
        }
      }
      for (const name of module.reexports) {
        if (name === module.name) {
          for (const [n, f] of own) exported.set(n, f);
          for (const [n, f] of ownType) typeExported.set(n, f);
        }
        for (const [n, f] of fromModule.get(name) ?? []) exported.set(n, f);
        for (const [n, f] of typeFromModule.get(name) ?? []) typeExported.set(n, f);
      }
    }
    scopes.set(module.name, scope);
    typeScopes.set(module.name, typeScope);
    exports.set(module.name, exported);
    typeExports.set(module.name, typeExported);
    membersByModule.set(
      module.name,
      new Map([...visibleMembers].map(([type, names]) => [type, names.filter((n) => exported.has(n))])),
    );
  }
  return { order, scopes, typeScopes, fields, diagnostics };
}

// ------------------------------------------------------------- renaming ---

/** Rewrite every value use in `decl` through `scope`, respecting local
 * binders: a lambda, `let`, `where`, `do` bind or pattern variable of the same
 * name shadows whatever the scope says. */
export function renameValue(
  decl: ValueDeclaration,
  scopes: Scopes,
  flat = decl.name,
  fields: ReadonlyMap<string, RecordField[]> = new Map(),
): ValueDeclaration {
  const r = new Renamer(scopes, fields);
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
export function renameDeclarations(
  module: Module,
  scopes: Scopes,
  root: boolean,
  scopeConstructors = false,
  fields: ReadonlyMap<string, RecordField[]> = new Map(),
): Declaration[] {
  const flatOf = (name: string): string => (root ? name : flatName(module.name, name));
  // A written type is rewritten wherever it is written, whether or not *this*
  // module's own types were renamed: a library module still names a project
  // module's `Object` by whatever that module renamed it to.
  const ty = (text: string): string => renameTypeText(text, scopes.types);
  const assoc = (a: AssociatedType): AssociatedType => (a.rhs === undefined ? a : { ...a, rhs: ty(a.rhs) });
  return module.declarations.map((decl) => {
    if (decl.tag === "value") return renameValue(decl, scopes, flatOf(decl.name), fields);
    if (decl.tag === "foreign")
      return { ...decl, name: flatOf(decl.name), signature: decl.signature.map(ty) };
    if (decl.tag === "signature") return { ...decl, name: flatOf(decl.name), type: ty(decl.type) };
    // The class name stays global; its methods and the types they mention do
    // not.  Only the signatures are rewritten here - the bodies are unparsed
    // source, renamed where they are parsed, against the same scopes.
    if (decl.tag === "class")
      return {
        ...decl,
        context: decl.context.map(ty),
        associatedTypes: decl.associatedTypes.map(assoc),
        members: decl.members.map((m) =>
          m.tag === "signature" ? { ...m, name: flatOf(m.name), surfaceName: m.name, type: ty(m.type) } : m,
        ),
      };
    if (decl.tag === "instance")
      return { ...decl, head: ty(decl.head), associatedTypes: decl.associatedTypes.map(assoc) };
    if (decl.tag === "typeAlias")
      return {
        ...decl,
        ...(scopeConstructors ? { name: flatOf(decl.name) } : {}),
        target: ty(decl.target),
      };
    if (decl.tag === "data")
      return {
        ...decl,
        surfaceName: decl.name,
        ...(scopeConstructors ? { name: flatOf(decl.name) } : {}),
        constructors: decl.constructors.map((c) => ({
          ...c,
          surface: { name: c.name, ...(c.fields ? { fields: c.fields } : {}) },
          ...(scopeConstructors ? { name: flatOf(c.name), ...(c.fields ? { fields: c.fields.map(flatOf) } : {}) } : {}),
          ...(c.fieldTypes ? { fieldTypes: c.fieldTypes.map(ty) } : {}),
        })),
      };
    return decl;
  });
}

const NOTHING: ReadonlySet<string> = new Set();

class Renamer {
  private readonly scope: Scope;
  constructor(
    private readonly scopes: Scopes,
    private readonly fields: ReadonlyMap<string, RecordField[]> = new Map(),
  ) {
    this.scope = scopes.values;
  }

  /** The fields a `{..}` stands for here: those the record does not write out.
   * A wildcard is resolved while both spellings of a field are still known -
   * the label the constructor is keyed by, and the surface name the wildcard
   * binds or reads - which is why it cannot wait for `src/sugar.ts`. */
  /** A field *label* is the selector's name and never a local variable, so it
   * is resolved past whatever the equation has bound: `Response { body = body }`
   * sets `Miso_FFI_Internal_body` from the parameter `body`. */
  private label(name: string): string {
    return this.lookup(name, NOTHING);
  }

  private wildcardFields(
    constructor: string,
    written: readonly string[],
    shadow: ReadonlySet<string>,
  ): RecordField[] | undefined {
    const all = this.fields.get(this.lookup(constructor, shadow));
    if (!all) return undefined;
    const given = new Set(written);
    return all.filter((f) => !given.has(f.surface));
  }

  private lookup(name: string, shadow: ReadonlySet<string>): string {
    if (shadow.has(name)) return name;
    const flat = this.scope.get(name);
    if (flat !== undefined) return flat;
    // `M.Just`, `T.Text`: a qualified constructor or type lives in the one
    // global namespace, so the qualifier is simply dropped.
    const dot = name.lastIndexOf(".");
    if (dot > 0) {
      const tail = name.slice(dot + 1);
      // A `:`-headed tail is an infix constructor (`S.:<|`), which lives in the
      // same global namespace as `S.Empty`.
      if (/^[A-Z:]/.test(tail)) return tail;
      // `Prelude.map`, `Prelude.id`: the Prelude is prepended to every module
      // and never renamed, so its qualified spelling is its bare one. miso
      // writes it wherever it has shadowed a Prelude name locally.
      if (name.slice(0, dot) === "Prelude") return tail;
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
        // `C {..}` binds each unwritten field under its surface name, which
        // shadows the selector of the same name for the rest of the equation.
        if (pattern.wildcard)
          for (const f of this.wildcardFields(pattern.name, pattern.fields.map((f) => f.name), into) ?? [])
            into.add(f.surface);
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
    if (pattern.tag === "record") {
      // The *label* is the record selector's name, and it moved with the
      // constructor; the variable a `{..}` binds keeps the surface spelling.
      // A constructor this pass has never seen declared - the Prelude's, say -
      // keeps its wildcard for `src/sugar.ts` rather than losing it here.
      const wildcard = pattern.wildcard ? this.wildcardFields(pattern.name, pattern.fields.map((f) => f.name), shadow) : [];
      return {
        ...pattern,
        name: this.lookup(pattern.name, shadow),
        wildcard: wildcard === undefined,
        fields: [
          ...pattern.fields.map((f) => ({ name: this.label(f.name), pattern: this.pattern(f.pattern, shadow) })),
          ...(wildcard ?? []).map((f) => ({ name: f.flat, pattern: { tag: "var" as const, name: f.surface, span: pattern.span } })),
        ],
      };
    }
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
      // A local signature names types in the module's scope, exactly as a
      // top-level one does. Left unrenamed it says `MisoString` where the
      // program says `JSString`, and the binding is checked against a type
      // nothing else in the program has.
      ...(binding.signature === undefined ? {} : { signature: renameTypeText(binding.signature, this.scopes.types) }),
    };
  }

  /** A guard's qualifiers bind left to right: `Right x <- a, Just y <- f x`
   * has `x` in scope for the second source, and both `x` and `y` in the body. */
  qualifiers(qualifiers: readonly GuardQualifier[] | undefined, shadow: Set<string>): GuardQualifier[] {
    return (qualifiers ?? []).map((q) => {
      if (q.tag === "bool") return { tag: "bool" as const, condition: this.expr(q.condition, shadow) };
      const source = this.expr(q.source, shadow);
      const pattern = this.pattern(q.pattern, shadow);
      this.patternBinders(q.pattern, shadow);
      return { tag: "pattern" as const, pattern, source };
    });
  }

  guard(guard: Guard, outer: ReadonlySet<string>): Guard {
    const shadow = new Set(outer);
    return {
      qualifiers: this.qualifiers(guard.qualifiers, shadow),
      body: this.expr(guard.body, shadow),
    };
  }

  alternative(alt: CaseAlternative, outer: ReadonlySet<string>): CaseAlternative {
    const shadow = new Set(outer);
    this.patternBinders(alt.pattern, shadow);
    return {
      pattern: this.pattern(alt.pattern, outer),
      qualifiers: this.qualifiers(alt.qualifiers, shadow),
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
      case "record": {
        // `C {..}` fills each unwritten field from the variable of that name in
        // scope, which is nearly always a local one shadowing the selector -
        // so the value is looked up under the *surface* name, through the same
        // shadow set as any other use.
        const wildcard = expr.wildcard ? this.wildcardFields(expr.constructor, expr.fields.map((f) => f.name), shadow) : [];
        return {
          ...expr,
          constructor: this.lookup(expr.constructor, shadow),
          wildcard: wildcard === undefined,
          fields: [
            ...expr.fields.map((f) => ({ name: this.label(f.name), value: this.expr(f.value, shadow) })),
            ...(wildcard ?? []).map((f) => ({
              name: f.flat,
              value: { tag: "var" as const, name: this.lookup(f.surface, shadow), span: expr.span },
            })),
          ],
        };
      }
      case "recordUpdate":
        return {
          ...expr,
          base: this.expr(expr.base, shadow),
          fields: expr.fields.map((f) => ({ name: this.label(f.name), value: this.expr(f.value, shadow) })),
        };
      case "annot":
      case "typeApp":
        return {
          ...expr,
          expr: this.expr(expr.expr, shadow),
          type: renameTypeText(expr.type, this.scopes.types),
        };
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
