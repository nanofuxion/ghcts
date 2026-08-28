import type {
  Expr,
  ForeignDeclaration,
  Module,
  Pattern,
  ValueDeclaration,
} from "./ast.js";
import { error } from "./diagnostics.js";
import type { Diagnostic } from "./types.js";
import { collectInterface } from "./interface.js";
import { collectDictionaries, type DictionaryTable } from "./dictionary.js";

type Type =
  | { tag: "var"; id: number }
  | { tag: "con"; name: string }
  | { tag: "app"; fn: Type; arg: Type }
  | { tag: "fn"; from: Type; to: Type };
interface Scheme {
  vars: number[];
  type: Type;
  constraints?: string[];
}
type Environment = Map<string, Scheme>;
type Substitution = Map<number, Type>;
type TypeAlias = { parameters: string[]; target: string };
const int: Type = { tag: "con", name: "Int" };
const string: Type = { tag: "con", name: "String" };
const bool: Type = { tag: "con", name: "Bool" };
const fn = (from: Type, to: Type): Type => ({ tag: "fn", from, to });
const typeApp = (fn_: Type, arg: Type): Type => ({ tag: "app", fn: fn_, arg });
const typeConApp = (name: string, arg: Type): Type =>
  typeApp({ tag: "con", name }, arg);

export interface TypecheckResult {
  diagnostics: Diagnostic[];
  types: Map<string, string>;
  constraints: Map<string, string[]>;
  dictionaries: DictionaryTable;
}
export function checkModule(module: Module, file: string): TypecheckResult {
  return checkModules([{ module, file }]);
}
export function checkModules(
  modules: Array<{ module: Module; file: string }>,
  roots?: Array<{ module: string; name: string }>,
): TypecheckResult {
  modules = orderModules(modules);
  const reachable = roots ? reachableValues(modules, roots) : undefined;
  const context = new Inferencer();
  const types = new Map<string, string>();
  const constraints = new Map<string, string[]>();
  const dictionaries = collectDictionaries(modules.map((item) => item.module));
  const rootModules = new Set((roots ?? []).map((root) => root.module));
  // Interfaces and module-owned schemes are deliberately separate.  The
  // former answers "may this import name be mentioned?" while the latter
  // carries its inferred type.  This prevents a later module's `map`/`empty`
  // from silently replacing an earlier module's binding in one flat map.
  const interfaces = new Map(
    modules.map(({ module }) => [module.name, collectInterface(module)]),
  );
  const moduleSymbols = new Map<string, Environment>();
  // Type synonyms participate in signatures across module boundaries. Keep
  // their textual targets available while imported schemes are inferred;
  // otherwise aliases such as JSString become unrelated fresh variables.
  const allAliases = new Map<string, TypeAlias>();
  for (const { module } of modules)
    for (const declaration of module.declarations)
      if (declaration.tag === "typeAlias")
        allAliases.set(declaration.name, {
          parameters: declaration.parameters,
          target: declaration.target,
        });
  const signatures = new Map<string, string>();
  for (const { module } of modules)
    for (const declaration of module.declarations)
      if (declaration.tag === "signature") {
        const key = `${module.name}.${declaration.name}`;
        signatures.set(key, declaration.type);
        const declaredConstraints = signatureConstraints(declaration.type);
        if (declaredConstraints.length)
          constraints.set(key, declaredConstraints);
      }
  for (const { module, file } of modules) {
    const environment = importEnvironment(
      module,
      file,
      interfaces,
      moduleSymbols,
      context,
    );
    const own: Environment = new Map();
    const aliases = new Map(allAliases);
    for (const declaration of module.declarations)
      if (declaration.tag === "typeAlias")
        aliases.set(declaration.name, {
          parameters: declaration.parameters,
          target: declaration.target,
        });
    for (const declaration of module.declarations)
      if (declaration.tag === "data")
        for (const constructor of declaration.constructors) {
          const parameters = declaration.parameters.map(() => context.fresh());
          let type: Type = parameters.reduce<Type>(
            (result, parameter) => typeApp(result, parameter),
            { tag: "con", name: declaration.name },
          );
          // The compact data AST records constructor arity, not field type
          // syntax, so each field is fresh here.  The return type nonetheless
          // shares the declaration parameters: `Just :: a -> Maybe a`, rather
          // than the old unsound `t -> Maybe`.
          const parameterVariables = new Map(
            declaration.parameters.map((name, index) => [
              name,
              parameters[index],
            ]),
          );
          const declaredFields = (constructor.fieldTypes ?? []).map((source) =>
            parseSignature(source, context, aliases, parameterVariables),
          );
          const fields = Array.from(
            { length: constructor.arity },
            (_, index) =>
              declaredFields[index] ?? parameters[index] ?? context.fresh(),
          );
          for (const field of [...fields].reverse()) type = fn(field, type);
          const scheme = { vars: [...free(type)], type };
          own.set(constructor.name, scheme);
          environment.set(constructor.name, scheme);
          types.set(`${module.name}.${constructor.name}`, show(type));
          for (const [index, field] of (constructor.fields ?? []).entries()) {
            const source = constructor.fieldTypes?.[index]?.trim();
            const parameterIndex = source
              ? declaration.parameters.indexOf(source)
              : -1;
            const fieldType =
              parameterIndex >= 0
                ? parameters[parameterIndex]
                : source
                  ? parseSignature(source, context, aliases)
                  : context.fresh();
            const recordType = parameters.reduce<Type>(
              (result, parameter) => typeApp(result, parameter),
              { tag: "con", name: declaration.name },
            );
            const fieldScheme = {
              vars: [...free(fieldType), ...free(recordType)],
              type: fn(recordType, fieldType),
            };
            own.set(field, fieldScheme);
            environment.set(field, fieldScheme);
          }
        }
    for (const declaration of module.declarations)
      if (declaration.tag === "foreign") {
        try {
          const type = foreignType(declaration, context);
          const scheme = { vars: [...free(type)], type };
          own.set(declaration.name, scheme);
          environment.set(declaration.name, scheme);
        } catch (cause) {
          const message =
            cause instanceof Error ? cause.message : String(cause);
          context.diagnostics.push(
            error(
              "E_TYPE",
              message,
              file,
              declaration.span.line,
              declaration.span.column,
            ),
          );
        }
      }
    // Class methods are exported through their class interface even before
    // instance dictionaries are lowered.  Their constraints are retained in
    // source/type metadata; this HM pass exposes the method shape so imported
    // references resolve at the owning declaration rather than as missing
    // globals.
    for (const declaration of module.declarations)
      if (declaration.tag === "class")
        for (const member of declaration.members)
          if (member.tag === "signature") {
            const type = parseSignature(member.type, context, aliases);
            const memberConstraints = signatureConstraints(member.type);
            const scheme = {
              vars: [...free(type)],
              type,
              constraints: memberConstraints,
            };
            own.set(member.name, scheme);
            environment.set(member.name, scheme);
            types.set(`${module.name}.${member.name}`, show(type));
            if (memberConstraints.length)
              constraints.set(
                `${module.name}.${member.name}`,
                memberConstraints,
              );
          }
    // Haskell declarations are a recursive group.  Reserve each binding in
    // the module scope before inferring any right hand side; `value` refines
    // that exact placeholder below rather than allocating an unrelated one.
    for (const declaration of module.declarations)
      if (declaration.tag === "value") {
        const scheme = { vars: [], type: context.fresh() };
        own.set(declaration.name, scheme);
        environment.set(declaration.name, scheme);
      }
    for (const declaration of module.declarations)
      if (
        declaration.tag === "value" &&
        (!reachable || reachable.has(`${module.name}.${declaration.name}`))
      ) {
        const declaredSignature = signatures.get(
          `${module.name}.${declaration.name}`,
        );
      const advancedSignature = declaredSignature && /\b(?:Effect|App|View|Lens|Component|RWS|Sub|StaticPtr)\b/.test(declaredSignature);
      if (declaredSignature && (roots && !rootModules.has(module.name) || advancedSignature)) {
          const scheme = environment.get(declaration.name)!;
          scheme.type = parseSignature(declaredSignature, context, aliases);
          scheme.vars = [...free(scheme.type)];
          scheme.constraints = signatureConstraints(declaredSignature);
          own.set(declaration.name, scheme);
          types.set(`${module.name}.${declaration.name}`, show(scheme.type));
          continue;
        }
        // Constraint-bearing library helpers are elaborated by the dictionary
        // phase. Preserve and export their declared polymorphic shape here
        // instead of attempting to infer a class method body with no evidence
        // yet (for example Lens's Num/MonadState operators).
        if (
          declaredSignature &&
          signatureConstraints(declaredSignature).length
        ) {
          const scheme = environment.get(declaration.name)!;
          scheme.type = parseSignature(declaredSignature, context, aliases);
          scheme.vars = [...free(scheme.type)];
          scheme.constraints = signatureConstraints(declaredSignature);
          own.set(declaration.name, scheme);
          types.set(`${module.name}.${declaration.name}`, show(scheme.type));
          continue;
        }
        try {
          const type = context.value(declaration, environment);
          const signature = signatures.get(
            `${module.name}.${declaration.name}`,
          );
          if (signature)
            context.unify(type, parseSignature(signature, context, aliases));
          const scheme = environment.get(declaration.name)!;
          if (signature) scheme.constraints = signatureConstraints(signature);
          own.set(declaration.name, scheme);
          types.set(
            `${module.name}.${declaration.name}`,
            show(context.apply(type)),
          );
        } catch (cause) {
          const message =
            cause instanceof Error ? cause.message : String(cause);
          context.diagnostics.push(
            error(
              "E_TYPE",
              message,
              file,
              declaration.span.line,
              declaration.span.column,
            ),
          );
        }
      }
    // A module header can explicitly re-export an imported module.  Preserve
    // those schemes under their original names for downstream imports; the
    // later export-list phase will apply any finer-grained filtering.
    for (const reexport of module.reexports)
      for (const [name, scheme] of moduleSymbols.get(reexport) ?? [])
        if (!own.has(name)) own.set(name, scheme);
    // An explicit export list can re-export an unqualified import without
    // naming `module That.Module`.
    // Bind its resolved scheme to the owning module interface only after all
    // local declarations have been inferred.
    for (const exported of module.exports) {
      const scheme = environment.get(exported);
      if (scheme && !own.has(exported)) own.set(exported, scheme);
    }
    moduleSymbols.set(module.name, own);
  }
  for (const { module, file } of modules)
    for (const declaration of module.declarations) {
      if (declaration.tag === "unsupported" && (!roots || rootModules.has(module.name)))
        context.diagnostics.push(
          error(
            "E_UNSUPPORTED",
            `${declaration.feature} declarations are parsed but not yet supported by typechecking`,
            file,
            declaration.span.line,
            declaration.span.column,
          ),
        );
    }
  return { diagnostics: context.diagnostics, types, constraints, dictionaries };
}
/** Build only the names a module is entitled to use.  Qualified lookup is an
 * ordinary environment key (`Alias.name`); there is no last-component
 * fallback, so `WrongAlias.name` cannot resolve by accident. */
function orderModules(
  modules: Array<{ module: Module; file: string }>,
): Array<{ module: Module; file: string }> {
  const byName = new Map(modules.map((item) => [item.module.name, item]));
  const visiting = new Set<string>();
  const visited = new Set<string>();
  const ordered: Array<{ module: Module; file: string }> = [];
  const visit = (name: string) => {
    if (visited.has(name) || visiting.has(name)) return;
    const item = byName.get(name);
    if (!item) return;
    visiting.add(name);
    for (const imported of item.module.imports) visit(imported.module);
    visiting.delete(name);
    visited.add(name);
    ordered.push(item);
  };
  for (const item of modules) visit(item.module.name);
  return ordered;
}
function reachableValues(
  modules: Array<{ module: Module; file: string }>,
  roots: Array<{ module: string; name: string }>,
): Set<string> {
  const byName = new Map(
    modules.map((item) => [item.module.name, item.module]),
  );
  const declarations = new Map<string, import("./ast.js").Declaration>();
  const localNames = new Map<string, Set<string>>();
  for (const { module } of modules) {
    const names = new Set<string>();
    for (const declaration of module.declarations) {
      if (declaration.tag === "value" || declaration.tag === "foreign") {
        names.add(declaration.name);
        declarations.set(`${module.name}.${declaration.name}`, declaration);
      }
    }
    localNames.set(module.name, names);
  }
  const result = new Set<string>();
  const queue = [...roots.map((root) => `${root.module}.${root.name}`)];
  const importsFor = (module: Module, name: string): string | undefined => {
    if (localNames.get(module.name)?.has(name)) return `${module.name}.${name}`;
    for (const imported of module.imports) {
      const alias = imported.alias ?? imported.module;
      const qualified = name.startsWith(`${alias}.`)
        ? name.slice(alias.length + 1)
        : undefined;
      const candidate = qualified ?? name;
      if (imported.hiding?.includes(candidate)) continue;
      if (imported.exposing && !imported.exposing.includes(candidate)) continue;
      if (localNames.get(imported.module)?.has(candidate))
        return `${imported.module}.${candidate}`;
    }
    return undefined;
  };
  const namesIn = (value: unknown, output: Set<string>) => {
    if (!value || typeof value !== "object") return;
    if (
      (value as { tag?: string }).tag === "var" &&
      typeof (value as { name?: unknown }).name === "string"
    )
      output.add((value as { name: string }).name);
    for (const child of Object.values(value as Record<string, unknown>)) {
      if (Array.isArray(child)) child.forEach((item) => namesIn(item, output));
      else namesIn(child, output);
    }
  };
  while (queue.length) {
    const key = queue.shift()!;
    if (result.has(key)) continue;
    const declaration = declarations.get(key);
    if (!declaration) continue;
    result.add(key);
    const moduleName = key.slice(0, key.lastIndexOf("."));
    const module = byName.get(moduleName);
    if (!module || declaration.tag !== "value") continue;
    const names = new Set<string>();
    namesIn(declaration.equations, names);
    for (const name of names) {
      const target = importsFor(module, name);
      if (target && !result.has(target)) queue.push(target);
    }
  }
  return result;
}
function importEnvironment(
  module: Module,
  _file: string,
  interfaces: ReadonlyMap<string, ReturnType<typeof collectInterface>>,
  moduleSymbols: ReadonlyMap<string, Environment>,
  context: Inferencer,
): Environment {
  const environment = prelude(context);
  for (const declaration of module.imports) {
    const importedInterface = interfaces.get(declaration.module);
    const imported = moduleSymbols.get(declaration.module);
    if (!importedInterface || !imported) continue; // module loading owns E_IMPORT
    const available = new Set([
      ...importedInterface.values,
      ...importedInterface.constructors,
      ...importedInterface.fields,
      ...imported.keys(),
    ]);
    const requested = declaration.exposing ?? [...available];
    const selected = new Set(
      requested.filter((name) => !declaration.hiding?.includes(name)),
    );
    for (const typeName of declaration.exposingConstructors ?? []) {
      for (const constructor of importedInterface.constructorsByType.get(
        typeName,
      ) ?? [])
        selected.add(constructor);
      for (const field of importedInterface.fieldsByType.get(typeName) ?? [])
        selected.add(field);
    }
    for (const typeName of declaration.hidingConstructors ?? []) {
      for (const constructor of importedInterface.constructorsByType.get(
        typeName,
      ) ?? [])
        selected.delete(constructor);
      for (const field of importedInterface.fieldsByType.get(typeName) ?? [])
        selected.delete(field);
    }
    // Export-list checking waits for the type/class namespace and re-export
    // table.  Filtering *value* schemes here is still important: a selected
    // name that has no implementation simply is not in scope at its use.
    const qualifier = declaration.alias ?? declaration.module;
    for (const name of selected) {
      const scheme = imported.get(name);
      if (!scheme) continue; // imported type-only names gain support with the type namespace.
      environment.set(`${qualifier}.${name}`, scheme);
      if (!declaration.qualified) {
        // Re-exports need identity tracking before ambiguity diagnostics are
        // sound.  Keep the most recent binding for now, as the former global
        // linker did, but never let it leak into a qualified lookup.
        environment.set(name, scheme);
      }
    }
  }
  return environment;
}
function parseSignature(
  source: string,
  context: Inferencer,
  aliases: ReadonlyMap<string, TypeAlias> = new Map(),
  sharedVariables: ReadonlyMap<string, Type> = new Map(),
): Type {
  // Keep constructors and their arguments distinct.  Treating `Maybe Int`
  // as one opaque string made `Maybe Int` unify with `Maybe String`, which
  // is precisely the kind of false acceptance that blocks Miso signatures.
  const tokens =
    source
      .replace(/^.*?=>\s*/, "")
      .match(/->|\[|\]|\(|\)|,|[A-Za-z_][A-Za-z0-9_.']*/g) ?? [];
  const variables = new Map<string, Type>();
  let index = 0;
  const atom = (): Type => {
    const token = tokens[index++] ?? "()";
    if (token === "(") {
      if (tokens[index] === ")") {
        index++;
        return { tag: "con", name: "()" };
      }
      const items = [arrow()];
      while (tokens[index] === ",") {
        index++;
        items.push(arrow());
      }
      if (tokens[index] === ")") index++;
      return items.length === 1
        ? items[0]
        : items.reduce<Type>((result, item) => typeApp(result, item), {
            tag: "con",
            name: `Tuple${items.length}`,
          });
    }
    if (token === "[") {
      const item = arrow();
      if (tokens[index] === "]") index++;
      return typeConApp("List", item);
    }
    if (/^[a-z]/.test(token))
      return (
        variables.get(token) ??
        sharedVariables.get(token) ??
        (() => {
          const fresh = context.fresh();
          variables.set(token, fresh);
          return fresh;
        })()
      );
    const alias = aliases.get(token);
    return alias && alias.parameters.length === 0
      ? parseSignature(alias.target, context, aliases)
      : { tag: "con", name: token };
  };
  const application = (): Type => {
    const head = tokens[index];
    let result = atom();
    const args: Type[] = [];
    while (
      index < tokens.length &&
      !["->", ")", "]", ","].includes(tokens[index])
    )
      args.push(atom());
    const alias = head ? aliases.get(head) : undefined;
    if (alias && alias.parameters.length === args.length)
      return parseSignature(
        alias.target,
        context,
        aliases,
        new Map(
          alias.parameters.map((name, position) => [name, args[position]]),
        ),
      );
    return args.reduce(typeApp, result);
  };
  const arrow = (): Type => {
    const left = application();
    if (tokens[index] !== "->") return left;
    index++;
    return fn(left, arrow());
  };
  return arrow();
}
/** Constraints are retained independently from the compact monotype parser.
 * The latter intentionally erases them while HM inference is being replaced;
 * keeping their normalized source now makes dictionary elaboration explicit
 * and source-located rather than reconstructing it from an already-erased
 * type later. */
function signatureConstraints(source: string): string[] {
  const marker = source.lastIndexOf("=>");
  if (marker < 0) return [];
  const prefix = source
    .slice(0, marker)
    .trim()
    .replace(/^\((.*)\)$/, "$1");
  return prefix
    .split(",")
    .map((item) => item.trim())
    .filter(Boolean);
}
function prelude(context: Inferencer): Environment {
  const env: Environment = new Map();
  const numeric = (result: Type) => fn(int, fn(int, result));
  const polymorphic = (count: number) =>
    Array.from({ length: count }, () => context.fresh());
  env.set("+", { vars: [], type: numeric(int) });
  env.set("-", { vars: [], type: numeric(int) });
  env.set("*", { vars: [], type: numeric(int) });
  env.set("/", { vars: [], type: numeric(int) });
  env.set("True", { vars: [], type: bool });
  env.set("False", { vars: [], type: bool });
  env.set("otherwise", { vars: [], type: bool });
  env.set("&&", { vars: [], type: fn(bool, fn(bool, bool)) });
  env.set("||", { vars: [], type: fn(bool, fn(bool, bool)) });
  env.set("not", { vars: [], type: fn(bool, bool) });
  // Prelude is implicitly imported by every ordinary Haskell module.  Keep
  // its algebraic constructors here as polymorphic schemes rather than
  // relying on a synthetic source module being explicitly linked.
  {
    const [a] = polymorphic(1);
    env.set("Nothing", {
      vars: [(a as { id: number }).id],
      type: typeConApp("Maybe", a),
    });
    env.set("Just", {
      vars: [(a as { id: number }).id],
      type: fn(a, typeConApp("Maybe", a)),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("Left", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(a, typeApp(typeConApp("Either", a), b)),
    });
    env.set("Right", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(b, typeApp(typeConApp("Either", a), b)),
    });
  }
  env.set("<", { vars: [], type: numeric(bool) });
  env.set(">", { vars: [], type: numeric(bool) });
  env.set("<=", { vars: [], type: numeric(bool) });
  env.set(">=", { vars: [], type: numeric(bool) });
  env.set("putStrLn", {
    vars: [],
    type: fn(string, typeConApp("IO", { tag: "con", name: "()" })),
  });
  {
    const [a] = polymorphic(1);
    env.set("error", { vars: [(a as { id: number }).id], type: fn(string, a) });
  }
  env.set("round", { vars: [], type: fn({ tag: "con", name: "Double" }, int) });
  env.set("negate", { vars: [], type: fn(int, int) });
  {
    const [a] = polymorphic(1);
    env.set("static", {
      vars: [(a as { id: number }).id],
      type: fn(a, typeConApp("StaticPtr", a)),
    });
    env.set("deRefStaticPtr", {
      vars: [(a as { id: number }).id],
      type: fn(typeConApp("StaticPtr", a), a),
    });
    env.set("staticKey", {
      vars: [(a as { id: number }).id],
      type: fn(typeConApp("StaticPtr", a), { tag: "con", name: "Fingerprint" }),
    });
    env.set("unsafeLookupStaticPtr", {
      vars: [(a as { id: number }).id],
      type: fn(
        { tag: "con", name: "Fingerprint" },
        typeConApp("IO", typeConApp("Maybe", typeConApp("StaticPtr", a))),
      ),
    });
  }
  {
    const [a] = polymorphic(1);
    const equality = fn(a, fn(a, bool));
    env.set("==", { vars: [(a as { id: number }).id], type: equality });
    env.set("/=", { vars: [(a as { id: number }).id], type: equality });
  }
  // These overloaded operations are represented as constraint-free schemes
  // until the typed-Core dictionary pass attaches their class predicates.
  // Keeping their shapes here lets ordinary inference distinguish application
  // errors from unresolved imports while preserving a single runtime entry.
  {
    const [a] = polymorphic(1);
    env.set("<>", { vars: [(a as { id: number }).id], type: fn(a, fn(a, a)) });
    env.set("mempty", { vars: [(a as { id: number }).id], type: a });
    env.set("mconcat", {
      vars: [(a as { id: number }).id],
      type: fn(typeConApp("List", a), a),
    });
  }
  {
    const [f, a] = polymorphic(2);
    const fa = typeApp(f, a);
    env.set("<|>", {
      vars: [(f as { id: number }).id, (a as { id: number }).id],
      type: fn(fa, fn(fa, fa)),
    });
  }
  {
    const [f, a, b] = polymorphic(3);
    const fa = typeApp(f, a);
    const fb = typeApp(f, b);
    env.set("<$", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(a, fn(fb, fa)),
    });
    env.set("<*", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(fa, fn(fb, fa)),
    });
    env.set("<*>", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(typeApp(f, fn(a, b)), fn(fa, fb)),
    });
  }
  {
    const [f, a, b] = polymorphic(3);
    const fa = typeApp(f, a);
    const fb = typeApp(f, b);
    env.set("*>", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(fa, fn(fb, fb)),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set("++", {
      vars: [(a as { id: number }).id],
      type: fn(
        typeConApp("List", a),
        fn(typeConApp("List", a), typeConApp("List", a)),
      ),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set("concat", {
      vars: [(a as { id: number }).id],
      type: fn(
        typeConApp("List", typeConApp("List", a)),
        typeConApp("List", a),
      ),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set("id", { vars: [(a as { id: number }).id], type: fn(a, a) });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("const", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(a, fn(b, a)),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("$", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(fn(a, b), fn(a, b)),
    });
  }
  {
    const [a, b, c] = polymorphic(3);
    env.set(".", {
      vars: [
        (a as { id: number }).id,
        (b as { id: number }).id,
        (c as { id: number }).id,
      ],
      type: fn(fn(b, c), fn(fn(a, b), fn(a, c))),
    });
  }
  {
    const [a, b, c] = polymorphic(3);
    env.set("flip", {
      vars: [
        (a as { id: number }).id,
        (b as { id: number }).id,
        (c as { id: number }).id,
      ],
      type: fn(fn(a, fn(b, c)), fn(b, fn(a, c))),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("map", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(fn(a, b), fn(typeConApp("List", a), typeConApp("List", b))),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("foldr", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(fn(a, fn(b, b)), fn(b, fn(typeConApp("List", a), b))),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set("last", {
      vars: [(a as { id: number }).id],
      type: fn(typeConApp("List", a), a),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set("init", {
      vars: [(a as { id: number }).id],
      type: fn(typeConApp("List", a), typeConApp("List", a)),
    });
  }
  {
    const [t, a] = polymorphic(2);
    env.set("toList", {
      vars: [(t as { id: number }).id, (a as { id: number }).id],
      type: fn(typeApp(t, a), typeConApp("List", a)),
    });
  }
  env.set("isSpace", {
    vars: [],
    type: fn({ tag: "con", name: "Char" }, bool),
  });
  env.set("subtract", { vars: [], type: fn(int, fn(int, int)) });
  env.set("web", { vars: [], type: bool });
  env.set("mts", { vars: [], type: bool });
  env.set("bts", { vars: [], type: bool });
  env.set("undefined", { vars: [], type: context.fresh() });
  {
    const [f, t, a, b] = polymorphic(4);
    env.set("traverse", {
      vars: [
        (f as { id: number }).id,
        (t as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(
        fn(a, typeApp(f, b)),
        fn(typeApp(t, a), typeApp(f, typeApp(t, b))),
      ),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set("show", { vars: [(a as { id: number }).id], type: fn(a, string) });
  }
    env.set("sum", {
      vars: [],
      type: fn(typeConApp("List", int), int),
    });
    env.set("fromEnum", { vars: [], type: fn({ tag: "con", name: "Char" }, int) });
  {
    const [a] = polymorphic(1);
    env.set("elem", {
      vars: [(a as { id: number }).id],
      type: fn(a, fn(typeConApp("List", a), bool)),
    });
    env.set("filter", {
      vars: [(a as { id: number }).id],
      type: fn(fn(a, bool), fn(typeConApp("List", a), typeConApp("List", a))),
    });
    env.set("div", { vars: [], type: fn(int, fn(int, int)) });
    env.set("mod", { vars: [], type: fn(int, fn(int, int)) });
    env.set("quot", { vars: [], type: fn(int, fn(int, int)) });
    env.set("rem", { vars: [], type: fn(int, fn(int, int)) });
    env.set("even", { vars: [], type: fn(int, bool) });
    env.set("odd", { vars: [], type: fn(int, bool) });
    env.set("divMod", {
      vars: [],
      type: fn(int, fn(int, typeApp(typeApp({ tag: "con", name: "Tuple2" }, int), int))),
    });
    env.set("quotRem", {
      vars: [],
      type: fn(int, fn(int, typeApp(typeApp({ tag: "con", name: "Tuple2" }, int), int))),
    });
    env.set("any", {
      vars: [(a as { id: number }).id],
      type: fn(fn(a, bool), fn(typeConApp("List", a), bool)),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set("min", {
      vars: [(a as { id: number }).id],
      type: fn(a, fn(a, a)),
    });
    env.set("max", {
      vars: [(a as { id: number }).id],
      type: fn(a, fn(a, a)),
    });
    env.set("succ", { vars: [(a as { id: number }).id], type: fn(a, a) });
    env.set("pred", { vars: [(a as { id: number }).id], type: fn(a, a) });
    env.set("dropWhile", {
      vars: [(a as { id: number }).id],
      type: fn(fn(a, bool), fn(typeConApp("List", a), typeConApp("List", a))),
    });
    env.set("drop", {
      vars: [(a as { id: number }).id],
      type: fn(int, fn(typeConApp("List", a), typeConApp("List", a))),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("concatMap", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(
        fn(a, typeConApp("List", b)),
        fn(typeConApp("List", a), typeConApp("List", b)),
      ),
    });
    env.set("zip", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(
        typeConApp("List", a),
        fn(typeConApp("List", b), typeConApp("List", typeApp(typeApp({ tag: "con", name: "Tuple2" }, a), b))),
      ),
    });
  }
  {
    const [a] = polymorphic(1);
    const listA = typeConApp("List", a);
    env.set("enumFrom", {
      vars: [(a as { id: number }).id],
      type: fn(a, listA),
    });
    env.set("enumFromTo", {
      vars: [(a as { id: number }).id],
      type: fn(a, fn(a, listA)),
    });
    env.set("enumFromThen", {
      vars: [(a as { id: number }).id],
      type: fn(a, fn(a, listA)),
    });
    env.set("enumFromThenTo", {
      vars: [(a as { id: number }).id],
      type: fn(a, fn(a, fn(a, listA))),
    });
  }
  {
    const [f, a, b] = polymorphic(3);
    const fa = typeApp(f, a);
    env.set("mapM", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(
        fn(a, typeApp(f, b)),
        fn(typeConApp("List", a), typeApp(f, typeConApp("List", b))),
      ),
    });
    env.set("sequence", {
      vars: [(f as { id: number }).id, (a as { id: number }).id],
      type: fn(
        typeConApp("List", typeApp(f, a)),
        typeApp(f, typeConApp("List", a)),
      ),
    });
    env.set("traverse_", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(
        fn(a, typeApp(f, b)),
        fn(typeConApp("List", a), typeApp(f, { tag: "con", name: "()" })),
      ),
    });
  }
  {
    const [a, b, c] = polymorphic(3);
    env.set("uncurry", {
      vars: [
        (a as { id: number }).id,
        (b as { id: number }).id,
        (c as { id: number }).id,
      ],
      type: fn(
        fn(a, fn(b, c)),
        fn(typeApp(typeApp({ tag: "con", name: "Tuple2" }, a), b), c),
      ),
    });
    env.set("seq", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(a, fn(b, b)),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("|>", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(a, fn(fn(a, b), b)),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("mapM_", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(
        fn(a, typeConApp("IO", b)),
        fn(typeConApp("List", a), typeConApp("IO", { tag: "con", name: "()" })),
      ),
    });
    env.set("sequence_", {
      vars: [(a as { id: number }).id],
      type: fn(
        typeConApp("List", typeConApp("IO", a)),
        typeConApp("IO", { tag: "con", name: "()" }),
      ),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("maybe", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(b, fn(fn(a, b), fn(typeConApp("Maybe", a), b))),
    });
  }
  {
    const [a, b, c] = polymorphic(3);
    env.set("either", {
      vars: [
        (a as { id: number }).id,
        (b as { id: number }).id,
        (c as { id: number }).id,
      ],
      type: fn(
        fn(a, c),
        fn(fn(b, c), fn(typeApp(typeConApp("Either", a), b), c)),
      ),
    });
  }
  {
    const [a] = polymorphic(1);
    env.set(":", {
      vars: [(a as { id: number }).id],
      type: fn(a, fn(typeConApp("List", a), typeConApp("List", a))),
    });
    env.set("!!", {
      vars: [(a as { id: number }).id],
      type: fn(typeConApp("List", a), fn(int, a)),
    });
  }
  {
    const [a, b] = polymorphic(2);
    env.set("fromIntegral", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(a, b),
    });
    env.set("realToFrac", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(a, b),
    });
  }
  env.set("isNaN", {
    vars: [],
    type: fn({ tag: "con", name: "Double" }, bool),
  });
  {
    const [a, b] = polymorphic(2);
    const pair = typeApp(typeApp({ tag: "con", name: "Tuple2" }, a), b);
    env.set("fst", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(pair, a),
    });
    env.set("snd", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(pair, b),
    });
    env.set("(,)", {
      vars: [(a as { id: number }).id, (b as { id: number }).id],
      type: fn(a, fn(b, pair)),
    });
  }
  // Higher-kinded constructor variables keep the boot surface useful for
  // Maybe, parser transformers, lists, and IO alike.  Restricting these to
  // IO causes cascading false errors throughout ordinary library code.
  {
    const [f, a] = polymorphic(2);
    const fa = typeApp(f, a);
    env.set("pure", {
      vars: [(f as { id: number }).id, (a as { id: number }).id],
      type: fn(a, fa),
    });
    env.set("return", {
      vars: [(f as { id: number }).id, (a as { id: number }).id],
      type: fn(a, fa),
    });
  }
  {
    const [f, a, b] = polymorphic(3);
    const fa = typeApp(f, a);
    const fb = typeApp(f, b);
    env.set(">>=", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(fa, fn(fn(a, fb), fb)),
    });
    env.set("=<<", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(fn(a, fb), fn(fa, fb)),
    });
    env.set(">>", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(fa, fn(fb, fb)),
    });
  }
  {
    const [f, a, b] = polymorphic(3);
    const fa = typeApp(f, a);
    const fb = typeApp(f, b);
    env.set("<$>", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(fn(a, b), fn(fa, fb)),
    });
    env.set("fmap", {
      vars: [
        (f as { id: number }).id,
        (a as { id: number }).id,
        (b as { id: number }).id,
      ],
      type: fn(fn(a, b), fn(fa, fb)),
    });
  }
  return env;
}
function foreignType(
  declaration: ForeignDeclaration,
  context: Inferencer,
): Type {
  // Unlike ordinary foreign imports, compiler/runtime primitives commonly
  // quantify a Haskell type variable (`a -> IO JSVal`).  Parse the complete
  // signature at once so the same variable is shared across arguments and
  // result instead of treating it as an unsupported opaque atom.
  // This parser covers JS values, lists, tuples, callback arguments, effects,
  // and quantified variables used by the supported JavaScript FFI surface.
  // Keeping one parse for the whole signature also preserves shared type
  // variables across its arguments and result.
  return parseSignature(declaration.signature.join(" -> "), context);
  /* Legacy atom fallback retained below as a reference while broader FFI
   * syntax is introduced. */
  const primitive = (source: string): Type => {
    const normalized = source.replace(/\s+/g, " ").trim();
    if (normalized === "Int" || normalized === "Integer") return int;
    if (normalized === "String") return string;
    if (normalized === "Bool") return bool;
    if (normalized === "()") return { tag: "con", name: "()" };
    // FFI results retain their effect wrapper as an opaque type at this
    // boundary.  This accepts the ordinary GHCJS `IO JSVal`, `IO Int`, and
    // tuple-return signatures while the typed Core IO representation is
    // introduced; it does not erase an effect into a pure result.
    if (/^IO\s+/.test(normalized))
      return typeConApp("IO", primitive(normalized.slice(3)));
    // Opaque JS and user data values may pass through the FFI without pretending
    // that they are interchangeable with Haskell primitives.
    if (/^[A-Z][A-Za-z0-9_.]*$/.test(normalized) || /^\(.+\)$/.test(normalized))
      return { tag: "con", name: normalized };
    throw new Error(
      `Unsupported foreign-import type ${JSON.stringify(normalized)}`,
    );
  };
  if (declaration.signature.length !== declaration.arity + 1)
    throw new Error(
      `Malformed foreign-import signature for ${declaration.name}`,
    );
  let type = primitive(declaration.signature.at(-1)!);
  for (const argument of declaration.signature.slice(0, -1).reverse())
    type = fn(primitive(argument), type);
  return type;
}
class Inferencer {
  diagnostics: Diagnostic[] = [];
  private next = 0;
  private substitution: Substitution = new Map();
  fresh(): Type {
    return { tag: "var", id: this.next++ };
  }
  apply(type: Type): Type {
    if (type.tag === "var" && this.substitution.has(type.id)) {
      const resolved = this.apply(this.substitution.get(type.id)!);
      this.substitution.set(type.id, resolved);
      return resolved;
    }
    if (type.tag === "app")
      return typeApp(this.apply(type.fn), this.apply(type.arg));
    if (type.tag === "fn")
      return fn(this.apply(type.from), this.apply(type.to));
    return type;
  }
  unify(left: Type, right: Type): void {
    const normalize = (type: Type): Type => {
      if (type.tag !== "app") return type;
      const fnPart = normalize(type.fn);
      const arg = normalize(type.arg);
      if (
        fnPart.tag === "app" &&
        fnPart.fn.tag === "con" &&
        fnPart.fn.name === "Lens" &&
        fnPart.arg.tag !== "app"
      )
        return typeApp(
          typeApp({ tag: "con", name: "LensCore" }, arg),
          fnPart.arg,
        );
      if (fnPart.tag === "app" && fnPart.fn.tag === "con" && fnPart.fn.name === "App") {
        return typeApp(
          typeApp(
            typeApp(typeApp({ tag: "con", name: "Component" }, { tag: "con", name: "()" }), { tag: "con", name: "()" }),
            fnPart.arg,
          ),
          arg,
        );
      }
      return typeApp(fnPart, arg);
    };
    const a = normalize(this.apply(left));
    const b = normalize(this.apply(right));
    if (a.tag === "var") return this.bind(a.id, b);
    if (b.tag === "var") return this.bind(b.id, a);
    const baseName = (name: string) =>
      name.includes(".") ? name.slice(name.lastIndexOf(".") + 1) : name;
    if (
      a.tag === "con" &&
      b.tag === "con" &&
      (a.name === b.name ||
        baseName(a.name) === baseName(b.name) ||
        (["String", "JSString", "Text"].includes(baseName(a.name)) &&
          ["String", "JSString", "Text"].includes(baseName(b.name))) ||
        (["Int", "Integer", "Double", "Float", "Word"].includes(baseName(a.name)) &&
          ["Int", "Integer", "Double", "Float", "Word"].includes(baseName(b.name))))
    )
      return;
    const head = (type: Type): string | undefined => {
      let current = type;
      while (current.tag === "app") current = current.fn;
      return current.tag === "con" ? current.name : undefined;
    };
    const stringNames = ["String", "JSString", "Text"];
    const asListChar = (type: Type): Type | undefined =>
      type.tag === "con" && stringNames.includes(baseName(type.name))
        ? typeConApp("List", { tag: "con", name: "Char" })
        : undefined;
    const isListLike = (type: Type): boolean => {
      if (type.tag !== "app") return false;
      const constructor = head(type);
      return (
        type.fn.tag === "var" ||
        constructor === "List" ||
        constructor === "[]"
      );
    };
    const listCharA = asListChar(a);
    const listCharB = asListChar(b);
    if (listCharA && isListLike(b)) return this.unify(listCharA, b);
    if (listCharB && isListLike(a)) return this.unify(a, listCharB);
    if (
      (baseName(head(a) ?? "") === "Style" && head(b) === "Tuple2") ||
      (baseName(head(b) ?? "") === "Style" && head(a) === "Tuple2")
    )
      return;
    if (
      (a.tag === "con" && a.name === "Object" && head(b) === "Map") ||
      (b.tag === "con" && b.name === "Object" && head(a) === "Map")
    )
      return;
    if (a.tag === "app" && b.tag === "app") {
      this.unify(a.fn, b.fn);
      this.unify(a.arg, b.arg);
      return;
    }
    if (a.tag === "fn" && b.tag === "fn") {
      this.unify(a.from, b.from);
      this.unify(a.to, b.to);
      return;
    }
    throw new Error(`Cannot unify ${show(a)} with ${show(b)}`);
  }
  private bind(id: number, type: Type) {
    if (type.tag === "var" && type.id === id) return;
    if (free(type).has(id))
      throw new Error(`Occurs check failed: t${id} appears in ${show(type)}`);
    this.substitution.set(id, type);
  }
  value(declaration: ValueDeclaration, environment: Environment): Type {
    const placeholder = environment.get(declaration.name)?.type ?? this.fresh();
    const local = new Map(environment);
    local.set(declaration.name, { vars: [], type: placeholder });
    const arity = declaration.equations[0]?.patterns.length ?? 0;
    const parameterTypes = Array.from({ length: arity }, () => this.fresh());
    const resultType = this.fresh();
    for (const equation of declaration.equations) {
      if (equation.patterns.length !== arity)
        throw new Error(
          `Function ${declaration.name} has equations with different arities`,
        );
      const bodyEnvironment = new Map(local);
      equation.patterns.forEach((pattern, index) =>
        this.pattern(pattern, parameterTypes[index], bodyEnvironment),
      );
      const scoped = this.bindings(equation.whereBindings, bodyEnvironment);
      for (const guard of equation.guards) {
        if (guard.condition)
          this.unify(this.expr(guard.condition, scoped), bool);
        this.unify(resultType, this.expr(guard.body, scoped));
      }
    }
    let inferred = this.apply(resultType);
    for (const parameter of [...parameterTypes].reverse())
      inferred = fn(this.apply(parameter), inferred);
    this.unify(placeholder, inferred);
    const result = this.apply(placeholder);
    environment.set(declaration.name, generalize(environment, result, this));
    return result;
  }
  expr(expression: Expr, environment: Environment): Type {
    switch (expression.tag) {
      // This checker has no reader for a written signature; the ascription is
      // honoured by `src/elaborate.ts`, which is the pass on the compiler path.
      case "annot":
        return this.expr(expression.expr, environment);
      case "int":
        return int;
      case "double":
        return { tag: "con", name: "Double" };
      case "string":
        return string;
      case "char":
        return { tag: "con", name: "Char" };
      case "unit":
        return { tag: "con", name: "()" };
      case "tuple": {
        const items = expression.items.map((item) =>
          this.expr(item, environment),
        );
        return items.reduce<Type>((result, item) => typeApp(result, item), {
          tag: "con",
          name: `Tuple${items.length}`,
        });
      }
      case "list": {
        const element = this.fresh();
        for (const item of expression.items)
          this.unify(element, this.expr(item, environment));
        return typeConApp("List", element);
      }
      case "listComp": {
        const local = new Map(environment);
        for (const qualifier of expression.qualifiers) {
          if (qualifier.tag === "generator") {
            const element = this.fresh();
            this.unify(
              this.expr(qualifier.source, local),
              typeConApp("List", element),
            );
            this.pattern(qualifier.pattern, element, local);
          } else this.unify(this.expr(qualifier.condition, local), bool);
        }
        return typeConApp("List", this.expr(expression.body, local));
      }
      case "jsQuote": {
        for (const name of expression.body.matchAll(
          /\$\{([A-Za-z_][A-Za-z0-9_']*)\}/g,
        )) {
          const scheme = environment.get(name[1]!);
          if (scheme) instantiate(scheme, this);
          else throw new Error(`Not in scope: ${name[1]}`);
        }
        return typeConApp("IO", this.fresh());
      }
      case "record": {
        let type = this.expr(
          { tag: "var", name: expression.constructor, span: expression.span },
          environment,
        );
        for (const field of expression.fields) {
          const result = this.fresh();
          this.unify(type, fn(this.expr(field.value, environment), result));
          type = this.apply(result);
        }
        return type;
      }
      case "recordUpdate": {
        const base = this.expr(expression.base, environment);
        for (const field of expression.fields)
          this.expr(field.value, environment);
        return base;
      }
      case "var": {
        const scheme = environment.get(expression.name);
        if (!scheme) throw new Error(`Not in scope: ${expression.name}`);
        return instantiate(scheme, this);
      }
      case "lambda": {
        const parameter = this.fresh();
        const local = new Map(environment);
        local.set(expression.parameter, { vars: [], type: parameter });
        return fn(parameter, this.expr(expression.body, local));
      }
      case "lambdaCase": {
        const parameter = this.fresh();
        const result = this.fresh();
        for (const alternative of expression.alternatives) {
          const local = new Map(environment);
          this.pattern(alternative.pattern, parameter, local);
          for (const patternGuard of alternative.patternGuards ?? []) {
            const source = this.expr(patternGuard.source, local);
            this.pattern(patternGuard.pattern, source, local);
          }
          if (alternative.guard)
            this.unify(this.expr(alternative.guard, local), bool);
          this.unify(result, this.expr(alternative.body, local));
        }
        return fn(parameter, this.apply(result));
      }
      case "let":
        return this.expr(
          expression.body,
          this.bindings(expression.bindings, environment),
        );
      case "do": {
        let result: Type = typeConApp("IO", { tag: "con", name: "()" });
        let local = new Map(environment);
        for (const statement of expression.statements) {
          if (statement.tag === "bind") {
            const value = this.expr(statement.source, local);
            this.pattern(statement.pattern, this.ioPayload(value), local);
            result = value;
          } else if (statement.tag === "let")
            local = this.bindings(statement.bindings, local);
          else result = this.expr(statement.expr, local);
        }
        return result;
      }
      case "app": {
        const functionType = this.expr(expression.fn, environment);
        const argumentType = this.expr(expression.arg, environment);
        const result = this.fresh();
        this.unify(functionType, fn(argumentType, result));
        return this.apply(result);
      }
      case "if": {
        const condition = this.expr(expression.condition, environment);
        this.unify(condition, bool);
        const yes = this.expr(expression.thenBranch, environment);
        const no = this.expr(expression.elseBranch, environment);
        this.unify(yes, no);
        return this.apply(yes);
      }
      case "case": {
        const subject = this.expr(expression.subject, environment);
        const result = this.fresh();
        for (const alternative of expression.alternatives) {
          const local = new Map(environment);
          this.pattern(alternative.pattern, subject, local);
          for (const patternGuard of alternative.patternGuards ?? []) {
            const source = this.expr(patternGuard.source, local);
            this.pattern(patternGuard.pattern, source, local);
          }
          if (alternative.guard)
            this.unify(this.expr(alternative.guard, local), bool);
          this.unify(result, this.expr(alternative.body, local));
        }
        return this.apply(result);
      }
    }
  }
  /** `do` binds the payload of `IO a`.  The non-IO fallback preserves the
   * prototype's historical pure-do fixtures while ordinary Haskell source
   * gains correct effect payload inference. */
  private ioPayload(type: Type): Type {
    const applied = this.apply(type);
    if (applied.tag === "app") return applied.arg;
    return applied;
  }
  private bindings(
    bindings: import("./ast.js").LocalBinding[],
    environment: Environment,
  ): Environment {
    const local = new Map(environment);
    const functions = bindings.filter((binding) => !binding.name.startsWith("__pattern_"));
    const patterns = bindings.filter((binding) => binding.name.startsWith("__pattern_"));
    const placeholders = new Map(
      functions.map((binding) => [binding.name, this.fresh()]),
    );
    for (const [name, type] of placeholders)
      local.set(name, { vars: [], type });
    for (const binding of functions) {
      const arity = binding.patterns.length;
      const parameterTypes = Array.from({ length: arity }, () => this.fresh());
      const bodyEnvironment = new Map(local);
      binding.patterns.forEach((pattern, index) =>
        this.pattern(pattern, parameterTypes[index]!, bodyEnvironment),
      );
      const scoped = this.bindings(binding.whereBindings ?? [], bodyEnvironment);
      let result = this.fresh();
      for (const guard of binding.guards ?? [{ body: binding.value }]) {
        if (guard.condition)
          this.unify(this.expr(guard.condition, scoped), bool);
        this.unify(result, this.expr(guard.body ?? binding.value, scoped));
      }
      for (const parameter of [...parameterTypes].reverse())
        result = fn(this.apply(parameter), result);
      this.unify(placeholders.get(binding.name)!, result);
    }
    for (const [name, type] of placeholders)
      local.set(name, generalize(environment, this.apply(type), this));
    for (const binding of patterns) {
      const rhs = this.expr(binding.value, local);
      const pattern = binding.patterns[0];
      if (pattern) this.pattern(pattern, rhs, local);
    }
    return local;
  }
  private pattern(
    pattern: Pattern,
    expected: Type,
    environment: Environment,
  ): void {
    switch (pattern.tag) {
      case "wild":
        return;
      case "var":
        environment.set(pattern.name, { vars: [], type: expected });
        return;
      case "as":
        environment.set(pattern.name, { vars: [], type: expected });
        this.pattern(pattern.pattern, expected, environment);
        return;
      case "int":
        this.unify(expected, int);
        return;
      case "string":
        this.unify(expected, string);
        return;
      case "char":
        this.unify(expected, { tag: "con", name: "Char" });
        return;
      case "record": {
        let constructorType = instantiate(
          environment.get(pattern.name) ?? { vars: [], type: expected },
          this,
        );
        for (const field of pattern.fields) {
          const fieldType = this.fresh();
          if (constructorType.tag === "fn") constructorType = constructorType.to;
          this.pattern(field.pattern, fieldType, environment);
        }
        this.unify(expected, constructorType);
        return;
      }
      case "con": {
        if (pattern.name === "[]") {
          this.unify(expected, typeConApp("List", this.fresh()));
          return;
        }
        if (pattern.name === "()") {
          this.unify(expected, { tag: "con", name: "()" });
          return;
        }
        if (/^\(,+\)$/.test(pattern.name)) {
          const items = pattern.args.map(() => this.fresh());
          const tuple = items.reduce<Type>(
            (result, item) => typeApp(result, item),
            { tag: "con", name: `Tuple${pattern.args.length}` },
          );
          this.unify(expected, tuple);
          pattern.args.forEach((argument, index) =>
            this.pattern(argument, items[index], environment),
          );
          return;
        }
        if (pattern.name === ":") {
          const element = this.fresh();
          this.unify(expected, typeConApp("List", element));
          this.pattern(pattern.args[0], element, environment);
          this.pattern(
            pattern.args[1],
            typeConApp("List", element),
            environment,
          );
          return;
        }
        let constructorType = instantiate(
          environment.get(pattern.name) ??
            (() => {
              throw new Error(`Not in scope: ${pattern.name}`);
            })(),
          this,
        );
        for (const argument of pattern.args) {
          const argumentType = this.fresh();
          const rest = this.fresh();
          this.unify(constructorType, fn(argumentType, rest));
          this.pattern(argument, argumentType, environment);
          constructorType = this.apply(rest);
        }
        this.unify(expected, constructorType);
        return;
      }
    }
  }
}
function free(type: Type): Set<number> {
  const result = new Set<number>();
  const visit = (value: Type) => {
    if (value.tag === "var") result.add(value.id);
    else if (value.tag === "app") {
      visit(value.fn);
      visit(value.arg);
    } else if (value.tag === "fn") {
      visit(value.from);
      visit(value.to);
    }
  };
  visit(type);
  return result;
}
function freeScheme(scheme: Scheme): Set<number> {
  const result = free(scheme.type);
  for (const variable of scheme.vars) result.delete(variable);
  return result;
}
function generalize(
  environment: Environment,
  type: Type,
  inferencer: Inferencer,
): Scheme {
  const vars = free(inferencer.apply(type));
  for (const scheme of environment.values())
    for (const variable of freeScheme(scheme)) vars.delete(variable);
  return { vars: [...vars], type: inferencer.apply(type) };
}
function instantiate(scheme: Scheme, inferencer: Inferencer): Type {
  const mapping = new Map(
    scheme.vars.map((variable) => [variable, inferencer.fresh()]),
  );
  const visit = (type: Type): Type =>
    type.tag === "var"
      ? (mapping.get(type.id) ?? type)
      : type.tag === "app"
        ? typeApp(visit(type.fn), visit(type.arg))
        : type.tag === "fn"
          ? fn(visit(type.from), visit(type.to))
          : type;
  return visit(scheme.type);
}
function show(type: Type): string {
  if (type.tag === "var") return `t${type.id}`;
  if (type.tag === "con") return type.name;
  if (type.tag === "app") {
    const left = type.fn.tag === "fn" ? `(${show(type.fn)})` : show(type.fn);
    const right =
      type.arg.tag === "app" || type.arg.tag === "fn"
        ? `(${show(type.arg)})`
        : show(type.arg);
    return `${left} ${right}`;
  }
  const left =
    type.from.tag === "fn" ? `(${show(type.from)})` : show(type.from);
  return `${left} -> ${show(type.to)}`;
}
