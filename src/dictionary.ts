import type { ClassDeclaration, ClassMemberSlice, InstanceDeclaration, Module, Span, ValueDeclaration } from './ast.js';
import { parseModule } from './parser.js';

/** A class method or instance implementation recovered from the lossless
 * member slice.  `tokens` intentionally remain available to the Core parser:
 * type families, default signatures, and ordinary equations do not share one
 * surface grammar. */
export interface DictionaryMember {
  name: string;
  kind: 'signature' | 'method' | 'associatedType';
  tokens: readonly string[];
  span: Span;
}

export interface DictionaryClass {
  module: string;
  name: string;
  parameters: readonly string[];
  members: readonly DictionaryMember[];
}

export interface DictionaryInstance {
  module: string;
  head: string;
  methods: readonly DictionaryMember[];
  values: readonly ValueDeclaration[];
}

export interface DictionaryTable {
  classes: ReadonlyMap<string, DictionaryClass>;
  instances: readonly DictionaryInstance[];
}
export interface DictionarySelection { instance: DictionaryInstance; className: string; target: string; substitutions: ReadonlyMap<string, string>; }

/** Build a module-qualified class/instance table.  It does not choose an
 * instance yet—that belongs to constraint solving—but gives later phases a
 * stable, source-preserving input for that selection. */
export function collectDictionaries(modules: readonly Module[]): DictionaryTable {
  const classes = new Map<string, DictionaryClass>(); const instances: DictionaryInstance[] = [];
  for (const module of modules) for (const declaration of module.declarations) {
    if (declaration.tag === 'class') classes.set(`${module.name}.${declaration.name}`, { module: module.name, name: declaration.name, parameters: declaration.parameters, members: classMembers(declaration) });
    if (declaration.tag === 'instance') instances.push({ module: module.name, head: declaration.head, methods: instanceMembers(declaration), values: instanceMethodValues(declaration, `<${module.name}:instance>`) });
  }
  return { classes, instances };
}

function normalized(source: string): string { return source.replace(/\s+/g, ' ').replace(/\(\s+/g, '(').replace(/\s+\)/g, ')').trim(); }
/** Extract a class and target after dropping a simple instance context. */
export function instanceHead(head: string): { className: string; target: string } | undefined {
  const constrained = normalized(head).split(/\s*=>\s*/).at(-1) ?? '';
  const match = /^([A-Z][A-Za-z0-9_.']*)\s+(.+)$/.exec(constrained);
  return match ? { className: match[1], target: normalized(match[2]) } : undefined;
}
type HeadType = { tag: 'var'; name: string } | { tag: 'con'; name: string } | { tag: 'app'; fn: HeadType; arg: HeadType };
function parseHeadType(source: string): HeadType | undefined {
  const tokens = source.match(/[A-Za-z_][A-Za-z0-9_.']*|\[|\]|\(|\)|,/g) ?? []; let index = 0;
  const atom = (): HeadType | undefined => { const token = tokens[index++]; if (!token) return undefined; if (token === '[') { const item = application(); if (tokens[index] === ']') index++; return item ? { tag: 'app', fn: { tag: 'con', name: 'List' }, arg: item } : undefined; } if (token === '(') { const item = application(); if (tokens[index] === ')') index++; return item; } return /^[a-z]/.test(token) ? { tag: 'var', name: token } : { tag: 'con', name: token }; };
  const application = (): HeadType | undefined => { let value = atom(); while (value && index < tokens.length && ![')', ']', ','].includes(tokens[index])) { const arg = atom(); if (!arg) break; value = { tag: 'app', fn: value, arg }; } return value; };
  const result = application(); return result && index === tokens.length ? result : undefined;
}
function showHead(type: HeadType): string { return type.tag === 'app' ? `${showHead(type.fn)} ${showHead(type.arg)}` : type.name; }
function matchHead(pattern: HeadType, target: HeadType, substitutions: Map<string, HeadType>): boolean { if (pattern.tag === 'var') { const previous = substitutions.get(pattern.name); if (!previous) { substitutions.set(pattern.name, target); return true; } return showHead(previous) === showHead(target); } if (pattern.tag === 'con' || target.tag === 'con') return pattern.tag === 'con' && target.tag === 'con' && pattern.name === target.name; if (pattern.tag !== 'app' || target.tag !== 'app') return false; return matchHead(pattern.fn, target.fn, substitutions) && matchHead(pattern.arg, target.arg, substitutions); }
/** Structural matching handles ordinary parameterized instance heads.  A
 * non-unique result remains unresolved so overlap checks stay conservative. */
export function selectInstance(table: DictionaryTable, className: string, target: string): DictionarySelection | undefined {
  const expected = normalized(target); const targetType = parseHeadType(expected); if (!targetType) return undefined;
  const matches = table.instances.flatMap(instance => { const parsed = instanceHead(instance.head); if (parsed?.className !== className) return []; const pattern = parseHeadType(parsed.target); if (!pattern) return []; const substitutions = new Map<string, HeadType>(); return matchHead(pattern, targetType, substitutions) ? [{ instance, substitutions: new Map([...substitutions].map(([name, type]) => [name, showHead(type)])) }] : []; });
  return matches.length === 1 ? { instance: matches[0].instance, className, target: expected, substitutions: matches[0].substitutions } : undefined;
}

// `@` is not an operator on an equation's left-hand side, it is an as-pattern:
// `fmap f r@R { body = b } = ...` was read as a definition of `@`, so the
// instance had no `fmap` at all. No Haskell operator can be named `@` or `..`.
function symbolic(token: string | undefined): boolean { return !!token && /^[!#$%&*+./<=>?@\\^|~:-]+$/.test(token) && !['=', '::', '=>', '->', '@', '..'].includes(token); }

/** Class bodies chiefly carry signatures, while preserving type-family lines
 * separately.  This keeps method identity stable before constraints and
 * dictionaries are elaborated. */
export function classMembers(declaration: ClassDeclaration): DictionaryMember[] {
  return declaration.rawMembers.flatMap(slice => member(slice, true));
}

/** Instances may use prefix equations (`at key = ...`) or infix equations
 * (`Options a <> Options b = ...`).  Both identify a method without parsing
 * the RHS prematurely. */
export function instanceMembers(declaration: InstanceDeclaration): DictionaryMember[] {
  return declaration.rawMembers.flatMap(slice => member(slice, false));
}

/** Recover instance equations through the ordinary declaration parser.  Infix
 * instance equations are normalized to Haskell's parenthesized prefix binder
 * form before parsing; this is a syntax-preserving transformation, not an
 * application-specific rewrite.  Associated types deliberately return no
 * value declaration and remain available through `instanceMembers`. */
export function instanceMethodValues(declaration: InstanceDeclaration, file = '<instance>'): ValueDeclaration[] {
  const values: ValueDeclaration[] = [];
  for (const item of instanceMembers(declaration)) {
    if (item.kind !== 'method') continue;
    const equals = item.tokens.indexOf('='); if (equals < 0) continue;
    // The body starts at the first guard, not at the first `=`, so a guarded
    // infix equation keeps all of its guards.
    const end = lhsEnd(item.tokens, equals);
    const operatorAt = infixOperatorAt(item.tokens, end);
    let sourceTokens = item.tokens;
    if (operatorAt >= 0) {
      const left = item.tokens.slice(0, operatorAt); const right = item.tokens.slice(operatorAt + 1, end); const body = item.tokens.slice(end);
      sourceTokens = ['(', item.name, ')', '(', ...left, ')', '(', ...right, ')', ...body];
    }
    const parsed = parseModule(`module Dictionary where\n${sourceTokens.join(' ')}\n`, file);
    if (parsed.diagnostics.length) continue;
    const value = parsed.module?.ast.declarations.find((candidate): candidate is ValueDeclaration => candidate.tag === 'value');
    if (!value) continue;
    // Layout puts each equation of a multi-equation member in its own slice, so
    // the equations arrive as separate declarations and have to be rejoined -
    // otherwise `f A = ...` / `f B = ...` would keep only the last equation.
    const existing = values.find((candidate) => candidate.name === value.name);
    if (existing) existing.equations = [...existing.equations, ...value.equations];
    else values.push(value);
  }
  return values;
}

/** Infix instance equations are `pat <> pat = ...`. Record wildcards (`{..}`)
 * and symbols nested in `{ }` / `( )` / `[ ]` are not the method operator. */
/** Where the left-hand side of an equation stops.  A depth-zero `|` is a
 * guard - `|` is reserved, so it can never be a user operator - and every
 * token from there on belongs to the right-hand side, not to the binder.
 * Without this, `toJSON x | p = a | otherwise = b` looks like a definition of
 * an infix operator named `|`, and the member is dropped. */
function lhsEnd(tokens: readonly string[], equals: number): number {
  let depth = 0;
  for (let i = 0; i < equals; i++) {
    const token = tokens[i];
    if (token === '{' || token === '(' || token === '[') depth++;
    else if (token === '}' || token === ')' || token === ']') depth = Math.max(0, depth - 1);
    else if (depth === 0 && token === '|') return i;
  }
  return equals;
}

function infixOperatorAt(tokens: readonly string[], equals: number): number {
  let depth = 0;
  for (let i = 0; i < equals; i++) {
    const token = tokens[i];
    if (token === '{' || token === '(' || token === '[') depth++;
    else if (token === '}' || token === ')' || token === ']') depth = Math.max(0, depth - 1);
    else if (depth === 0 && symbolic(token) && token !== '..') return i;
  }
  return -1;
}

function member(slice: ClassMemberSlice, classBody: boolean): DictionaryMember[] {
  const tokens = slice.tokens;
  if (!tokens.length) return [];
  if (tokens[0] === 'type' || (tokens[0] === 'type' && tokens[1] === 'family')) return [{ name: tokens[1] ?? '<associated type>', kind: 'associatedType', tokens, span: slice.span }];
  const signature = tokens.indexOf('::');
  const equals = tokens.indexOf('=');
  // Instance RHS expressions may contain local type annotations (for
  // example `readHex h :: [(Word64, String)]`).  In that case the first
  // `::` is not a method signature; the top-level equation is identified by
  // its `=`.  Class bodies still treat `::` as a declaration signature.
  if (signature > 0 && (classBody || equals < 0)) {
    const name = binder(tokens.slice(0, signature));
    return name ? [{ name, kind: 'signature', tokens, span: slice.span }] : [];
  }
  if (equals < 0) return [];
  const name = binder(tokens.slice(0, lhsEnd(tokens, equals)));
  if (!name) return [];
  return [{ name, kind: classBody ? 'signature' : 'method', tokens, span: slice.span }];
}

function binder(lhs: readonly string[]): string | undefined {
  // `(<=)` and ordinary `method x` prefix forms.
  if (lhs[0] === '(' && symbolic(lhs[1]) && lhs[2] === ')') return lhs[1];
  if (lhs[0] && /^[A-Za-z_][A-Za-z0-9_'.]*$/.test(lhs[0])) {
    // Constructor-pattern/infix instance equations put the operation after
    // the left pattern, so prefer a symbolic binder when present.
    return lhs.find((token) => symbolic(token) && token !== "..") ?? lhs[0];
  }
  return lhs.find(symbolic);
}
