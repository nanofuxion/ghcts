export interface Span { start: number; end: number; line: number; column: number; }
/** `voidRep` on a binder means its type is zero JS values wide - the erased
 * `RealWorld` state token, and nothing else. `src/elaborate.ts` sets it from
 * the inferred type (it is the only pass that has one) and `src/desugar.ts`
 * turns it into `Binder.arity = 0`, which is what makes codegen drop the
 * binder, its argument register and its closure slot entirely. */
export type Pattern = { tag: 'wild'; voidRep?: true; span: Span } | { tag: 'var'; name: string; voidRep?: true; span: Span } | { tag: 'as'; name: string; pattern: Pattern; span: Span } | { tag: 'int'; value: number; span: Span } | { tag: 'double'; value: number; span: Span } | { tag: 'string'; value: string; span: Span } | { tag: 'char'; value: string; span: Span } | { tag: 'con'; name: string; args: Pattern[]; span: Span } | { tag: 'record'; name: string; fields: Array<{ name: string; pattern: Pattern }>; wildcard: boolean; span: Span };
/** One `|` qualifier.  Haskell's guards are a *sequence* of these, evaluated
 * left to right, and a `p <- e` binds for everything to its right as well as
 * for the body - which is why they cannot be a single condition plus an
 * unordered bag of pattern matches. */
export type GuardQualifier = { tag: 'bool'; condition: Expr } | { tag: 'pattern'; pattern: Pattern; source: Expr };
export interface CaseAlternative {
  pattern: Pattern;
  /** Empty or absent for an unguarded alternative. */
  qualifiers?: GuardQualifier[];
  body: Expr;
}
export interface Guard { qualifiers?: GuardQualifier[]; body: Expr; }
export type ListQualifier = { tag: 'guard'; condition: Expr } | { tag: 'generator'; pattern: Pattern; source: Expr };
export type DoStatement = { tag: 'expr'; expr: Expr } | { tag: 'bind'; pattern: Pattern; source: Expr } | { tag: 'let'; bindings: LocalBinding[] };
export type Expr = { tag: 'var'; name: string; span: Span } | { tag: 'int'; value: number; span: Span } | { tag: 'double'; value: number; span: Span } | { tag: 'string'; value: string; span: Span } | { tag: 'char'; value: string; span: Span } | { tag: 'unit'; span: Span } | { tag: 'tuple'; items: Expr[]; span: Span } | { tag: 'list'; items: Expr[]; span: Span } | { tag: 'listComp'; body: Expr; qualifiers: ListQualifier[]; span: Span } | { tag: 'jsQuote'; body: string; quoter?: string; span: Span } | { tag: 'record'; constructor: string; fields: Array<{ name: string; value: Expr }>; wildcard?: boolean; span: Span } | { tag: 'recordUpdate'; base: Expr; fields: Array<{ name: string; value: Expr }>; span: Span } | { tag: 'app'; fn: Expr; arg: Expr; span: Span } | { tag: 'lambda'; parameter: string; /** See `Pattern`'s `voidRep`. */ voidRep?: true; body: Expr; span: Span } | { tag: 'lambdaCase'; alternatives: CaseAlternative[]; span: Span } | { tag: 'let'; bindings: LocalBinding[]; body: Expr; span: Span } | { tag: 'do'; statements: DoStatement[]; span: Span } | { tag: 'if'; condition: Expr; thenBranch: Expr; elseBranch: Expr; span: Span } | { tag: 'case'; subject: Expr; alternatives: CaseAlternative[]; span: Span } | { tag: 'annot'; expr: Expr; /** The written type, as source text; `src/elaborate.ts` parses it. */ type: string; span: Span } | { tag: 'typeApp'; expr: Expr; /** One `@T` argument, as source text; parsed by `src/elaborate.ts`. */ type: string; span: Span };
/** `strict` is BangPatterns' `let !x = e`: the binding is forced where the
 * group's body begins, which `src/desugar.ts` renders as a `Case`. */
export interface LocalBinding { name: string; patterns: Pattern[]; value: Expr; guards?: Guard[]; whereBindings?: LocalBinding[]; strict?: true; span: Span; }
export interface ValueDeclaration { tag: 'value'; name: string; equations: Array<{ patterns: Pattern[]; guards: Guard[]; whereBindings: LocalBinding[] }>; span: Span; }
export interface DataDeclaration { tag: 'data'; name: string; /** The name as the declaring module wrote it: `deriving Generic`'s `datatypeName` and `deriving Show`'s output are the surface name, not the module-scoped one. */ surfaceName?: string; parameters: string[]; constructors: Array<{ name: string; arity: number; fields?: string[]; fieldTypes?: string[];
    /** The names as the declaring module wrote them, kept because `deriving
     * Show` prints them and every other pass wants the renamed ones. */
    surface?: { name: string; fields?: string[] } }>;
  /** GHC's `deriving stock`, and a strategy-less clause, which means the same
   * for the classes this compiler derives. */
  deriving: string[];
  /** `deriving anyclass (C)`: an empty instance, every method from the class's
   * own defaults. */
  derivingAnyclass?: string[];
  /** `deriving newtype (C)`: the wrapped type's instance, lifted through the
   * newtype's constructor. */
  derivingNewtype?: string[];
  newtype?: boolean; span: Span; }
/** The signature is split at top-level arrows, preserving the declared Haskell types. */
export interface ForeignDeclaration { tag: 'foreign'; name: string; javascript: string; signature: string[]; arity: number; span: Span; }
/** `isDefault` marks GHC's DefaultSignatures form, `default f :: ty` in a class
 * body: the type of the class's *default implementation* of `f`, which may be
 * more constrained than `f`'s own. */
export interface SignatureDeclaration { tag: 'signature'; name: string; /** The name as the declaring module wrote it. An instance may bind a class method it has not imported - the method binder of an instance is resolved against the class, not the value namespace - so the instance's written name has to be matchable against this. */ surfaceName?: string; type: string; isDefault?: true; span: Span; }
export interface TypeAliasDeclaration { tag: 'typeAlias'; name: string; parameters: string[]; target: string; /** Empty only to keep declaration visitors exhaustive until Core gains aliases. */ equations: []; span: Span; }
/** Class/instance headers and members are preserved instead of being skipped.
 * Dictionary construction is a later typed-Core phase, but interface and
 * dependency analysis must already be able to see these declarations. */
/** Lossless member slice retained for dictionary/Core parsing.  A member may
 * contain associated types or an infix equation that is not yet one of the
 * compact surface `Declaration` forms. */
export interface ClassMemberSlice { tokens: string[]; span: Span; }
/** `associatedTypes` is a class's `type family F a` members, or an instance's
 * `type F t = rhs` ones. An associated type is read as an extra class
 * parameter the class's own parameters determine - see `src/elaborate.ts`. */
export interface AssociatedType { name: string; rhs?: string; }
export interface ClassDeclaration { tag: 'class'; name: string; associatedTypes: AssociatedType[]; /** Superclass constraints, one string per item of the `=>` context. */ context: string[]; parameters: string[]; /** `| m -> s, a b -> c`: each dependency names parameters, by name. */ fundeps: Array<{ from: string[]; to: string[] }>; members: Declaration[]; rawMembers: ClassMemberSlice[]; span: Span; }
export interface InstanceDeclaration { tag: 'instance'; head: string; associatedTypes: AssociatedType[]; members: Declaration[]; rawMembers: ClassMemberSlice[]; span: Span; }
/** Parsed but not yet represented in Core.  Keeping these explicit ensures a
 * later phase reports one accurate unsupported-feature diagnostic instead of
 * pretending the declaration was absent. */
export interface UnsupportedDeclaration { tag: 'unsupported'; feature: string; span: Span; }
export interface SpliceDeclaration { tag: 'splice'; name: string; argument: string; span: Span; }
export type Declaration = ValueDeclaration | DataDeclaration | ForeignDeclaration | SignatureDeclaration | TypeAliasDeclaration | ClassDeclaration | InstanceDeclaration | UnsupportedDeclaration | SpliceDeclaration;
/** The surface import is retained until name resolution.  In particular,
 * `qualified`, `as`, explicit import lists, and `hiding` cannot be recovered
 * once an import has been reduced to a module-name string. */
export interface ImportDeclaration {
  module: string;
  qualified: boolean;
  alias?: string;
  exposing?: string[];
  /** Type names written as `T(..)` in an explicit import list. */
  exposingConstructors?: string[];
  hiding?: string[];
  /** Type names written as `T(..)` in a hiding list. */
  hidingConstructors?: string[];
  span: Span;
}
export interface Module { name: string; imports: ImportDeclaration[]; /** Named values/types explicitly exported by the module header. */ exports: string[]; /** Modules explicitly re-exported from the module header. */ reexports: string[]; declarations: Declaration[]; }
