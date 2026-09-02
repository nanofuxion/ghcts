/** STG, ported from GHC/Stg/Syntax.hs.
 *
 * This is the input language of `GHC.StgToJS` - the backend ghcts now
 * reproduces byte-for-byte. GHC arrives here via Core, CorePrep and
 * CoreToStg; ghcts is building the same road from the other end, so this
 * module exists before anything produces it.
 *
 * Two properties of STG are what make the JS backend possible at all, and
 * both are invariants callers must maintain rather than things this module
 * can check:
 *
 *   - every application is saturated, and every argument is atomic (a
 *     variable or a literal, never a nested expression). That is what lets
 *     codegen pick `h$ap_2_2` at compile time instead of dispatching on
 *     arity at run time.
 *   - every closure lists its free variables and says whether entering it
 *     updates it. That is what lets codegen lay out `{d1, d2, f, m}` and
 *     know which entries need an update frame.
 *
 * GHC parameterises the syntax over a compilation `pass` so binders can gain
 * free-variable and liveness annotations. TypeScript has no equivalent that
 * pays for itself here, so this models the post-CoreToStg shape directly -
 * the one StgToJS consumes - with the annotations as optional fields.
 */

/** An STG binder. GHC uses Core `Id`s throughout; ghcts has no Core `Id`
 * yet, so a binder is its own record and identity is object identity. */
export interface Binder {
  /** Source name, for readable output and symbol generation. */
  name: string;
  /** Unique within a module; supplies the `_u` suffix on generated names. */
  unique: number;
  /** Defining module for a top-level imported binding. The frontend flattens
   * Core names for resolution, but StgToJS must still emit the binding in the
   * package/module namespace GHC compiled it in. Local binders leave this
   * unset and use the current codegen module. */
  definingUnitId?: string;
  definingModuleName?: string;
  /** How many JS values this binder occupies - see JSRep/varSize. A void
   * binder occupies none and is dropped entirely by codegen. */
  arity?: number;
  /** Set on a top-level binder that other modules can reference. Codegen also
   * reads it as GHC's `isGlobalId` - see `liveVars` in src/stg-js/utils.ts. */
  exported?: boolean;
  /** Binder is a module-level binding, including compiler-generated workers.
   * This is distinct from `exported`: GHC's internal top-level workers are
   * local symbols but are still non-local Ids for saturated direct apply. */
  topLevel?: boolean;
  /** GHC's `isNothing (nameModule_maybe (idName i))`: this name was invented by
   * the compiler and belongs to no module, so nothing outside can ever spell
   * it. Only `GHC.StgToJS.Sinker` asks (src/stg-js/sinker.ts), and only about
   * top-level binders, where `exported` is true of every binder that came from
   * source and so cannot tell the two apart on its own. */
  internal?: boolean;
  /** The answer to GHC's `mightBeFunTy (idType i)`, precomputed.
   *
   * A binder carries no type here, and `GHC.Types.RepType.mightBeFunTy` is the
   * only thing StgToJS asks a type that changes the bytes this compiler emits
   * (see `genApp` in src/stg-js/expr.ts). So rather than grow a Core type
   * system, the desugarer answers that one question where it can and leaves it
   * `undefined` where it cannot. `undefined` therefore means "unknown", and
   * every consumer must read it the way `mightBeFunTy` is documented to be
   * read: False only when we are *sure* it is a data type. */
  mightBeFun?: boolean;
  /** Number of source-level value arguments in the closure's entry point. */
  funRepArity?: number;
  /** The thunk this binder names is entered at most once, so no update frame
   * is needed - GHC's `SingleEntry`. Set only when the binding's body reads it
   * exactly once, outside any lambda or recursive group. */
  singleEntry?: boolean;
  /** The binder is known to be strict/evaluated at its use site. */
  strict?: boolean;
  /** GHC's separate proof that a known-arity entry may use direct apply. */
  directJumpEligible?: boolean;
  evaluated?: boolean;
  /** The binding is entered at most once (GHC's one-shot information). */
  oneShot?: boolean;
  /** Join-point marker; join points must not use direct native calls. */
  join?: boolean;
  /** Proven-safe candidate for raw primitive lowering.  This is only a
   * compiler fact; code generation must still retain the ABI entry wrapper. */
  nativeEligible?: boolean;
  /** Result representation proven by the narrow native-candidate analysis. */
  nativeResultRep?: "i32" | "f64" | "bool" | "string";
  /** Source-level primitive representation retained for worker/wrapper. */
  primitiveRep?: "Int" | "Bool" | "Double" | "Float" | "Word" | "Char" | "JSVal" | "JSString";
  parameterReps?: Array<"Int" | "Bool" | "Double" | "Float" | "Word" | "Char" | "JSVal" | "JSString">;
  /** Source declaration carried an explicit GHC INLINE pragma. */
  inline?: boolean;
  /** Closed floated value that lives at a top-level static binding. */
  staticValue?: boolean;
  /** Boxed result type retained from elaboration for CPR/worker-wrapper. */
  resultRep?: "boxed-int";
  /** Case alternative binder already carries an unboxed Int payload. */
  unboxedInt?: true;
  /** 128-bit static-pointer fingerprint as two Word64 halves. Set on the
   * binder of each `static e` form so StgToJS can push `h$hs_spt_insert`
   * onto `h$initStatic` the way GHC's `initStaticPtrs` does. */
  sptFingerprint?: [bigint, bigint];
}

/** GHC's Literal, narrowed to what the JS backend can represent.
 *
 * The split matters: `LitNumInt` becomes a single untouched JS number, while
 * the explicitly-sized `LitNumInt64`/`LitNumWord64` become a hi/lo pair of
 * 32-bit values. That is why `Int` is 32-bit on this target and not the
 * 64-bit machine word it is on native GHC. */
export type Literal =
  | { tag: "LitChar"; value: string }
  | { tag: "LitString"; value: string }
  | { tag: "LitNullAddr" }
  | { tag: "LitFloat"; value: number }
  | { tag: "LitDouble"; value: number }
  | { tag: "LitNumInt"; value: bigint }
  | { tag: "LitNumInt8"; value: bigint }
  | { tag: "LitNumInt16"; value: bigint }
  | { tag: "LitNumInt32"; value: bigint }
  | { tag: "LitNumInt64"; value: bigint }
  | { tag: "LitNumWord"; value: bigint }
  | { tag: "LitNumWord8"; value: bigint }
  | { tag: "LitNumWord16"; value: bigint }
  | { tag: "LitNumWord32"; value: bigint }
  | { tag: "LitNumWord64"; value: bigint }
  | { tag: "LitLabel"; name: string };

/** A data constructor. */
export interface DataCon {
  name: string;
  unique: number;
  /** Defining module for an imported constructor. The STG backend derives a
   * worker Binder from this record, so provenance must survive that step. */
  definingUnitId?: string;
  definingModuleName?: string;
  /** 1-based, in declaration order. The RTS compares against this. */
  tag: number;
  arity: number;
  /** The type this constructor belongs to, for `AlgAlt` dispatch. */
  typeName: string;
  /** Source field representations, when known. */
  fieldReps?: Array<"boxed-int" | "other">;
  /** Fields delivered as raw machine values when pattern-matched. */
  fieldUnboxed?: boolean[];
  /** A newtype's constructor: erased by `src/erase-newtypes.ts`, never built. */
  newtype?: true;
}

/** An unboxed tuple, spelled `(#,#)` as GHC spells it. It is not a heap
 * object: its fields live in registers, so it is never allocated, never
 * entered and never tagged - the backend keys off exactly this name prefix
 * (`stg-js/utils.ts`), and the front half of the pipeline has to agree. */
export const isUnboxedTupleCon = (con: DataCon): boolean => con.name.startsWith("(#");

/** StgArg - atomic by construction. */
export type StgArg = { tag: "StgVarArg"; id: Binder } | { tag: "StgLitArg"; lit: Literal };

export const varArg = (id: Binder): StgArg => ({ tag: "StgVarArg", id });
export const litArg = (lit: Literal): StgArg => ({ tag: "StgLitArg", lit });

/** A primitive operation or foreign call. */
export type StgOp =
  | { tag: "StgPrimOp"; op: string }
  | { tag: "StgPrimCallOp"; name: string }
  | { tag: "StgFCallOp"; target: ForeignCall };

/** A `foreign import javascript` target. The body is opaque spliced text -
 * GHC's own FFI does not parse it either. */
export interface ForeignCall {
  /** JS source with `$1`, `$2`, ... argument holes and an optional `$r`. */
  javascript: string;
  safety: "unsafe" | "safe" | "interruptible";
}

/** How entering a closure behaves. */
export enum UpdateFlag {
  /** May be entered many times; entering does not update it. Functions. */
  ReEntrant,
  /** Entering overwrites it with its value. Ordinary thunks. */
  Updatable,
  /** Entered at most once, so the update is provably wasted. */
  SingleEntry,
}

export type StgExpr =
  /** Application of a variable to arguments. Saturated except where the
   * callee's arity is genuinely unknown, which is what `h$ap_gen` handles. */
  | { tag: "StgApp"; fn: Binder; args: StgArg[] }
  | { tag: "StgLit"; lit: Literal }
  /** Saturated constructor application. Kept distinct from StgApp because a
   * constructor allocates rather than enters. */
  | { tag: "StgConApp"; con: DataCon; args: StgArg[] }
  /** Saturated primop or foreign call. */
  | { tag: "StgOpApp"; op: StgOp; args: StgArg[] }
  | { tag: "StgCase"; scrutinee: StgExpr; binder: Binder; altType: AltType; alts: StgAlt[] }
  | { tag: "StgLet"; binding: StgBinding; body: StgExpr }
  /** A `let` whose right-hand sides are guaranteed already evaluated, so no
   * thunk needs allocating. */
  | { tag: "StgLetNoEscape"; binding: StgBinding; body: StgExpr };

/** What the scrutinee of a case evaluates to, which decides how codegen
 * dispatches: on a constructor tag, on a literal, or not at all. */
export type AltType =
  /** One alternative; nothing to dispatch on. */
  | { tag: "PolyAlt" }
  /** Unboxed tuple or enum-like unboxed sum. */
  | { tag: "MultiValAlt"; arity: number }
  | { tag: "AlgAlt"; typeName: string }
  | { tag: "PrimAlt" };

export type AltCon =
  | { tag: "DataAlt"; con: DataCon }
  | { tag: "LitAlt"; lit: Literal }
  /** The catch-all. GHC requires it to come first when present. */
  | { tag: "DEFAULT" };

export interface StgAlt {
  con: AltCon;
  /** Fields bound by a DataAlt, in constructor field order. */
  binders: Binder[];
  body: StgExpr;
}

/** A closure's right-hand side. */
export type StgRhs =
  | {
      tag: "StgRhsClosure";
      /** Free variables, which become the closure's payload. */
      freeVars: Binder[];
      update: UpdateFlag;
      /** Empty means a thunk rather than a function. */
      args: Binder[];
      body: StgExpr;
    }
  /** A constructor application known at allocation time; no entry needed. */
  | { tag: "StgRhsCon"; con: DataCon; args: StgArg[] };

export type StgBinding =
  | { tag: "StgNonRec"; binder: Binder; rhs: StgRhs }
  | { tag: "StgRec"; pairs: Array<[Binder, StgRhs]> };

export interface StgModule {
  name: string;
  bindings: StgBinding[];
}

/** Does this right-hand side allocate a function, as opposed to a thunk or a
 * constructor? Codegen needs this to choose an entry convention. */
export function isFunctionRhs(rhs: StgRhs): boolean {
  return rhs.tag === "StgRhsClosure" && rhs.args.length > 0;
}

/** Binders an alternative brings into scope. */
export function altBinders(alt: StgAlt): Binder[] {
  return alt.binders;
}

let nextUnique = 0;
/** Fresh binder. Uniques are per-process, matching GHC's own supply in
 * spirit; codegen only requires that they not collide within a module. */
export function mkBinder(name: string, extra: Partial<Binder> = {}): Binder {
  return { name, unique: nextUnique++, ...extra };
}
export function mkDataCon(name: string, tag: number, arity: number, typeName: string, fieldReps?: DataCon["fieldReps"]): DataCon {
  return { name, unique: nextUnique++, tag, arity, typeName, ...(fieldReps ? { fieldReps } : {}) };
}
