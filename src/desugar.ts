/** Surface AST (`src/ast.ts`) to Core (`src/core.ts`).
 *
 * Scope. This pass targets class-free Haskell, which is what it now receives:
 * `src/elaborate.ts` runs first and has already turned classes, instances and
 * constrained call sites into data types, values and explicit dictionary
 * arguments. Anything still unsupported here - `do` notation, list
 * comprehensions, records - produces a diagnostic and an expression that
 * raises, so one unsupported construct never silently corrupts the rest of
 * the module.
 *
 * Representation, now that dictionaries exist:
 *
 *   - an integer literal is an `Int#` ONLY under `fromInteger`. `Int` itself
 *     is the ordinary boxed `I Int#` the Prelude declares, so arithmetic goes
 *     through `$fNumInt` and an `Int` argument can be a thunk again.
 *   - `Bool` is an ordinary two-constructor data type. The comparison primops
 *     still yield a 0/1 machine value, so each one is wrapped here into a
 *     real `False`/`True` - GHC's `tagToEnum# (<# a b)`, applied once, at the
 *     only place the machine value is visible.
 *   - the `prim*` names below are the only primitives. They are typed over the
 *     unboxed `IntPrim`/`CharPrim`, never over `Int`, so no builtin can be
 *     mistaken for a class method.
 */
import type {
  CaseAlternative,
  Declaration,
  Expr,
  ForeignDeclaration,
  Guard,
  GuardQualifier,
  LocalBinding,
  Module,
  Pattern,
  Span,
} from "./ast.js";
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "./core.js";
import { coreFreeVars, mkApps, mkLams } from "./core.js";
import { error } from "./diagnostics.js";
import type { Binder, DataCon, Literal, StgOp } from "./stg.js";
import { isUnboxedTupleCon, mkBinder, mkDataCon } from "./stg.js";
import type { Diagnostic } from "./types.js";

export interface DesugarResult {
  program: CoreProgram;
  diagnostics: Diagnostic[];
}

const int = (value: number): Literal => ({ tag: "LitNumInt", value: BigInt(Math.trunc(value)) });

/** Primitive name to primop. `bool` marks the ones whose 0/1 machine result
 * is wrapped into a real `Bool` constructor. Only ops the JS backend
 * implements appear here (see src/stg-js/prim.ts). */
interface Prim {
  op: string | StgOp;
  arity: number;
  bool?: true;
}

/** GHC's `realWorld# :: State# RealWorld`, wired in exactly as GHC wires it.
 *
 * It is a variable, not a primop: it stands for a value of a VOID type, so it
 * occupies no JS value and codegen drops every reference to it. That is why
 * one shared binder for the whole program is safe - nothing is ever loaded
 * from it, stored into it or captured by it. */
const REAL_WORLD: Binder = mkBinder("realWorld#", { arity: 0 });

/** Data types the frontend represents as GHC's unboxed tuples rather than as
 * heap objects. The only one is `IOResult`, which IS `(# State# RealWorld,
 * a #)`: it is declared as ordinary Haskell so the type checker can see its
 * fields, and wired here to the backend's unboxed-tuple constructor, which is
 * recognised by the `(#` name prefix (`stg-js/utils.ts isUnboxedTupleDataCon`).
 *
 * The consequences are the whole point of the representation: building one
 * assigns registers instead of allocating, and matching one binds the result
 * slot WITHOUT entering it, so an `IO` action can return a thunk - which is
 * what makes `readIORef` hand back what was written without forcing it. */
const UNBOXED_TUPLE_TYPES = new Set(["IOResult"]);

/** `(#,,#)` with `n-1` commas, GHC's own spelling. */
const unboxedTupleName = (arity: number): string => `(#${",".repeat(Math.max(0, arity - 1))}#)`;

const primOps: Record<string, Prim> = {
  primIntAdd: { op: "IntAddOp", arity: 2 },
  primIntSub: { op: "IntSubOp", arity: 2 },
  primIntMul: { op: "IntMulOp", arity: 2 },
  primIntQuot: { op: "IntQuotOp", arity: 2 },
  primIntRem: { op: "IntRemOp", arity: 2 },
  primIntNeg: { op: "IntNegOp", arity: 1 },
  primIntEq: { op: "IntEqOp", arity: 2, bool: true },
  primIntNe: { op: "IntNeOp", arity: 2, bool: true },
  primIntLt: { op: "IntLtOp", arity: 2, bool: true },
  primIntLe: { op: "IntLeOp", arity: 2, bool: true },
  primIntGt: { op: "IntGtOp", arity: 2, bool: true },
  primIntGe: { op: "IntGeOp", arity: 2, bool: true },
  primChr: { op: "ChrOp", arity: 1 },
  primCharOrd: { op: "OrdOp", arity: 1 },
  primCharEq: { op: "CharEqOp", arity: 2, bool: true },
  primCharLt: { op: "CharLtOp", arity: 2, bool: true },
  primDoubleAdd: { op: "DoubleAddOp", arity: 2 },
  primDoubleSub: { op: "DoubleSubOp", arity: 2 },
  primDoubleMul: { op: "DoubleMulOp", arity: 2 },
  primDoubleDiv: { op: "DoubleDivOp", arity: 2 },
  primDoubleNeg: { op: "DoubleNegOp", arity: 1 },
  primDoubleAbs: { op: "DoubleFabsOp", arity: 1 },
  primDoubleEq: { op: "DoubleEqOp", arity: 2, bool: true },
  primDoubleLt: { op: "DoubleLtOp", arity: 2, bool: true },
  primDoubleLe: { op: "DoubleLeOp", arity: 2, bool: true },
  primDoubleGt: { op: "DoubleGtOp", arity: 2, bool: true },
  primDoubleGe: { op: "DoubleGeOp", arity: 2, bool: true },
  primDoubleSqrt: { op: "DoubleSqrtOp", arity: 1 },
  primDoubleLog: { op: "DoubleLogOp", arity: 1 },
  primDoubleExp: { op: "DoubleExpOp", arity: 1 },
  primDoublePower: { op: "DoublePowerOp", arity: 2 },
  // `Float` is IEEE *single* precision: every result goes through `Math.fround`,
  // which is the whole of what makes it a different type from `Double` on a
  // backend where both are JS numbers.
  primFloatAdd: { op: "FloatAddOp", arity: 2 },
  primFloatSub: { op: "FloatSubOp", arity: 2 },
  primFloatMul: { op: "FloatMulOp", arity: 2 },
  primFloatDiv: { op: "FloatDivOp", arity: 2 },
  primFloatNeg: { op: "FloatNegOp", arity: 1 },
  primFloatAbs: { op: "FloatFabsOp", arity: 1 },
  primFloatEq: { op: "FloatEqOp", arity: 2, bool: true },
  primFloatLt: { op: "FloatLtOp", arity: 2, bool: true },
  primFloatLe: { op: "FloatLeOp", arity: 2, bool: true },
  primFloatGt: { op: "FloatGtOp", arity: 2, bool: true },
  primFloatGe: { op: "FloatGeOp", arity: 2, bool: true },
  primFloatToDouble: { op: "FloatToDoubleOp", arity: 1 },
  primDoubleToFloat: { op: "DoubleToFloatOp", arity: 1 },
  primIntToDouble: { op: "IntToDoubleOp", arity: 1 },
  // Truncates towards zero, as GHC's `double2Int#` does.
  primDoubleToInt: { op: "DoubleToIntOp", arity: 1 },
  // `IORef` is GHC's `MutVar#`: a one-field JS object whose read and write are
  // a property read and a property write (rts/js/mem.js). Writing this in
  // Haskell instead would be a slower cell with identical semantics.
  primNewMutVar: { op: "NewMutVarOp", arity: 1 },
  primReadMutVar: { op: "ReadMutVarOp", arity: 1 },
  primWriteMutVar: { op: "WriteMutVarOp", arity: 2 },
  // `MVar` is NOT a cell: `takeMVar` on an empty one blocks the *thread*, and
  // only the RTS can do that (rts/js/thread.js). These map onto the same
  // primops GHC's `Control.Concurrent.MVar` uses, so a take that must block
  // does block instead of silently reading a hole.
  //
  // `NewMVarOp` ignores its argument slot; the argument is the state token, and
  // it is there only so the call is not a CAF - a nullary primop would be one
  // top-level `MVar` shared by every `newEmptyMVar` in the program.
  primNewMVar: { op: "NewMVarOp", arity: 1 },
  primTakeMVar: { op: "TakeMVarOp", arity: 1 },
  primPutMVar: { op: "PutMVarOp", arity: 2 },
  primReadMVar: { op: "ReadMVarOp", arity: 1 },
  primTryPutMVar: { op: "TryPutMVarOp", arity: 2, bool: true },
  primIsEmptyMVar: { op: "IsEmptyMVarOp", arity: 1, bool: true },
  // `h$makeStableName` hands back one object per heap object and
  // `h$stableNameInt` its unique integer, so integer equality on two stable
  // names is object identity - which is what `Eq (StableName a)` means.
  primMakeStableName: { op: "MakeStableNameOp", arity: 1 },
  primStableNameInt: { op: "StableNameToIntOp", arity: 1 },
  // `Word` is GHC's unsigned machine word, 32 bits on this backend exactly as
  // `Int` is signed 32 bits. Its own primops are what make that unsigned: the
  // results come back through `>>> 0` and the multiply through `Math.imul`,
  // neither of which `Int` arithmetic would give.
  primWordAdd: { op: "WordAddOp", arity: 2 },
  primWordSub: { op: "WordSubOp", arity: 2 },
  primWordMul: { op: "WordMulOp", arity: 2 },
  primWordQuot: { op: "WordQuotOp", arity: 2 },
  primWordRem: { op: "WordRemOp", arity: 2 },
  primWordEq: { op: "WordEqOp", arity: 2, bool: true },
  primWordLt: { op: "WordLtOp", arity: 2, bool: true },
  primWordLe: { op: "WordLeOp", arity: 2, bool: true },
  primWordGt: { op: "WordGtOp", arity: 2, bool: true },
  primWordGe: { op: "WordGeOp", arity: 2, bool: true },
  primIntToWord: { op: "IntToWordOp", arity: 1 },
  primWordToDouble: { op: "WordToDoubleOp", arity: 1 },
  primFork: { op: "ForkOp", arity: 1 },
  primDelay: { op: "DelayOp", arity: 1 },
  // These three are the reason `IO` had to move onto GHC's representation.
  // Each one manipulates the *stack*, so none of them can be a foreign call:
  //
  //   - `h$catch` pushes a handler frame and then JUMPS into the action with
  //     `h$ap_1_0_fast`, which only works if the action is a closure of arity
  //     one whose argument occupies no register. `h$throw` later unwinds to
  //     that frame and applies the handler with `h$ap_2_1_fast` - two
  //     arguments, one register, the exception and the erased token.
  //   - `h$throw` does not return at all; it hands back the frame to resume.
  //   - `h$killThread` returns a *continuation* to jump to when the victim is
  //     the current thread.
  //
  // A `foreign import javascript unsafe` cannot say "do not return, jump
  // here"; `PRPrimCall` in the backend can, and that is what these compile to.
  primCatch: { op: "CatchOp", arity: 3 },
  primRaiseIO: { op: "RaiseIOOp", arity: 2 },
  primKillThread: { op: "KillThreadOp", arity: 3 },
};

/** What a name resolves to. Locals shadow top levels, which shadow
 * constructors, which shadow primops. */
type Scope = ReadonlyMap<string, Binder>;

class Desugarer {
  readonly diagnostics: Diagnostic[] = [];
  readonly cons = new Map<string, DataCon>();
  /** How many constructors each data type has, so an alternative list that
   * covers all of them can drop its unreachable DEFAULT. Codegen emits no tag
   * test for a single-constructor type, and would then see two defaults. */
  readonly conCount = new Map<string, number>([["[]", 2]]);
  readonly top = new Map<string, Binder>();
  /** Names introduced by a `class` declaration, so a use of one can say
   * "dictionary elaboration" instead of "not in scope". */
  readonly classMethods = new Set<string>();
  /** Foreign imports, by name, so a *saturated* call becomes the foreign call
   * itself rather than a call to the wrapper closure.
   *
   * This is not an optimisation. A `foreign import javascript unsafe` consumes
   * machine values, and the wrapper is an ordinary Haskell function whose
   * arguments are therefore thunks: `len (hello 0)` handed the JS function a
   * thunk object instead of the string. Inlining the call puts the argument in
   * a primop's strict position, where `src/core-to-stg.ts` binds it with a
   * `case` - which is exactly what GHC does by inlining the same wrapper. */
  readonly foreignOps = new Map<string, Prim>();

  constructor(private readonly file: string) {}

  fail(feature: string, span: Span): CoreExpr {
    this.diagnostics.push(
      error("GHCTS-DESUGAR", `${feature} is not supported by the STG frontend yet`, this.file, span.line, span.column),
    );
    return raise();
  }

  /** Constructors are looked up by name across the module; tuples and list
   * cells are synthesised on demand so class-free code can still build them. */
  lookupCon(name: string, arity: number): DataCon {
    const found = this.cons.get(name);
    if (found) return found;
    const made =
      name === "[]"
        ? mkDataCon("[]", 1, 0, "[]")
        : name === ":"
          ? mkDataCon(":", 2, 2, "[]")
          : mkDataCon(name, 1, arity, name);
    this.cons.set(name, made);
    return made;
  }

  expr(e: Expr, scope: Scope): CoreExpr {
    switch (e.tag) {
      case "int":
        return { tag: "Lit", lit: int(e.value) };
      case "double":
        return { tag: "Lit", lit: { tag: "LitDouble", value: e.value } };
      case "char":
        return { tag: "Con", con: this.lookupCon("C", 1), args: [{ tag: "Lit", lit: { tag: "LitChar", value: e.value } }] };
      case "string":
        // A `String` is `[Char]`, so a literal is the list it denotes. The
        // backend's `LitString` is an address, which is a different type.
        return [...e.value].reduceRight<CoreExpr>(
          (tail, character) => ({
            tag: "Con",
            con: this.lookupCon(":", 2),
            args: [
              { tag: "Con", con: this.lookupCon("C", 1), args: [{ tag: "Lit", lit: { tag: "LitChar", value: character } }] },
              tail,
            ],
          }),
          { tag: "Con", con: this.lookupCon("[]", 0), args: [] },
        );
      case "unit":
        return { tag: "Lit", lit: int(0) };
      // The type has already done its work in `src/elaborate.ts`, and STG is
      // type-erased, so the node is simply the expression it wraps.
      case "annot":
      case "typeApp":
        return this.expr(e.expr, scope);
      case "var":
        return this.varRef(e.name, scope, e.span);
      case "app": {
        const [head, args] = flattenApp(e);
        return this.application(head, args, scope);
      }
      case "lambda": {
        const binder = mkBinder(e.parameter, voidArity(e.voidRep));
        return { tag: "Lam", binder, body: this.expr(e.body, extend(scope, [[e.parameter, binder]])) };
      }
      case "lambdaCase": {
        const binder = mkBinder("lcase");
        return {
          tag: "Lam",
          binder,
          body: this.alternatives({ tag: "Var", binder }, e.alternatives, scope, e.span),
        };
      }
      case "if":
        return this.boolCase(
          this.expr(e.condition, scope),
          () => this.expr(e.thenBranch, scope),
          () => this.expr(e.elseBranch, scope),
        );
      case "case": {
        const scrutinee = this.expr(e.subject, scope);
        return this.alternatives(scrutinee, e.alternatives, scope, e.span);
      }
      case "let": {
        const [binds, inner] = this.localGroup(e.bindings, scope);
        return binds.reduceRight<CoreExpr>(
          (body, bind) => ({ tag: "Let", bind, body }),
          forceStrict(e.bindings, inner, this.expr(e.body, inner)),
        );
      }
      case "tuple": {
        const con = this.lookupCon(`(${",".repeat(e.items.length - 1)})`, e.items.length);
        return { tag: "Con", con, args: e.items.map((item) => this.expr(item, scope)) };
      }
      case "list":
        return e.items.reduceRight<CoreExpr>(
          (tail, item) => ({ tag: "Con", con: this.lookupCon(":", 2), args: [this.expr(item, scope), tail] }),
          { tag: "Con", con: this.lookupCon("[]", 0), args: [] },
        );
      case "do":
        return this.fail("do notation (it needs a Monad dictionary)", e.span);
      case "listComp":
        return this.fail("list comprehensions", e.span);
      case "record":
      case "recordUpdate":
        return this.fail("record syntax", e.span);
      case "jsQuote":
        return this.fail("JS quotation", e.span);
    }
  }

  varRef(name: string, scope: Scope, span: Span): CoreExpr {
    const local = scope.get(name);
    if (local) return { tag: "Var", binder: local };
    if (name === "primRealWorld") return { tag: "Var", binder: REAL_WORLD };
    const con = this.cons.get(name);
    if (con) return this.saturateCon(con, []);
    const prim = primOps[name];
    if (prim) return this.saturateOp(prim, []);
    if (this.classMethods.has(name)) {
      return this.fail(`class method \`${name}\` (dictionary elaboration)`, span);
    }
    return this.fail(`\`${name}\` is not in scope`, span);
  }

  /** Con and Op nodes must come out saturated (see src/core.ts). An
   * under-applied occurrence becomes a lambda that supplies the rest. */
  saturateCon(con: DataCon, args: CoreExpr[]): CoreExpr {
    if (args.length === con.arity) return { tag: "Con", con, args };
    if (args.length > con.arity) {
      // Over-application of a constructor cannot happen in well-typed code.
      return mkApps({ tag: "Con", con, args: args.slice(0, con.arity) }, args.slice(con.arity));
    }
    const extra = Array.from({ length: con.arity - args.length }, (_, i) => mkBinder(`${con.name}_${i}`));
    return mkLams(extra, { tag: "Con", con, args: [...args, ...extra.map(varOf)] });
  }

  saturateOp(prim: Prim, args: CoreExpr[]): CoreExpr {
    const op: StgOp = typeof prim.op === "string" ? { tag: "StgPrimOp", op: prim.op } : prim.op;
    const call = (as: CoreExpr[]): CoreExpr => {
      const raw: CoreExpr = { tag: "Op", op, arity: prim.arity, args: as };
      // GHC's `tagToEnum#`: the machine comparison yields 0 or 1, and the
      // whole rest of the compiler only ever sees a real constructor.
      return prim.bool ? this.boolCase(raw, () => this.con("True"), () => this.con("False"), true) : raw;
    };
    if (args.length >= prim.arity) return mkApps(call(args.slice(0, prim.arity)), args.slice(prim.arity));
    const extra = Array.from({ length: prim.arity - args.length }, (_, i) => mkBinder(`p${i}`));
    return mkLams(extra, call([...args, ...extra.map(varOf)]));
  }

  con(name: string): CoreExpr {
    return { tag: "Con", con: this.lookupCon(name, 0), args: [] };
  }

  /** Scrutinise a condition. `primitive` says whether it is still the 0/1
   * machine result of a comparison primop, or already a real `Bool`. */
  boolCase(scrutinee: CoreExpr, whenTrue: () => CoreExpr, whenFalse: () => CoreExpr, primitive = false): CoreExpr {
    return {
      tag: "Case",
      scrutinee,
      binder: mkBinder("cond"),
      alts: primitive
        ? [
            { con: { tag: "LitAlt", lit: int(0) }, binders: [], body: whenFalse() },
            { con: { tag: "DEFAULT" }, binders: [], body: whenTrue() },
          ]
        : [
            { con: { tag: "DataAlt", con: this.lookupCon("False", 0) }, binders: [], body: whenFalse() },
            { con: { tag: "DataAlt", con: this.lookupCon("True", 0) }, binders: [], body: whenTrue() },
          ],
    };
  }

  application(head: Expr, args: Expr[], scope: Scope): CoreExpr {
    let lowered = args.map((arg) => this.expr(arg, scope));
    if (head.tag === "var") {
      const shortCut = this.overloadedLit(head.name, lowered);
      if (shortCut) return shortCut;
      lowered = this.boxIntegerLit(head.name, lowered);
    }
    if (head.tag === "var") {
      // A foreign import IS in scope (it is a top-level binding), so this test
      // is that the name still means that binding and has not been shadowed.
      const foreign = this.foreignOps.get(head.name);
      if (foreign && scope.get(head.name) === this.top.get(head.name) && lowered.length >= foreign.arity)
        return this.saturateOp(foreign, lowered);
    }
    if (
      head.tag === "var" &&
      head.name === "seq" &&
      lowered.length >= 2 &&
      // `seq` is an ordinary Prelude binding here, so "not shadowed" is the
      // same test the foreign-import short-cut above uses: the name still
      // resolves to the top-level one.
      scope.get(head.name) === this.top.get(head.name)
    ) {
      // `seq` is a language primitive in GHC, not a library function:
      // `GHC.Core.Utils.mkCoreApp` turns a saturated `seq a b` into
      // `case a of _DEFAULT -> b`. ghcts had it as an ordinary two-argument
      // Prelude function calling a second one (`forceValue`), so every use
      // allocated a thunk per argument and made two generic-apply calls to
      // achieve what a `case` does with no allocation at all. That is pure
      // overhead in exactly the places `seq` exists to appear - strict
      // accumulators and forcing loops.
      //
      // Only a *saturated* occurrence is rewritten, and only where `seq` still
      // means the Prelude's: shadowed or partially applied, it stays the
      // ordinary function it always was, so `foldr seq` and friends keep
      // working.
      const rest = lowered.slice(2);
      const forced: CoreExpr = {
        tag: "Case",
        scrutinee: lowered[0]!,
        binder: mkBinder("seq"),
        alts: [{ con: { tag: "DEFAULT" }, binders: [], body: lowered[1]! }],
      };
      return rest.length ? mkApps(forced, rest) : forced;
    }
    if (head.tag === "var" && !scope.has(head.name)) {
      const con = this.cons.get(head.name);
      if (con) return this.saturateCon(con, lowered);
      const prim = primOps[head.name];
      if (prim) return this.saturateOp(prim, lowered);
    }
    return mkApps(this.expr(head, scope), lowered);
  }

  /** GHC's `dsOverLit` short-cut: an overloaded literal whose type is already
   * known is built directly rather than left as a `fromInteger` call, so
   * `5 :: Int` is `I# 5#` and not a thunk that computes it. The literal is
   * then a constructor application with an atomic argument, which the backend
   * allocates statically - and for `Int`, whose one field is unboxable, that
   * static allocation IS the number.
   *
   * Elaboration has already picked the dictionary, and `$fNumInt` names the
   * `Int` instance the way GHC's `intDataCon` names its constructor, so the
   * type is recoverable here without a type checker.
   *
   * When the short-cut does NOT fire the call is still rewritten, because
   * `fromInteger :: Integer -> a` and the elaborator hands over the machine
   * literal untouched (src/elaborate.ts `rewriteBinding`). `integerFromIntPrim`
   * is what turns it into the `Integer` the instance destructures - the same
   * boxing GHC's `mkIntegerExpr` does for the literals `shortCutLit` declines.
   *
   * The literal itself is a JS number, so a source literal above 2^53 has
   * already lost bits in the lexer; every value below that reaches `Integer`
   * exactly. */
  overloadedLit(head: string, args: CoreExpr[]): CoreExpr | undefined {
    if (args.length !== 2) return undefined;
    const [dict, lit] = args;
    if (dict.tag !== "Var") return undefined;
    if (head === "fromRational" && dict.binder === this.top.get("$fFractionalDouble")) {
      if (lit.tag !== "Lit" || lit.lit.tag !== "LitDouble") return undefined;
      return { tag: "Con", con: this.lookupCon("DoubleBox", 1), args: [lit] };
    }
    // Binder identity, not just the name: only the module's own `$fNumInt`
    // pins the type down to `Int`.
    if (head === "fromInteger" && dict.binder === this.top.get("$fNumInt")) {
      if (lit.tag !== "Lit" || lit.lit.tag !== "LitNumInt") return undefined;
      return { tag: "Con", con: this.lookupCon("I", 1), args: [lit] };
    }
    return undefined;
  }

  /** The other half of `overloadedLit`: a `fromInteger` the short-cut declined
   * still has a machine literal where its `Integer` argument belongs, so the
   * literal is boxed here. Everything else about the call is left alone. */
  boxIntegerLit(head: string, args: CoreExpr[]): CoreExpr[] {
    if (head !== "fromInteger" || args.length !== 2) return args;
    const lit = args[1]!;
    // A dictionary in the first slot is what says this is the elaborated class
    // method and not something else the source happened to call `fromInteger`.
    // A dictionary is not always a plain `Var`: under a constraint that only
    // *implies* `Num` - `Real a => a -> a`, say - the elaborator passes
    // `$p0Real dReal`, an application. Requiring a `Var` here left the machine
    // literal unboxed in exactly those bindings, so `x + 1` handed `Integer`'s
    // `fromInteger` a JS number to destructure.
    if (!isDictionaryArg(args[0]!) || lit.tag !== "Lit" || lit.lit.tag !== "LitNumInt") return args;
    const box = this.top.get("integerFromIntPrim");
    if (!box) return args;
    return [args[0]!, { tag: "App", fn: { tag: "Var", binder: box }, arg: lit }];
  }

  /** `case` and `\case` alternatives; guards inside an alternative fall
   * through to the next alternative when none succeeds. */
  /** `case <action> of IOResult s a -> body`.
   *
   * An unboxed tuple needs exactly ONE `case`, and the general path below
   * would emit two: an outer one to bring the scrutinee to WHNF and an inner
   * one to test the constructor. Both are wrong here. There is no constructor
   * to test - the fields arrive in registers - and bringing the scrutinee to
   * WHNF is precisely what must NOT happen, because the result slot of
   * `(# s, a #)` is returned unevaluated. Forcing it would make every `>>=`
   * force the value it binds.
   *
   * Only the shape the state token needs is recognised: one alternative, no
   * guards, and every field a plain variable or wildcard. */
  unboxedTupleCase(scrutinee: CoreExpr, alts: CaseAlternative[], scope: Scope): CoreExpr | undefined {
    if (alts.length !== 1) return undefined;
    const alt = alts[0]!;
    if (alt.qualifiers?.length) return undefined;
    if (alt.pattern.tag !== "con") return undefined;
    const con = this.cons.get(alt.pattern.name);
    if (!con || !isUnboxedTupleCon(con)) return undefined;
    const args = alt.pattern.args;
    if (args.length !== con.arity || args.some((a) => a.tag !== "var" && a.tag !== "wild")) return undefined;

    const fields = args.map((a) => mkBinder(patternName(a) ?? "ubx", voidArity(voidRepOf(a))));
    const names = args.flatMap((a, i): Array<[string, Binder]> => {
      const name = patternName(a);
      return name ? [[name, fields[i]!]] : [];
    });
    return {
      tag: "Case",
      scrutinee,
      // The case binder holds the tuple's slots, so it is as wide as the
      // fields that survive erasure - see `altTypeOf` in src/core-to-stg.ts.
      binder: mkBinder("ubx", { arity: fields.filter((f) => f.arity !== 0).length }),
      alts: [{ con: { tag: "DataAlt", con }, binders: fields, body: this.expr(alt.body, extend(scope, names)) }],
    };
  }

  alternatives(scrutinee: CoreExpr, alts: CaseAlternative[], scope: Scope, span: Span): CoreExpr {
    const unboxed = this.unboxedTupleCase(scrutinee, alts, scope);
    if (unboxed) return unboxed;
    const subject = scrutinee.tag === "Var" ? scrutinee.binder : mkBinder("scrut");
    const rows = alts.map((alt) => ({
      patterns: [alt.pattern],
      guards: [{ qualifiers: alt.qualifiers, body: alt.body }],
      whereBindings: [] as LocalBinding[],
    }));
    // A `Var` scrutinee still needs a real `Case` to force it: this frontend
    // has no strictness analysis, so an ordinary variable reference (a lazy
    // CAF, a lambda parameter, any binding the caller may not have forced)
    // cannot be assumed already evaluated just because it is *named*. Only
    // skipping the wrapper when the scrutinee is unboxed (never a thunk to
    // begin with) would be sound; unconditionally skipping it for every
    // `Var` silently dropped the force and shipped the raw closure to
    // whatever consumed it. Always wrapping costs an extra entry on an
    // already-evaluated/blackholed thunk, which is cheap and correct.
    return {
      tag: "Case",
      scrutinee,
      binder: subject,
      alts: [
        {
          con: { tag: "DEFAULT" },
          binders: [],
          body: this.match([subject], rows, scope, raise()),
        },
      ],
    };
  }

  /** The pattern-match compiler, in the classic left-to-right form. Rows are
   * tried in order; the first column that actually discriminates becomes a
   * `case`, and every other column is deferred by recursion. */
  match(subjects: Binder[], rows: MatchRow[], scope: Scope, fallback: CoreExpr): CoreExpr {
    if (rows.length === 0) return fallback;
    if (subjects.length === 0) return this.guardedBody(rows[0]!, scope, () => this.match([], rows.slice(1), scope, fallback));

    const column = subjects.findIndex((_, i) => rows.some((row) => isRefutable(row.patterns[i])));
    if (column < 0) {
      // Every remaining pattern binds or ignores; bind the first row's names.
      const row = rows[0]!;
      const inner = extend(scope, bindingsOf(subjects, row.patterns));
      return this.guardedBody(row, inner, () => this.match(subjects, rows.slice(1), scope, fallback));
    }

    const subject = subjects[column]!;
    const groups = new Map<string, MatchRow[]>();
    const order: Array<{ key: string; pattern: Pattern }> = [];
    const defaults: MatchRow[] = [];
    for (const row of rows) {
      const pattern = row.patterns[column]!;
      if (!isRefutable(pattern)) {
        defaults.push(row);
        // A variable row also matches every constructor seen so far and any
        // seen later, so it joins each group as well.
        for (const [, group] of groups) group.push(row);
        continue;
      }
      const key = patternKey(pattern);
      if (!groups.has(key)) {
        groups.set(key, [...defaults]);
        order.push({ key, pattern });
      }
      groups.get(key)!.push(row);
    }

    // The default rows keep every column, including this one: their pattern
    // there is a variable that still has to bind the scrutinee's name. The
    // recursion terminates anyway because the row set strictly shrinks.
    const defaultBody = (): CoreExpr => this.match(subjects, defaults, scope, fallback);

    const alts: CoreAlt[] = order.map(({ key, pattern }) => {
      const group = groups.get(key)!;
      if (pattern.tag === "char") {
        return {
          con: { tag: "LitAlt", lit: { tag: "LitChar", value: pattern.value } },
          binders: [],
          body: this.matchGroup(subjects, group, column, [], scope, fallback),
        };
      }
      if (pattern.tag === "double") {
        return {
          con: { tag: "LitAlt", lit: { tag: "LitDouble", value: pattern.value } },
          binders: [],
          body: this.matchGroup(subjects, group, column, [], scope, fallback),
        };
      }
      if (pattern.tag === "int") {
        return {
          con: { tag: "LitAlt", lit: int(pattern.value) },
          binders: [],
          body: this.matchGroup(subjects, group, column, [], scope, fallback),
        };
      }
      const con = this.lookupCon(patternConName(pattern), patternArity(pattern));
      const fields = Array.from({ length: con.arity }, (_, i) => mkBinder(`${con.name}_f${i}`));
      return {
        con: { tag: "DataAlt", con },
        binders: fields,
        body: this.matchGroup(subjects, group, column, fields, scope, fallback),
      };
    });

    const typeName = alts[0]?.con.tag === "DataAlt" ? alts[0].con.con.typeName : undefined;
    // Rows whose pattern here is a variable were merged into every
    // constructor group above, so once every constructor has an alternative
    // the DEFAULT one is unreachable.
    const exhaustive = typeName !== undefined && alts.length === this.conCount.get(typeName);
    if (exhaustive) {
      return { tag: "Case", scrutinee: { tag: "Var", binder: subject }, binder: mkBinder("c"), alts };
    }
    const missing = this.onlyMissingCon(typeName, alts);
    return {
      tag: "Case",
      scrutinee: { tag: "Var", binder: subject },
      binder: mkBinder("c"),
      alts: [
        missing === undefined
          ? { con: { tag: "DEFAULT" }, binders: [], body: defaultBody() }
          : {
              con: { tag: "DataAlt", con: missing },
              binders: Array.from({ length: missing.arity }, (_, i) => mkBinder(`${missing.name}_f${i}`)),
              body: defaultBody(),
            },
        ...alts,
      ],
    };
  }

  /** GHC's `refineDefaultAlt`: if the alternatives already name every
   * constructor of the type but one, the DEFAULT alternative can only be that
   * one constructor, so say so.
   *
   * This is not tidying. Codegen only compiles a two-alternative `Bool` case to
   * a truthiness test when BOTH alternatives are DataAlts (GHC's `genAlts`,
   * mirrored in `src/stg-js/expr.ts`); otherwise it switches on the tag word
   * `x.f.a`. But a `Bool` has no tag word - `tagToEnum#` and a nullary `True` /
   * `False` both produce a raw JS boolean - so `case b of True -> ...; _ -> ...`
   * compiled to a tag switch reads `.f` off `true` and dies. GHC never hits
   * that because it refines the DEFAULT away first. */
  onlyMissingCon(typeName: string | undefined, alts: readonly CoreAlt[]): DataCon | undefined {
    if (typeName === undefined) return undefined;
    const all = [...this.cons.values()].filter((con) => con.typeName === typeName);
    // Constructors are registered lazily, so an incomplete table would make
    // "all but one" a lie. Only trust it once it holds the whole type.
    if (all.length !== this.conCount.get(typeName)) return undefined;
    const covered = new Set(alts.flatMap((alt) => (alt.con.tag === "DataAlt" ? [alt.con.con.name] : [])));
    const missing = all.filter((con) => !covered.has(con.name));
    return missing.length === 1 ? missing[0] : undefined;
  }

  /** Inside one alternative, prepend the constructor's fields as new columns.
   *
   * The matched column is KEPT rather than dropped: a row that reached this
   * alternative through the fall-through path still has a variable pattern
   * there, and that variable has to go on binding the scrutinee. Its pattern
   * is only rewritten to a wildcard for the rows the alternative actually
   * discriminated on, which is also what stops `match` picking the same
   * column again and looping. */
  matchGroup(
    subjects: Binder[],
    group: MatchRow[],
    column: number,
    fields: Binder[],
    scope: Scope,
    fallback: CoreExpr,
  ): CoreExpr {
    const rows = group.map((row) => {
      const pattern = row.patterns[column]!;
      const matched = isRefutable(pattern);
      const inner = stripAs(pattern);
      const sub: Pattern[] =
        inner.tag === "con" && matched
          ? inner.args
          : fields.map<Pattern>(() => ({ tag: "wild", span: pattern.span }));
      const columns = row.patterns.map((p, i) => (i === column && matched ? asOnly(p) : p));
      return { ...row, patterns: [...sub, ...columns] };
    });
    return this.match([...fields, ...subjects], rows, scope, fallback);
  }

  /** One equation's guards, `where` bindings and body. */
  guardedBody(row: MatchRow, scope: Scope, next: () => CoreExpr): CoreExpr {
    if (row.core) return row.core(scope);
    const [binds, inner] = this.localGroup(row.whereBindings, scope);
    const wrap = (body: CoreExpr): CoreExpr =>
      binds.reduceRight<CoreExpr>((b, bind) => ({ tag: "Let", bind, body: b }), body);
    const chain = row.guards.reduceRight<CoreExpr>((rest, guard) => this.guard(guard, inner, rest), next());
    return wrap(forceStrict(row.whereBindings, inner, chain));
  }

  /** One `|` guard: its qualifiers left to right, falling through to `rest`
   * as soon as any of them fails. */
  private guard(guard: Guard, scope: Scope, rest: CoreExpr): CoreExpr {
    const qualifiers = guard.qualifiers ?? [];
    // A lone boolean has exactly one way to fail and uses `rest` once. Anything
    // else can reach the fall-through from several branches - a second
    // qualifier, or the pattern-match compiler's own default alternatives - so
    // the continuation is bound once instead of being copied into each of them.
    if (qualifiers.length <= 1 && qualifiers[0]?.tag !== "pattern")
      return this.qualifiers(qualifiers, guard.body, scope, () => rest);
    const bail = mkBinder("guardfail");
    const body = this.qualifiers(qualifiers, guard.body, scope, () => varOf(bail));
    return { tag: "Let", bind: { tag: "NonRec", binder: bail, rhs: rest }, body };
  }

  private qualifiers(
    qualifiers: readonly GuardQualifier[],
    body: Expr,
    scope: Scope,
    bail: () => CoreExpr,
  ): CoreExpr {
    const [first, ...rest] = qualifiers;
    if (!first) return this.expr(body, scope);
    if (first.tag === "bool")
      return this.boolCase(
        this.expr(first.condition, scope),
        () => this.qualifiers(rest, body, scope, bail),
        bail,
      );
    // `p <- e` is a one-row match through the same pattern-match compiler an
    // ordinary alternative goes through, so `p` may be nested, may be a
    // literal, and binds for everything to its right.
    const source = this.expr(first.source, scope);
    const subject = source.tag === "Var" ? source.binder : mkBinder("guard");
    const row: MatchRow = {
      patterns: [first.pattern],
      guards: [],
      whereBindings: [],
      core: (inner) => this.qualifiers(rest, body, inner, bail),
    };
    const matched = this.match([subject], [row], scope, bail());
    if (source.tag === "Var") return matched;
    return {
      tag: "Case",
      scrutinee: source,
      binder: subject,
      alts: [{ con: { tag: "DEFAULT" }, binders: [], body: matched }],
    };
  }

  /** A `let`/`where` group. Bindings with parameters become functions; the
   * group is `Rec` only when a right-hand side actually mentions the group. */
  localGroup(bindings: readonly LocalBinding[], scope: Scope): [CoreBind[], Scope] {
    if (bindings.length === 0) return [[], scope];
    // The parser emits one `LocalBinding` per *clause*, so a multi-equation
    // `where` function arrives as several entries sharing a name. Grouping them
    // back together is what makes the equations one function: without it the
    // last clause won the scope and the earlier ones were dead code, so
    // `withMaybe Nothing = pure jsNull` never ran and every call fell into the
    // `Just` clause's pattern-match failure.
    const clauses = new Map<string, LocalBinding[]>();
    for (const b of bindings) {
      const list = clauses.get(b.name);
      if (list) list.push(b);
      else clauses.set(b.name, [b]);
    }
    const names = [...clauses.keys()];
    const binders = names.map((n) => mkBinder(n));
    const inner = extend(scope, names.map((n, i) => [n, binders[i]!] as [string, Binder]));
    const rhss = names.map((name) => {
      const group = clauses.get(name)!;
      const binding = group[0]!;
      const params = binding.patterns.map((p) => mkBinder(patternName(p) ?? "arg", voidArity(voidRepOf(p))));
      const bodyScope = extend(
        inner,
        binding.patterns.flatMap((p, j) => {
          const name = patternName(p);
          return name ? [[name, params[j]!] as [string, Binder]] : [];
        }),
      );
      const rows: MatchRow[] = group.map((b) => ({
        patterns: b.patterns,
        guards: b.guards ?? [{ body: b.value }],
        whereBindings: b.whereBindings ?? [],
      }));
      const body =
        group.length === 1 && binding.patterns.every((p) => !isRefutable(p))
          ? this.guardedBody(rows[0]!, bodyScope, () => raise())
          : this.match(params, rows, inner, raise());
      return mkLams(params, body);
    });
    const groupSet = new Set(binders);
    const recursive = rhss.some((rhs) => [...coreFreeVars(rhs)].some((v) => groupSet.has(v)));
    return recursive
      ? [[{ tag: "Rec", pairs: binders.map((b, i) => [b, rhss[i]!] as [Binder, CoreExpr]) }], inner]
      : [binders.map((b, i): CoreBind => ({ tag: "NonRec", binder: b, rhs: rhss[i]! })), inner];
  }

  /** GHC's `dsFCall`: the body of a foreign import whose Haskell type says
   * more than "call this with these registers".
   *
   *   - `unboxArg`: an argument whose type is a one-field box over a primitive
   *     (`Int`, `Char`, `JSVal`, `JSString`, ...) is opened with a `case`, so
   *     JavaScript is handed the machine value rather than the heap object.
   *   - `boxResult`: a result of that shape is closed back up, and an `IO`
   *     result becomes an actual `IO` action - `IO (\s -> IOResult s r)` -
   *     rather than the raw value. Without this an `IO`-returning import
   *     evaluates at the point it is *applied*, and hands `unIO` something
   *     with no `IO` constructor to take apart.
   *
   * The call sits in a `case` scrutinee, exactly as `boxResult` puts it there:
   * a constructor field is a lazy position, and an `unsafe` foreign call
   * deferred into a thunk would run at an arbitrary later moment. */
  foreignBody(
    decl: ForeignDeclaration,
    op: StgOp,
    params: readonly Binder[],
    args: ReadonlyArray<DataCon | undefined>,
    result: DataCon | undefined,
    payload: string | undefined,
  ): CoreExpr {
    const opened = params.map((p, i) => (args[i] === undefined ? p : mkBinder(`${p.name}u`)));
    const unbox = (body: CoreExpr): CoreExpr =>
      params.reduceRight((rest, p, i) => {
        const con = args[i];
        if (con !== undefined)
          return {
            tag: "Case",
            scrutinee: varOf(p),
            binder: mkBinder(`${p.name}b`),
            alts: [{ con: { tag: "DataAlt", con }, binders: [opened[i]!], body: rest }],
          };
        // No wrapper type to unwrap, but the argument is still an ordinary
        // (possibly unevaluated) expression - a recursive call's result, a
        // thunked accumulator, anything. A primitive-typed FFI parameter is
        // handed to raw JavaScript with no representation for a Haskell
        // thunk, so it must be forced even when there is nothing to unbox.
        return {
          tag: "Case",
          scrutinee: varOf(p),
          binder: p,
          alts: [{ con: { tag: "DEFAULT" }, binders: [], body: rest }],
        };
      }, body);
    const called = call(op, decl.arity, opened);
    const box = (v: CoreExpr): CoreExpr => (result === undefined ? v : { tag: "Con", con: result, args: [v] });
    if (payload === undefined) return unbox(box(called));

    const io = this.cons.get("IO");
    const ioResult = this.cons.get("IOResult");
    if (io === undefined || ioResult === undefined) {
      this.diagnostics.push(
        error(
          "GHCTS-DESUGAR",
          `foreign import \`${decl.name}\` returns IO, but IO is not in scope`,
          this.file,
          decl.span.line,
          decl.span.column,
        ),
      );
      return unbox(box(called));
    }
    // The state token is void: it occupies no register and no payload slot.
    const state = mkBinder(`${decl.name}$s`, { arity: 0 });
    const value = mkBinder(`${decl.name}$r`);
    // `IO ()` has no result to hand back. GHC's `boxResult` drops the call's
    // value and returns the unit, which keeps a JavaScript function that
    // returns nothing from putting `undefined` where `()` belongs.
    const returned: CoreExpr = isUnitType(payload) ? { tag: "Lit", lit: int(0) } : box(varOf(value));
    const body: CoreExpr = {
      tag: "Case",
      scrutinee: called,
      binder: value,
      alts: [
        {
          con: { tag: "DEFAULT" },
          binders: [],
          body: { tag: "Con", con: ioResult, args: [varOf(state), returned] },
        },
      ],
    };
    // Unboxing goes INSIDE the state lambda: `getProp_ffi k o` only builds the
    // action, and must not force `k` until that action is run.
    return { tag: "Con", con: io, args: [mkLams([state], unbox(body))] };
  }
}

interface MatchRow {
  patterns: Pattern[];
  guards: Guard[];
  whereBindings: LocalBinding[];
  /** The one-row match a pattern guard compiles to: its body is the rest of
   * that guard, which is Core already under construction rather than a
   * surface expression, so it replaces `guards` entirely. */
  core?: (scope: Scope) => CoreExpr;
}

const varOf = (binder: Binder): CoreExpr => ({ tag: "Var", binder });

const call = (op: StgOp, arity: number, args: readonly Binder[]): CoreExpr => ({
  tag: "Op",
  op,
  arity,
  args: args.map(varOf),
});

/** The head type constructor of one `->`-separated piece of a foreign import's
 * signature, which `src/parser.ts` hands over as its tokens joined by spaces.
 * `undefined` unless the piece *begins* with a type name, so `( JSVal , JSVal )`
 * and `JSVal -> IO ()` are not mistaken for `JSVal`. */
const headTypeCon = (text: string): string | undefined => /^\s*([A-Z][A-Za-z0-9_'.]*)/.exec(text)?.[1];

/** `IO t` -> `t`; anything else -> `undefined`. `\b` keeps `IOResult a` out. */
const ioPayload = (text: string): string | undefined => /^\s*IO\b(.*)$/.exec(text)?.[1]?.trim();

const isUnitType = (text: string): boolean => text.replace(/\s+/g, "") === "()";

/** Types a foreign import marshals across: one constructor, one field, and
 * that field a primitive - GHC's `unboxArg`/`boxResult` condition that the
 * wrapped type be unlifted, spelled in this frontend's `...Prim` convention
 * (see the header of src/library.ts). `data JSVal = JSVal JSValPrim` is one;
 * `data Bool = False | True` is not, and needs none - the backend already
 * represents it as a JavaScript boolean. */
function boxTypes(module: Module, cons: ReadonlyMap<string, DataCon>): Map<string, DataCon> {
  const out = new Map<string, DataCon>();
  for (const decl of module.declarations) {
    if (decl.tag !== "data" || decl.constructors.length !== 1) continue;
    const con = decl.constructors[0]!;
    const field = headTypeCon(con.fieldTypes?.[0] ?? "");
    const dataCon = cons.get(con.name);
    if (con.arity === 1 && field?.endsWith("Prim") === true && dataCon !== undefined)
      out.set(decl.name, dataCon);
  }
  return out;
}

/** `let !x = e in b` is GHC's `case e of x -> b`: the group is still a `Let`,
 * and a `Case` on each strict binder in front of the body forces it exactly
 * where the `in` is - not earlier, and not only when `x` happens to be used. */
const forceStrict = (bindings: readonly LocalBinding[], scope: Scope, body: CoreExpr): CoreExpr =>
  bindings.reduceRight<CoreExpr>((rest, binding) => {
    const binder = binding.strict ? scope.get(binding.name) : undefined;
    return binder
      ? { tag: "Case", scrutinee: varOf(binder), binder: mkBinder("$bang"), alts: [{ con: { tag: "DEFAULT" }, binders: [], body: rest }] }
      : rest;
  }, body);


/** Pattern-match failure. `RaiseDivZeroOp` is the only nullary raising primop
 * the JS backend implements; a real `PatternMatchFail` needs an exception
 * closure, which needs `Control.Exception`, which needs classes. */
const raise = (): CoreExpr => ({ tag: "Op", op: { tag: "StgPrimOp", op: "RaiseDivZeroOp" }, arity: 0, args: [] });

const extend = (scope: Scope, entries: Array<[string, Binder]>): Scope =>
  entries.length === 0 ? scope : new Map([...scope, ...entries]);

function flattenApp(e: Expr): [Expr, Expr[]] {
  const args: Expr[] = [];
  let head: Expr = e;
  while (head.tag === "app") {
    args.unshift(head.arg);
    head = head.fn;
  }
  return [head, args];
}

/** A missing pattern means the equation has fewer arguments than its
 * siblings. That is an arity error, and the elaborator already reports it as
 * one; crashing here would replace a good diagnostic with a stack trace, so
 * an absent column is treated as irrefutable and the build carries on to
 * report everything else it finds. */
/** `xs@(y : ys)` discriminates on what it wraps; the name it binds is kept
 * separately, by `asOnly` below.  Every question the match compiler asks about
 * a column - is it refutable, which constructor, how many fields - is a
 * question about the wrapped pattern. */
const stripAs = (p: Pattern): Pattern => (p.tag === "as" ? stripAs(p.pattern) : p);

/** The same column once its alternative has matched: the constructor test is
 * spent, but the as-names still have to bind the scrutinee, so what is left is
 * irrefutable and binds exactly those names. */
const asOnly = (p: Pattern): Pattern =>
  p.tag === "as" ? { ...p, pattern: asOnly(p.pattern) } : { tag: "wild", span: p.span };

const isRefutable = (p: Pattern | undefined): boolean => {
  if (p === undefined) return false;
  const q = stripAs(p);
  return q.tag === "int" || q.tag === "double" || q.tag === "string" || q.tag === "char" || q.tag === "con" || q.tag === "record";
};

/** A binder at the void state token occupies no JS value; everything else
 * takes the default (one slot). See `Binder.arity` in src/stg.ts. */
const voidArity = (voidRep: true | undefined): Partial<Binder> => (voidRep ? { arity: 0 } : {});

const voidRepOf = (p: Pattern): true | undefined =>
  p.tag === "var" || p.tag === "wild" ? p.voidRep : undefined;

/** See `Pattern.notFun` in src/ast.ts.
 *
 * A `var`/`wild` column only knows this if the elaborator wrote its type down
 * (`Pattern.notFun`). Every *refutable* column knows it outright, and needs no
 * type at all: a constructor, record or literal pattern can only ever be
 * matched against a value of that data type, so the subject standing at that
 * column is a heap constructor and never a bare function. That is exactly the
 * fact `genApp` wants in order to emit `h$e(x)` instead of routing the value
 * through the generic apply, and it is the common case in the Prelude - every
 * instance method written `(+) (I a) (I b) = ...` forces both arguments
 * through such a column.
 *
 * `newtype` is included deliberately: unlike GHC, ghcts never erases a
 * newtype's constructor (see `elaborate.ts`'s deriving-newtype note), so a
 * value matched against one is a real single-field closure here regardless of
 * what it wraps. */
const notFunOf = (p: Pattern): true | undefined =>
  p.tag === "var" || p.tag === "wild"
    ? p.notFun
    : p.tag === "con" || p.tag === "record" || p.tag === "int" || p.tag === "char" || p.tag === "string"
      ? true
      : undefined;

const patternName = (p: Pattern): string | undefined =>
  p.tag === "var" ? p.name : p.tag === "as" ? p.name : undefined;

/** Every name an irrefutable column binds, outermost first: `xs@ys@_` binds
 * both, and each one binds the whole subject. */
const patternNames = (p: Pattern, out: string[] = []): string[] => {
  if (p.tag === "var") out.push(p.name);
  if (p.tag === "as") {
    out.push(p.name);
    patternNames(p.pattern, out);
  }
  return out;
};

const patternSpan = (p: Pattern): Span => p.span;
const patternConName = (p: Pattern): string => {
  const q = stripAs(p);
  return q.tag === "con" ? q.name : q.tag === "record" ? q.name : "?";
};
const patternArity = (p: Pattern): number => {
  const q = stripAs(p);
  return q.tag === "con" ? q.args.length : 0;
};
const patternKey = (p: Pattern): string => {
  const q = stripAs(p);
  return q.tag === "int" || q.tag === "double" ? `#${q.value}` : q.tag === "string" ? `s${q.value}` : q.tag === "char" ? `q${q.value}` : `c${patternConName(q)}`;
};

function bindingsOf(subjects: Binder[], patterns: Pattern[]): Array<[string, Binder]> {
  const out: Array<[string, Binder]> = [];
  patterns.forEach((p, i) => {
    // The only funnel through which an irrefutable column reaches the binder
    // that stands for it, which makes it the one place the elaborator's
    // void mark can be carried onto that binder. A wildcard at the state
    // token binds no name but still has to erase its argument register.
    if (voidRepOf(p) && subjects[i]) subjects[i]!.arity = 0;
    // ... and the same funnel for the one type fact codegen reads, GHC's
    // `mightBeFunTy (idType i)` (see `Binder.mightBeFun` in src/stg.ts).
    if (notFunOf(p) && subjects[i]) subjects[i]!.mightBeFun = false;
    for (const name of patternNames(p)) out.push([name, subjects[i]!]);
  });
  return out;
}

/** An elaborated dictionary argument: a dictionary binding, or a superclass
 * selector or instance function applied to further dictionaries. */
function isDictionaryArg(e: CoreExpr): boolean {
  let head = e;
  while (head.tag === "App") head = head.fn;
  return head.tag === "Var";
}

export function desugarModule(module: Module, file = `${module.name}.hs`): DesugarResult {
  const d = new Desugarer(file);

  for (const decl of module.declarations) {
    if (decl.tag === "data") {
      const unboxed = UNBOXED_TUPLE_TYPES.has(decl.name);
      decl.constructors.forEach((con, i) => {
        const name = unboxed ? unboxedTupleName(con.arity) : con.name;
        d.cons.set(con.name, mkDataCon(name, i + 1, con.arity, unboxed ? name : decl.name));
      });
      d.conCount.set(unboxed ? unboxedTupleName(decl.constructors[0]?.arity ?? 0) : decl.name, decl.constructors.length);
    } else if (decl.tag === "class") {
      for (const member of decl.members) if ("name" in member) d.classMethods.add(member.name);
      d.diagnostics.push(
        error(
          "GHCTS-DESUGAR",
          `class \`${decl.name}\`: dictionary elaboration is not implemented yet`,
          file,
          decl.span.line,
          decl.span.column,
        ),
      );
    } else if (decl.tag === "instance") {
      d.diagnostics.push(
        error(
          "GHCTS-DESUGAR",
          `instance \`${decl.head}\`: dictionary elaboration is not implemented yet`,
          file,
          decl.span.line,
          decl.span.column,
        ),
      );
    }
  }

  const values = module.declarations.filter(isValue);
  const foreigns = module.declarations.filter(isForeign);
  for (const decl of [...values, ...foreigns]) d.top.set(decl.name, mkBinder(decl.name, { exported: true }));

  const binds: CoreBind[] = [];

  const boxes = boxTypes(module, d.cons);
  for (const decl of foreigns) {
    // A foreign import is a saturated foreign call under enough lambdas to
    // consume its declared arguments; `arity` comes from the signature's
    // top-level arrows.
    const params = Array.from({ length: decl.arity }, (_, i) => mkBinder(`ffi${i}`));
    const op: StgOp = {
      tag: "StgFCallOp",
      target: { javascript: decl.javascript, safety: "unsafe" },
    };
    // The declared type is not decoration: JavaScript is handed machine
    // values, and every one of `getProp_ffi :: JSString -> JSVal -> IO JSVal`'s
    // three is a heap object in Haskell. GHC's desugarer bridges that in
    // `dsFCall` (GHC/HsToCore/Foreign/Call.hs) with `unboxArg` on each
    // argument and `boxResult` on the result, and this is that pair.
    const payload = ioPayload(decl.signature[decl.arity] ?? "");
    const result = boxes.get(headTypeCon(payload ?? decl.signature[decl.arity] ?? "") ?? "");
    const args = Array.from({ length: decl.arity }, (_, i) => boxes.get(headTypeCon(decl.signature[i] ?? "") ?? ""));
    const marshalled = payload !== undefined || result !== undefined || args.some((a) => a !== undefined);
    // Without marshalling the wrapper is the bare call, and a saturated use of
    // it can go straight to the call itself (see `foreignOps`). With it, the
    // wrapper IS the marshalling and inlining the call would skip it.
    if (!marshalled) d.foreignOps.set(decl.name, { op, arity: decl.arity });
    binds.push({
      tag: "NonRec",
      binder: d.top.get(decl.name)!,
      rhs: mkLams(params, marshalled ? d.foreignBody(decl, op, params, args, result, payload) : call(op, decl.arity, params)),
    });
  }

  for (const decl of values) {
    const arity = decl.equations[0]?.patterns.length ?? 0;
    const params = Array.from({ length: arity }, (_, i) => mkBinder(`a${i}`));
    const rows: MatchRow[] = decl.equations.map((eq) => ({
      patterns: eq.patterns,
      guards: eq.guards,
      whereBindings: eq.whereBindings,
    }));
    const body = d.match(params, rows, d.top, raise());
    binds.push({ tag: "NonRec", binder: d.top.get(decl.name)!, rhs: mkLams(params, body) });
  }

  return {
    // An unboxed tuple has no worker: there is no closure to enter, so GHC
    // emits no `_con_e` for one and neither does this.
    program: { name: module.name, binds, dataCons: [...d.cons.values()].filter((c) => !isUnboxedTupleCon(c)) },
    diagnostics: d.diagnostics,
  };
}

const isValue = (d: Declaration): d is Extract<Declaration, { tag: "value" }> => d.tag === "value";
const isForeign = (d: Declaration): d is Extract<Declaration, { tag: "foreign" }> => d.tag === "foreign";
