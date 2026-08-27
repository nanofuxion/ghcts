/** Ported from GHC/StgToJS/FFI.hs (GHC 9.12.2): `genForeignCall`, `genPrimCall`.
 *
 * Note [the FFI "pattern" is not a pattern in 9.12]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The `$1`/`$2`/`$r` holes in the header comment of FFI.hs are GHCJS history.
 * `parseFFIPattern'` in 9.12.2 never looks at the string: both of its guards
 * run the same `mkApply pat`, which turns the whole import string into a
 * *global* (`global (mkFastString f)`) and applies it. So the import string
 * must be a JavaScript expression denoting a function - `"h$foo"` or
 * `"((x,y) => x+y)"` - and the results come back in the return registers
 * `h$ret1`, `h$ret2`, ... rather than through `$r1`/`$r2` splices. This port
 * keeps that behaviour exactly; see `rejectHoles` for the one addition, which
 * turns a GHCJS-style pattern into a compile error instead of emitting
 * `$1 + $2(a,b)`.
 */
import type { Ident } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { Var, global } from "../js/jstg-syntax.js";
import {
  assignAllEqual,
  assign_,
  declAssign_,
  idx_,
  jAdd,
  jhFromList,
  null_,
  one_,
  returnS,
  sel_,
  strictEq_,
  toJExpr,
} from "../js/make.js";
import { mconcatJStgStat, memptyJStgStat } from "../js/jstg-syntax.js";
import type { ForeignCall, StgArg } from "../stg.js";
import type { ExprCtx } from "./expr-ctx.js";
import { ctxSrcSpan, ctxTarget } from "./expr-ctx.js";
import type { ExprResult } from "./expr.js";
import { freshIdent, varForId, varForIdN } from "./ids.js";
import { genLit } from "./literal.js";
import type { CCallConv, GenState, Safety } from "./monad.js";
import { emitForeign, getSettings } from "./monad.js";
import { jsRegsFromR1, sp, stack } from "./regs.js";
import { hdMVar, hdStrStr, hdTakeMVar, hdUnboxFFIResult } from "./symbols.js";
import { idIsMultiVar, idIsVoid, idSlotCount } from "./utils.js";

// ---------------------------------------------------------------------------
// GHC.StgToJS.Symbols bindings that scripts/gen-symbols.mjs does not emit
// (it only scans the generated-symbol table, and these four are hand-written
// in Symbols.hs).
// ---------------------------------------------------------------------------

const hdThrowJSException: JStgExpr = global("h$throwJSException");
const hdMkForeignCallback: JStgExpr = global("h$mkForeignCallback");
const hdTraceForeign: JStgExpr = global("h$traceForeign");
/** `exceptStr = name (fsLit "except")`, and `except = global (identFS exceptStr)`. */
const exceptStr = "except";
const except: JStgExpr = global(exceptStr);
/** `mv = fsLit "mv"` - the MVar field of the async-call result object. */
const mv = "mv";

/** `GHC.Types.ForeignCall.playSafe` / `playInterruptible`. */
const playSafe = (s: Safety): boolean => s !== "unsafe";
const playInterruptible = (s: Safety): boolean => s === "interruptible";

/** ghcts's `ForeignCall` only models `foreign import javascript`, so the
 * calling convention is always JavaScriptCallConv. The CCallConv branches of
 * `genForeignCall` (the `ghczuwrapperZC` prefix strip and the `h$` prefix) are
 * therefore unreachable and are not reproduced. */
const cconv: CCallConv = "JavaScriptCallConv";

export function genPrimCall(
  gs: GenState,
  ctx: ExprCtx,
  lbl: string,
  args: StgArg[],
): [JStgStat, ExprResult] {
  const j = parseFFIPattern(gs, false, false, false, hdStrStr + lbl, targetExprs(ctx), args);
  return [j, "ExprInline"];
}

export function genForeignCall(
  gs: GenState,
  ctx: ExprCtx,
  fc: ForeignCall,
  tgt: JStgExpr[],
  args: StgArg[],
): [JStgStat, ExprResult] {
  const safety = fc.safety;
  const lbl = fc.javascript;
  rejectHoles(lbl);

  // (cconv == JavaScriptCallConv && playSafe safety) || playInterruptible safety
  const catchExcep = (playSafe(safety) && true) || playInterruptible(safety);
  const async = playInterruptible(safety);
  // An async call returns through the registers, not through the case binder's
  // slots, so the targets are the first `length tgt` registers from R1.
  const tgt_ = async ? takeGen(jsRegsFromR1(), tgt.length) : tgt;

  // ghcts has no Core `Type` for the call, so the argument/result type names
  // GHC renders with `ppr tc` are unavailable; `<unknown>` is what showType
  // itself falls back to.
  emitForeign(gs, ctxSrcSpan(ctx), lbl, safety, cconv, args.map(() => unknownType), unknownType);

  const stat = parseFFIPattern(gs, catchExcep, async, true, lbl, tgt_, args);
  return [stat, async ? "ExprCont" : "ExprInline"];
}

const unknownType = "<unknown>";

function takeGen(g: Generator<JStgExpr>, n: number): JStgExpr[] {
  const out: JStgExpr[] = [];
  for (const x of g) {
    if (out.length >= n) break;
    out.push(x);
  }
  return out;
}

const targetExprs = (ctx: ExprCtx): JStgExpr[] => ctxTarget(ctx).flatMap((t) => t.expr);

/** GHCJS's `$1`/`$r` splices would silently render as garbage here, since the
 * whole string becomes a JS identifier. Reject them with the reason. */
function rejectHoles(pat: string): void {
  if (/\$(r|\d)/.test(pat)) {
    throw new Error(
      `genForeignCall: GHCJS-style FFI pattern ${JSON.stringify(pat)} is not supported. ` +
        "GHC 9.12 requires the import string to be a JavaScript expression denoting a " +
        "function; extra results are returned in h$ret1, h$ret2, ...",
    );
  }
}

function parseFFIPattern(
  gs: GenState,
  catchExcep: boolean,
  async: boolean,
  jscc: boolean,
  pat: string,
  es: JStgExpr[],
  as: StgArg[],
): JStgStat {
  if (!catchExcep) return parseFFIPatternA(gs, async, jscc, pat, es, as);
  const c = parseFFIPatternA(gs, async, jscc, pat, es, as);
  // try { `c`; } catch(except) { return h$throwJSException(except); }
  return {
    tag: "TryStat",
    body: c,
    ident: exceptStr,
    catch: returnS({ tag: "ApplExpr", fn: hdThrowJSException, args: [except] }),
    finally: memptyJStgStat,
  };
}

function parseFFIPatternA(
  gs: GenState,
  async: boolean,
  jscc: boolean,
  pat: string,
  es: JStgExpr[],
  as: StgArg[],
): JStgStat {
  if (!(async && jscc)) return parseFFIPattern_(gs, undefined, jscc, pat, es, as);

  // async calls get an extra callback argument; call it with the result
  const cb: Ident = freshIdent(gs);
  const x: Ident = freshIdent(gs);
  const d: Ident = freshIdent(gs);
  const stat = parseFFIPattern_(gs, Var(cb), true, pat, es, as);
  const xe = Var(x);
  // `typeSize t` counts the JS slots of the call's result type. ghcts has no
  // Type here, but `es` is exactly those slots (see parseFFIPattern_), so its
  // length is the same number.
  const nrst = es.length;
  return mconcatJStgStat([
    declAssign_(x, toJExpr(jhFromList([[mv, null_]]))),
    declAssign_(cb, { tag: "ApplExpr", fn: hdMkForeignCallback, args: [xe] }),
    stat,
    {
      tag: "IfStat",
      cond: strictEq_(sel_(xe, mv), null_),
      // The callback has not fired yet: block the thread on a fresh MVar and
      // push h$unboxFFIResult, which the callback's take will return into.
      then: mconcatJStgStat([
        assign_(sel_(xe, mv), { tag: "UOpExpr", op: "NewOp", value: { tag: "ApplExpr", fn: hdMVar, args: [] } }),
        assign_(sp, jAdd(sp, one_)),
        assign_(idx_(stack, sp), hdUnboxFFIResult),
        returnS({ tag: "ApplExpr", fn: hdTakeMVar, args: [sel_(xe, mv)] }),
      ]),
      // It fired synchronously: the result array is already there.
      else: mconcatJStgStat([
        declAssign_(d, sel_(xe, mv)),
        assignAllEqual(es, Array.from({ length: nrst }, (_, i) => idx_(Var(d), { tag: "ValExpr", value: { tag: "JInt", value: BigInt(i) } }))),
      ]),
    },
  ]);
}

function parseFFIPattern_(
  gs: GenState,
  callback: JStgExpr | undefined,
  javascriptCc: boolean,
  pat: string,
  ret: JStgExpr[],
  args: StgArg[],
): JStgStat {
  // GHC: `tgt = take (typeSize t) ret`. `ret` is already exactly the target
  // slots the caller wants filled, so the take is the identity here.
  const tgt = ret;
  const f_ = global(pat);
  const marshalled = args.map((a) => genFFIArg(gs, javascriptCc, a));
  const stats = mconcatJStgStat(marshalled.map(([s]) => s));
  const as = marshalled.flatMap(([, e]) => e);
  const trace = getSettings(gs).traceForeign
    ? ({ tag: "ApplStat", fn: hdTraceForeign, args: [{ tag: "ValExpr", value: { tag: "JStr", value: pat } }, { tag: "ValExpr", value: { tag: "JList", values: as } }] } as JStgStat)
    : memptyJStgStat;

  if (callback !== undefined) {
    return mconcatJStgStat([trace, stats, { tag: "ApplStat", fn: f_, args: [...as, callback] }]);
  }
  if (tgt.length > 0) {
    // The first result is the call's value; the rest come out of h$ret1...
    const rest = tgt.slice(1);
    return mconcatJStgStat([
      trace,
      stats,
      assign_(tgt[0], { tag: "ApplExpr", fn: f_, args: as }),
      mconcatJStgStat(rest.map((r, n) => assign_(r, foreignRet(n)))),
    ]);
  }
  return mconcatJStgStat([trace, stats, { tag: "ApplStat", fn: f_, args: as }]);
}

/** `enumFrom Ret1 !! n` as a JStgExpr - `h$ret1`, `h$ret2`, ... */
const foreignRet = (n: number): JStgExpr => global(`h$ret${n + 1}`);

/** Generate an arg to be passed to an FFI call, with the marshalling statement
 * to run before the call.
 *
 * CONSERVATIVE: GHC's first clause passes a ByteArray#/MutableByteArray# as
 * `(arr, 0)` for the C calling convention. ghcts models only
 * JavaScriptCallConv, where that clause is guarded off anyway
 * (`not isJavaScriptCc`), and it has no Core Type to test the TyCon with. */
function genFFIArg(gs: GenState, _isJavaScriptCc: boolean, a: StgArg): [JStgStat, JStgExpr[]] {
  if (a.tag === "StgLitArg") return [memptyJStgStat, genLit(gs, a.lit)];
  const i = a.id;
  if (idIsVoid(i)) return [memptyJStgStat, []];
  if (idIsMultiVar(i)) {
    return [memptyJStgStat, Array.from({ length: idSlotCount(i) }, (_, n) => varForIdN(gs, i, n + 1))];
  }
  return [memptyJStgStat, [varForId(gs, i)]];
}
