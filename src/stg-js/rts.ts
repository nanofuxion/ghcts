/** Ported from GHC/StgToJS/Rts/Rts.hs - the generated half of the JS RTS.
 *
 * GHC's `rts.js` is exactly `jsOptimize (jStgStatToJS <$> rts cfg)` and
 * nothing else: the static `rts/js/*.js` files are ordinary package JS
 * sources, which the linker concatenates into `lib.js` instead. That split
 * makes this module a self-contained, diffable target - the oracle's rts.js
 * is 611 symbols, and scripts/oracle-diff.mjs scores against it.
 */
import { global, memptyJStgStat, mconcatJStgStat, New, type JStgExpr, type JStgStat } from "../js/jstg-syntax.js";
import { name, type Ident } from "../js/ident.js";
import { initJSM, type JSM } from "../js/jstg-monad.js";
import { jsOptimize } from "../js/optimizer.js";
import { renderStat } from "../js/ppr.js";
import { jStgStatToJS } from "../js/transform.js";
import {
  app,
  appS,
  assign_,
  decl,
  false_,
  gt_,
  idx_,
  ifS,
  if_,
  jAdd,
  jBlock,
  jFunction_,
  jFunctionSized,
  jInt,
  jString,
  jSub,
  jVar,
  jVars,
  jwhenS,
  land_,
  le_,
  loop_,
  lt_,
  null_,
  postIncrS,
  returnS,
  returnStack,
  sel_,
  strictEq_,
  strictNeq_,
  toJExpr,
  true_,
  typeOf,
  undefined_,
  zero_,
} from "../js/make.js";
import {
  hdAp00FastStr,
  hdAp10,
  hdAp11Fast,
  hdAp1EntryStr,
  hdAp22FastStr,
  hdAp2EntryStr,
  hdAp33FastStr,
  hdAp3EntryStr,
  hdAtomicallyEntry,
  hdAtomicallyEntryStr,
  hdBhStr,
  hdBlackHole,
  hdBlackHoleLNEStr,
  hdBlackHoleStr,
  hdBlackHoleTrapStr,
  hdC0,
  hdCAFsResetStr,
  hdCAFsStr,
  hdCatchEntryStr,
  hdClosureTypeNameStr,
  hdCollectProps,
  hdCurrentThread,
  hdCurrentThreadStr,
  hdData1Entry,
  hdData2Entry,
  hdDataToTagEntryStr,
  hdDone,
  hdDoneMain,
  hdDoneMainEntryStr,
  hdDumpResStr,
  hdFalseEntry,
  hdFinishedThread,
  hdFlushStdoutEntry,
  hdFlushStdoutEntryStr,
  hdFlushStdoutStr,
  hdGetRegStr,
  hdGhcInternalIOHandleFDStdout,
  hdGhcInternalIOHandleFlush,
  hdInitStaticStr,
  hdInternalExceptionControlExceptionBaseNonTermination,
  hdKeepAliveEntryStr,
  hdLazyEntryStr,
  hdLogStr,
  hdMaskFrameStr,
  hdMaskUnintFrameStr,
  hdNoopEntry,
  hdNoopEntryStr,
  hdNoopStr,
  hdRaiseAsyncEntryStr,
  hdRaiseAsyncFrameStr,
  hdRaiseEntryStr,
  hdReduceStr,
  hdRegsStr,
  hdReportHeapOverflowStr,
  hdReportStackOverflowStr,
  hdReschedule,
  hdRescheduleStr,
  hdRestoreCCSStr,
  hdRestoreThreadStr,
  hdResumeEntryStr,
  hdRetryInterruptedStr,
  hdReturn,
  hdReturnFStr,
  hdReturnStr,
  hdRtsProfiling,
  hdRtsTraceForeign,
  hdRunIOEntryStr,
  hdSelect1EntryStr,
  hdSelect1Ret,
  hdSelect1RetStr,
  hdSelect2EntryStr,
  hdSelect2Return,
  hdSelect2ReturnStr,
  hdSetCcsEntryStr,
  hdSetRegStr,
  hdStackPtrStr,
  hdStackStr,
  hdStaticThunkStr,
  hdStaticThunksArrStr,
  hdStaticThunksStr,
  hdStgResumeRetryEntryStr,
  hdStmCatchEntryStr,
  hdStmCatchRetryEntryStr,
  hdStmCommitTransactionStr,
  hdStmRemoveBlockedThreadStr,
  hdStmStartTransactionStr,
  hdStmValidateTransactionStr,
  hdThrowStr,
  hdTrueEntry,
  hdUnboxEntryStr,
  hdUnboxFFIResultStr,
  hdUnMaskFrameStr,
  hdUpdFrame,
  hdUpdThunkEntryStr,
  hdC0Str,
  hdCStr,
  hdResetRegisters,
  hdResetResultVars,
} from "./symbols.js";
import { jsRegToInt, lowRegs, register, regsFromR1, retRegs, sp, stack, R1, R2, R3, R4 } from "./regs.js";
import { closure, clsName, conClosure, dataFieldName, dataName, jsClosureCount, mkClosure, newClosure } from "./closure.js";
import { closureCC_, closureField1, closureField1_, closureField2, closureField2_, closureInfo, isThunk, jTyObject } from "./heap.js";
import { adjSpN_, adjSp_, bhStats, push_, pushN, pushNN, updateThunk_ } from "./stack.js";
import { rtsApply } from "./apply.js";
import {
  ciFun,
  ciLayoutFixed,
  ciLayoutUnknown,
  ciLayoutVariable,
  ciRegs,
  ciStackFrame,
  ciThunk,
  ciBlackhole,
  closureInfo as mkClosureInfo,
  ClosureType,
  closureTypeName as closureTypeNameOf,
  closureTypeToJExpr,
  ctNum,
  defaultStgToJSConfig,
  JSRep,
  type CILayout,
  type CIType,
  type CIRegs,
  type StgToJSConfig,
} from "./types.js";

/** GHC.JS.Make's `x ||= e`: declare a global and assign it in one statement. */
const globalAssign = (n: string, e: JStgExpr): JStgStat => ({ tag: "DeclStat", ident: name(n), value: e });

const jsNull: JStgExpr = { tag: "ValExpr", value: { tag: "JVar", ident: name("null") } };
const emptyArray: JStgExpr = { tag: "ValExpr", value: { tag: "JList", values: [] } };
const emptyObject: JStgExpr = { tag: "ValExpr", value: { tag: "JHash", entries: [] } };

/** Rts.hs generates 32 register loaders. */
const loaderCount = 32;

/** `h$l1 .. h$l32`. Symbols.hs builds `hdLoads` by name rather than as a
 * literal, so it is not among symbols.ts's generated exports. */
const hdLoads = (n: number): Ident => name(`h$l${n}`);

/** declRegs - `h$regs`, `h$r1..h$r31`, the getters/setters, and the loaders. */
export function declRegs(js: JSM): JStgStat {
  return mconcatJStgStat([
    globalAssign(hdRegsStr, emptyArray),
    mconcatJStgStat(lowRegs.map((r): JStgStat => ({ tag: "DeclStat", ident: r, value: zero_ }))),
    regGettersSetters(js),
    loadRegs(js),
  ]);
}

/** regGettersSetters - `h$getReg`/`h$setReg`, switching on the register
 * number. There is a case for every one of the 128 registers, and the switch
 * default is `mempty` - a bare `default:` with no body.
 *
 * The names `setters`/`getters` are swapped upstream (the binding called
 * `setters` builds h$getReg); kept verbatim so the emission order - h$getReg
 * then h$setReg - matches. */
export function regGettersSetters(js: JSM): JStgStat {
  const setters = jFunctionSized(js, name(hdGetRegStr), 1, ([n]) => ({
    tag: "SwitchStat",
    scrut: n!,
    cases: regsFromR1.map((r): [JStgExpr, JStgStat] => [jInt(jsRegToInt(r)), returnS(register(r))]),
    default: memptyJStgStat,
  }));
  const getters = jFunctionSized(js, name(hdSetRegStr), 2, ([n, v]) => ({
    tag: "SwitchStat",
    scrut: n!,
    cases: regsFromR1.map((r): [JStgExpr, JStgStat] => [
      jInt(jsRegToInt(r)),
      // a `return undefined;`, not a `break`
      mconcatJStgStat([assign_(register(r), v!), returnS(undefined_)]),
    ]),
    default: memptyJStgStat,
  }));
  return mconcatJStgStat([setters, getters]);
}

/** loadRegs - `h$l1 .. h$l32`. `h$l4(a, b, c, d)` sets R4=a, R3=b, R2=c,
 * R1=d: arguments fill registers in *descending* order, so a call site can
 * pass its arguments in ordinary left-to-right order. */
export function loadRegs(js: JSM): JStgStat {
  const mkLoad = (n: number): JStgStat =>
    jFunctionSized(js, hdLoads(n), n, (args) => {
      const targets = regsFromR1.slice(0, n).reverse();
      return mconcatJStgStat(args.map((a, i) => assign_(register(targets[i]!), a)));
    });
  return mconcatJStgStat(range(1, loaderCount).map(mkLoad));
}

/** assignRegs - assign R1..Rn in descending order, Rn first. At 32 registers
 * or fewer this calls the shared `h$lN` loader instead of inlining the
 * assignments, unless -fjs-inline-load-regs says otherwise. */
export function assignRegs(s: StgToJSConfig, xs: JStgExpr[]): JStgStat {
  if (xs.length === 0) return memptyJStgStat;
  const l = xs.length;
  if (l <= 32 && !s.inlineLoadRegs)
    return { tag: "ApplStat", fn: { tag: "ValExpr", value: { tag: "JVar", ident: hdLoads(l) } }, args: [...xs].reverse() };
  const targets = regsFromR1.slice(0, l);
  return mconcatJStgStat(xs.map((ex, i) => assign_(register(targets[i]!), ex)).reverse());
}

/** garbageCollector - `h$resetRegisters` / `h$resetResultVars`.
 *
 * Both "reset" by assigning the *global named* `null` (GHC.JS.Make.null_),
 * not JS's nil literal. 9.12.2 resets every one of the 128 registers one by
 * one; there is no `h$regs.fill(null)` shortcut. */
export function garbageCollector(js: JSM): JStgStat {
  return jBlock([
    jFunctionSized(js, name(hdResetRegisters), 0, () =>
      mconcatJStgStat(regsFromR1.map((r) => assign_(register(r), jsNull))),
    ),
    jFunctionSized(js, name(hdResetResultVars), 0, () =>
      mconcatJStgStat(retRegs.map((r) => assign_(global(r), jsNull))),
    ),
  ]);
}

/** declRets - declare the return variables `h$ret1..h$ret10`. */
export const declRets: JStgStat = mconcatJStgStat(retRegs.map(decl));

const allClosureTypes = [
  ClosureType.Thunk,
  ClosureType.Fun,
  ClosureType.Pap,
  ClosureType.Con,
  ClosureType.Blackhole,
  ClosureType.StackFrame,
];

/** closureTypes - `h$closureTypeName`, mapping a closure tag back to its
 * name. Both halves go through GHC's own instances: the tag compared against
 * is `toJExpr ct` (which is `ctNum`), and the name returned is `show ct`.
 * So tag 4 names nothing and tag 5 is Blackhole - StackFrame's tag is -1. */
export function closureTypes(js: JSM): JStgStat {
  const closureTypeName = jFunctionSized(js, name(hdClosureTypeNameStr), 1, ([c]) =>
    mconcatJStgStat([
      ...allClosureTypes.map((ct) => jwhenS(strictEq_(c!, closureTypeToJExpr(ct)), returnS(jString(closureTypeNameOf(ct))))),
      returnS(jString("InvalidClosureType")),
    ]),
  );
  return mconcatJStgStat([
    // GHC.StgToJS.Types.closureNames: "h$" ++ map toUpper (show ct) ++ "_CLOSURE".
    ...allClosureTypes.map((ct) => globalAssign(`h$${closureTypeNameOf(ct).toUpperCase()}_CLOSURE`, closureTypeToJExpr(ct))),
    closureTypeName,
  ]);
}

/** The `h$ct_*` closure tags and `h$vt_*` representation tags that generated
 * code compares against. `ctNum` - not the derived Enum - supplies the values
 * here, which is why `h$ct_stackframe` is -1. */
export const closureTypeConstants = (s: StgToJSConfig): JStgStat => mconcatJStgStat([
  globalAssign(hdRtsTraceForeign, toJExpr(s.traceForeign)),
  globalAssign(hdRtsProfiling, toJExpr(s.prof)),
  globalAssign("h$ct_fun", jInt(ctNum(ClosureType.Fun))),
  globalAssign("h$ct_con", jInt(ctNum(ClosureType.Con))),
  globalAssign("h$ct_thunk", jInt(ctNum(ClosureType.Thunk))),
  globalAssign("h$ct_pap", jInt(ctNum(ClosureType.Pap))),
  globalAssign("h$ct_blackhole", jInt(ctNum(ClosureType.Blackhole))),
  globalAssign("h$ct_stackframe", jInt(ctNum(ClosureType.StackFrame))),
  globalAssign("h$vt_ptr", jInt(JSRep.PtrV)),
  globalAssign("h$vt_void", jInt(JSRep.VoidV)),
  globalAssign("h$vt_int", jInt(JSRep.IntV)),
  globalAssign("h$vt_double", jInt(JSRep.DoubleV)),
  globalAssign("h$vt_long", jInt(JSRep.LongV)),
  globalAssign("h$vt_addr", jInt(JSRep.AddrV)),
  globalAssign("h$vt_obj", jInt(JSRep.ObjV)),
  globalAssign("h$vt_arr", jInt(JSRep.ArrV)),
]);

/** rtsDecls - the RTS's globals, declared before anything runs. */
export function rtsDecls(js: JSM): JStgStat {
  return mconcatJStgStat([
    globalAssign(hdCurrentThreadStr, jsNull),
    globalAssign(hdStackStr, jsNull),
    globalAssign(hdStackPtrStr, jInt(0)),
    // Static objects need delayed initialization; functions are pushed here
    // to be run just before Haskell starts.
    globalAssign(hdInitStaticStr, emptyArray),
    globalAssign(hdStaticThunksStr, emptyObject),
    globalAssign(hdStaticThunksArrStr, emptyArray),
    globalAssign(hdCAFsStr, emptyArray),
    globalAssign(hdCAFsResetStr, emptyArray),
    declRegs(js),
    declRets,
  ]);
}

/** closureConstructors - `h$c`, `h$c0..h$c24` and the `h$d1..h$d24` field
 * fillers.
 *
 * These exist for the JIT's benefit: allocating through a fixed set of
 * constructors keeps every closure of a given size monomorphic, which hand-
 * rolled object literals at each allocation site would not. Note `h$c1` takes
 * *two* arguments - the entry function plus one data field - so the 1 counts
 * data fields, not parameters. */
export function closureConstructors(js: JSM, s: StgToJSConfig): JStgStat {
  const ccVal = s.prof ? global(closureCC_) : undefined;
  const ccArg: JStgExpr[] = s.prof ? [global(closureCC_)] : [];

  // `h$c` and `h$c0` both take only an entry function; GHC gives them their
  // own case because they carry no data field to name.
  const singletonClosureCon = (n: string): JStgStat =>
    jFunctionSized(js, name(n), 1, ([f]) =>
      jVar(js, (x) => mconcatJStgStat([assign_(x, newClosure(mkClosure(f!, [], jInt(0), ccVal))), returnS(x)])),
    );

  const mkClosureCon = (n: number | undefined): JStgStat => {
    if (n === undefined) return singletonClosureCon(hdCStr);
    if (n === 0) return singletonClosureCon(hdC0Str);
    return jFunctionSized(js, name(clsName(n)), n + 1, (args) => {
      const [f, ...vars] = args;
      return jVar(js, (x) =>
        mconcatJStgStat([assign_(x, newClosure(mkClosure(f!, [...vars, ...ccArg], jInt(0), ccVal))), returnS(x)]),
      );
    });
  };

  // h$dN returns a plain object of named fields, used for closures whose
  // payload outgrows the two inline d1/d2 slots.
  const mkDataFill = (n: number): JStgStat =>
    jFunctionSized(js, name(dataName(n)), n, (args) =>
      returnS({
        tag: "ValExpr",
        value: { tag: "JHash", entries: args.map((a, i): [string, JStgExpr] => [dataFieldName(i + 1), a]) },
      }),
    );

  return mconcatJStgStat([
    ...[undefined, ...range(0, jsClosureCount)].map(mkClosureCon),
    ...range(1, jsClosureCount).map(mkDataFill),
  ]);
}

/** The set bit indices of `n`, least significant first. */
export function bitsIdx(n: number): number[] {
  if (n < 0) throw new Error("bitsIdx: negative");
  const out: number[] = [];
  let m = n;
  for (let b = 0; m !== 0; b++) {
    if (m & (1 << b)) out.push(b);
    m &= ~(1 << b);
  }
  return out;
}

/** stackManip - `h$p1..h$p32` and the partial pushes `h$pp<bitmap>`.
 *
 * `h$pN` pushes N consecutive slots. A partial push takes a bitmap naming
 * which slots of the frame are actually being written, and raises Sp by the
 * highest set bit; a bitmap whose bits are all consecutive from 0 is exactly
 * what `h$pN` already does, so those are skipped. */
export function stackManip(js: JSM): JStgStat {
  const mkPush = (n: number): JStgStat =>
    jFunctionSized(js, pushN[n]!, n, (args) =>
      mconcatJStgStat([
        assign_(sp, jAdd(sp, jInt(n))),
        ...args.map((a, i) => assign_(idx_(stack, jSub(sp, jInt(n - (i + 1)))), a)),
      ]),
    );

  const mkPpush = (sig: number): JStgStat => {
    if ((sig & (sig + 1)) === 0) return memptyJStgStat; // already an h$pN
    const bits = bitsIdx(sig);
    const h = bits[bits.length - 1]!;
    return jFunctionSized(js, pushNN[sig]!, bits.length, (args) =>
      mconcatJStgStat([
        assign_(sp, jAdd(sp, jInt(h + 1))),
        ...bits.map((b, i) => assign_(idx_(stack, jSub(sp, jInt(h - b))), args[i]!)),
      ]),
    );
  };

  return mconcatJStgStat([...range(1, 32).map(mkPush), ...range(1, 255).map(mkPpush)]);
}

// ---------------------------------------------------------------------------
//                     rts_gen's `impure` list (Rts.hs:383-680)
// ---------------------------------------------------------------------------

/** Property names GHC keeps in Symbols.hs as bare FastStrings rather than
 * `hd*` symbols, so scripts/gen-symbols.mjs does not pick them up. They are
 * plain JS field/method names, not RTS entry points. */
const excepStr = "excep";
const lngth = "length";
const slice = "slice";
const substring = "substring";
const replace = "replace";
const hasOwnProperty = "hasOwnProperty";
const d1Str = "d1";
const d2Str = "d2";
const d3Str = "d3";
const maskStr = "mask";
const unMask = "unmask";
const resume = "resume";
const fStr = "f";
const nStr = "n";
const traceStr = "trace";
/** GHC writes `appS throwStr` for the JS `throw` keyword; not an h$ symbol. */
const throwStr = "throw";
const console_: JStgExpr = global("console");
const this_: JStgExpr = global("this");

/** GHC.StgToJS.Profiling is not ported; rts_gen needs only these three
 * bindings, and all of them vanish unless -prof is on. */
const jSystemCCS: JStgExpr = global("h$CCS_SYSTEM");
const enterCostCentreThunk: JStgStat = { tag: "ApplStat", fn: global("h$enterThunkCCS"), args: [sel_(register(R1), closureCC_)] };
const profStat = (cfg: StgToJSConfig, e: JStgStat): JStgStat => (cfg.prof ? e : memptyJStgStat);

const r1 = register(R1);
const r2 = register(R2);
const r3 = register(R3);
const r4 = register(R4);

const ptr = JSRep.PtrV;
const objV = JSRep.ObjV;

/** `h$stack[h$sp - n]`, the workhorse of every stack frame below. */
const stackAt = (n: number): JStgExpr => idx_(stack, jSub(sp, jInt(n)));
const topOfStack: JStgExpr = idx_(stack, sp);

const ci = (v: string, regs: CIRegs, n: string, layout: CILayout, t: CIType): Parameters<typeof closure>[1] =>
  mkClosureInfo(v, regs, n, layout, t);

/** Black-hole a let-no-escape thunk. Unlike `bhStats` there is no closure to
 * overwrite - the "thunk" is a stack frame - so the marker goes into the stack
 * slot itself, and re-entering it is <<loop>>. */
export function bhLneStats(js: JSM, _s: StgToJSConfig, p: JStgExpr, frameSize: JStgExpr): JStgStat {
  return jVar(js, (v) =>
    mconcatJStgStat([
      assign_(v, idx_(stack, p)),
      ifS(
        v,
        mconcatJStgStat([
          assign_(sp, jSub(sp, frameSize)),
          ifS(
            strictEq_(v, hdBlackHole),
            returnS(app(hdThrowStr, [hdInternalExceptionControlExceptionBaseNonTermination, false_])),
            mconcatJStgStat([assign_(r1, v), assign_(sp, jSub(sp, frameSize)), returnStack]),
          ),
        ]),
        mconcatJStgStat([assign_(idx_(stack, p), hdBlackHole), returnS(null_)]),
      ),
    ]),
  );
}

/** The apply-N entry points share a shape: unpack N fields out of the thunk,
 * black-hole it, load them into R1..Rn and tail-call `h$ap_n_n_fast`. */
function apNEntry(js: JSM, s: StgToJSConfig, sym: string, nm: string, n: number, fast: string, prof: boolean): JStgStat {
  const regs = [r1, r2, r3, r4];
  const fields = [d1Str, d2Str, d3Str];
  return closure(js, ci(sym, ciRegs(0, [ptr]), nm, ciLayoutFixed(n + 1, Array.from({ length: n + 1 }, () => ptr)), ciThunk), () =>
    jVars(js, n + 1, (ds) =>
      mconcatJStgStat([
        assign_(ds[0]!, closureField1(r1)),
        ...ds.slice(1).map((d, i) => assign_(d, n === 1 ? closureField2(r1) : sel_(closureField2(r1), fields[i]!))),
        appS(hdBhStr, []),
        prof ? profStat(s, enterCostCentreThunk) : memptyJStgStat,
        ...ds.map((d, i) => assign_(regs[i]!, d)),
        returnS(app(fast, [])),
      ]),
    ),
  );
}

/** `h$select1_e` / `h$select2_e`: a thunk that forces its argument and then
 * projects one field, leaving `retSym` on the stack to do the projection. */
function selectEntry(js: JSM, sym: string, nm: string, retSym: JStgExpr): JStgStat {
  return closure(js, ci(sym, ciRegs(0, [ptr]), nm, ciLayoutFixed(1, [ptr]), ciThunk), () =>
    jVar(js, (t) =>
      mconcatJStgStat([
        assign_(t, closureField1(r1)),
        adjSp_(3),
        assign_(stackAt(2), r1),
        assign_(stackAt(1), hdUpdFrame),
        assign_(topOfStack, retSym),
        assign_(closureInfo(r1), hdBlackHole),
        assign_(closureField1(r1), hdCurrentThread),
        assign_(closureField2(r1), null_),
        assign_(r1, t),
        returnS(app(hdAp00FastStr, [])),
      ]),
    ),
  );
}

/** `h$maskFrame` / `h$maskUnintFrame`: set the thread's mask and fall through. */
function maskFrame(js: JSM, sym: string, nm: string, level: number): JStgStat {
  return closure(js, ci(sym, ciRegs(0, [ptr]), nm, ciLayoutFixed(0, []), ciStackFrame), () =>
    mconcatJStgStat([assign_(sel_(hdCurrentThread, maskStr), jInt(level)), adjSpN_(1), returnS(topOfStack)]),
  );
}

/** `h$reportHeapOverflow` / `h$reportStackOverflow`. */
function overflowFrame(js: JSM, sym: string, message: string): JStgStat {
  return closure(js, ci(sym, ciRegs(0, [ptr]), sym, ciLayoutFixed(0, []), ciStackFrame), () =>
    appS(throwStr, [jString(message)]),
  );
}

/** `rts_gen`'s `impure` list, verbatim in source order - concatenation order
 * is the emission order of rts.js. */
function rtsImpure(js: JSM, s: StgToJSConfig): JStgStat {
  return mconcatJStgStat([
    jFunction_(name(hdBhStr), bhStats(s, true)),
    jFunctionSized(js, name(hdBlackHoleLNEStr), 2, ([x, frameSize]) => bhLneStats(js, s, x!, frameSize!)),
    closure(js, ci(hdBlackHoleStr, ciRegs(0, []), "blackhole", ciLayoutUnknown(2), ciBlackhole), () =>
      appS(throwStr, [jString("oops: entered black hole")]),
    ),
    closure(js, ci(hdBlackHoleTrapStr, ciRegs(0, []), "blackhole", ciLayoutUnknown(2), ciThunk), () =>
      appS(throwStr, [jString("oops: entered multiple times")]),
    ),
    closure(js, ci(hdDone, ciRegs(0, [ptr]), "done", ciLayoutUnknown(0), ciStackFrame), () =>
      mconcatJStgStat([appS(hdFinishedThread, [hdCurrentThread]), returnS(hdReschedule)]),
    ),
    closure(js, ci(hdDoneMainEntryStr, ciRegs(0, [ptr]), "doneMain", ciLayoutUnknown(0), ciStackFrame), () => returnS(hdDoneMain)),
    conClosure(js, hdFalseEntry, "GHC.Types.False", ciLayoutFixed(0, []), 1),
    conClosure(js, hdTrueEntry, "GHC.Types.True", ciLayoutFixed(0, []), 2),
    // generic data constructor with 1 non-heapobj field
    conClosure(js, hdData1Entry, "data1", ciLayoutFixed(1, [objV]), 1),
    // generic data constructor with 2 non-heapobj fields
    conClosure(js, hdData2Entry, "data2", ciLayoutFixed(2, [objV, objV]), 1),
    closure(js, ci(hdNoopEntryStr, ciRegs(1, [ptr]), "no-op IO ()", ciLayoutFixed(0, []), ciFun(1, 0)), () => returnS(topOfStack)),
    globalAssign(hdNoopStr, { tag: "ApplExpr", fn: hdC0, args: [hdNoopEntry, ...(s.prof ? [jSystemCCS] : [])] }),
    closure(js, ci(hdCatchEntryStr, ciRegs(0, [ptr]), "exception handler", ciLayoutFixed(2, [ptr, JSRep.IntV]), ciStackFrame), () =>
      mconcatJStgStat([adjSpN_(3), returnS(topOfStack)]),
    ),
    closure(js, ci(hdDataToTagEntryStr, ciRegs(0, [ptr]), "data to tag", ciLayoutFixed(0, []), ciStackFrame), () =>
      mconcatJStgStat([
        // `true` is its own tag-1 value; any other object carries its tag in
        // the info table's `a` field, one-based, and everything else is 0.
        assign_(r1, if_(strictEq_(r1, true_), jInt(1), if_(strictEq_(typeOf(r1), jTyObject), jSub(sel_(sel_(r1, fStr), "a"), jInt(1)), jInt(0)))),
        adjSpN_(1),
        returnS(topOfStack),
      ]),
    ),
    // function application to one/two/three arguments
    apNEntry(js, s, hdAp1EntryStr, "apply1", 1, hdAp11Fast, true),
    apNEntry(js, s, hdAp2EntryStr, "apply2", 2, hdAp22FastStr, true),
    // NB: no enterCostCentreThunk here - Rts.hs omits it for ap3 only
    apNEntry(js, s, hdAp3EntryStr, "apply3", 3, hdAp33FastStr, false),
    closure(js, ci(hdUpdThunkEntryStr, ciRegs(0, [ptr]), "updatable thunk", ciLayoutFixed(1, [ptr]), ciThunk), () =>
      jVar(js, (t) =>
        mconcatJStgStat([
          assign_(t, closureField1(r1)),
          adjSp_(2),
          assign_(stackAt(1), r1),
          assign_(topOfStack, hdUpdFrame),
          assign_(closureInfo(r1), hdBlackHole),
          assign_(closureField1(r1), hdCurrentThread),
          assign_(closureField2(r1), null_),
          assign_(r1, t),
          returnS(app(hdAp00FastStr, [])),
        ]),
      ),
    ),
    // select first field
    selectEntry(js, hdSelect1EntryStr, "select1", hdSelect1Ret),
    closure(js, ci(hdSelect1RetStr, ciRegs(0, [ptr]), "select1ret", ciLayoutFixed(0, []), ciStackFrame), () =>
      mconcatJStgStat([assign_(r1, closureField1(r1)), adjSpN_(1), returnS(app(hdAp00FastStr, []))]),
    ),
    // select second field of a two-field constructor
    selectEntry(js, hdSelect2EntryStr, "select2", hdSelect2Return),
    closure(js, ci(hdSelect2ReturnStr, ciRegs(0, [ptr]), "select2ret", ciLayoutFixed(0, []), ciStackFrame), () =>
      mconcatJStgStat([assign_(r1, closureField2(r1)), adjSpN_(1), returnS(app(hdAp00FastStr, []))]),
    ),
    closure(js, ci(hdKeepAliveEntryStr, ciRegs(0, [ptr]), "keepAlive", ciLayoutFixed(1, [ptr]), ciStackFrame), () =>
      mconcatJStgStat([adjSpN_(2), returnS(topOfStack)]),
    ),
    // a thunk that just raises a synchronous exception
    closure(js, ci(hdRaiseEntryStr, ciRegs(0, [ptr]), hdRaiseEntryStr, ciLayoutFixed(0, []), ciThunk), () =>
      returnS(app(hdThrowStr, [closureField1(r1), false_])),
    ),
    closure(js, ci(hdRaiseAsyncEntryStr, ciRegs(0, [ptr]), hdRaiseAsyncEntryStr, ciLayoutFixed(0, []), ciThunk), () =>
      returnS(app(hdThrowStr, [closureField1(r1), true_])),
    ),
    closure(js, ci(hdRaiseAsyncFrameStr, ciRegs(0, []), hdRaiseAsyncFrameStr, ciLayoutFixed(1, []), ciStackFrame), () =>
      jVar(js, (ex) => mconcatJStgStat([assign_(ex, stackAt(1)), adjSpN_(2), returnS(app(hdThrowStr, [ex, true_]))])),
    ),
    // reduce result if it's a thunk, follow if it's an ind. Add this to the
    // stack if you want the outermost result to always be reduced to whnf,
    // and not an ind.
    closure(js, ci(hdReduceStr, ciRegs(0, [ptr]), hdReduceStr, ciLayoutFixed(0, []), ciStackFrame), () =>
      ifS(isThunk(r1), returnS(sel_(r1, fStr)), mconcatJStgStat([adjSpN_(1), returnS(topOfStack)])),
    ),
    rtsApply(js, s),
    closureTypes(js),
    closure(js, ci(hdRunIOEntryStr, ciRegs(0, [ptr]), "runio", ciLayoutFixed(1, [ptr]), ciThunk), () =>
      mconcatJStgStat([
        assign_(r1, closureField1(r1)),
        assign_(idx_(stack, { tag: "UOpExpr", op: "PreIncOp", value: sp }), hdAp10),
        returnS(hdAp10),
      ]),
    ),
    closure(js, ci(hdFlushStdoutEntryStr, ciRegs(0, []), "flushStdout", ciLayoutFixed(0, []), ciThunk), () =>
      mconcatJStgStat([
        assign_(r1, hdGhcInternalIOHandleFlush),
        assign_(r2, hdGhcInternalIOHandleFDStdout),
        returnS(app(hdAp11Fast, [])),
      ]),
    ),
    globalAssign(hdFlushStdoutStr, app(hdStaticThunkStr, [hdFlushStdoutEntry])),
    // the scheduler pushes this frame when suspending a thread that has not
    // called h$reschedule explicitly
    closure(js, ci(hdRestoreThreadStr, ciRegs(0, []), "restoreThread", ciLayoutVariable, ciStackFrame), () =>
      jVars(js, 3, ([f, frameSize, nregs]) => {
        const setRegs = loop_(js, jInt(1), (i) => le_(i, nregs!), (i) =>
          mconcatJStgStat([appS(hdSetRegStr, [i, idx_(stack, jSub(jSub(sp, jInt(2)), i))]), postIncrS(i)]),
        );
        return mconcatJStgStat([
          assign_(f!, stackAt(2)),
          assign_(frameSize!, stackAt(1)),
          assign_(nregs!, jSub(frameSize!, jInt(3))),
          setRegs,
          assign_(sp, jSub(sp, frameSize!)),
          returnS(f!),
        ]);
      }),
    ),
    // return a closure in the stack frame to the next thing on the stack
    closure(js, ci(hdReturnStr, ciRegs(0, []), "return", ciLayoutFixed(1, [ptr]), ciStackFrame), () =>
      mconcatJStgStat([assign_(r1, stackAt(1)), adjSpN_(2), returnS(topOfStack)]),
    ),
    // return a function in the stack frame for the next call
    closure(js, ci(hdReturnFStr, ciRegs(0, [ptr]), "returnf", ciLayoutFixed(1, [objV]), ciStackFrame), () =>
      jVar(js, (r) => mconcatJStgStat([assign_(r, stackAt(1)), adjSpN_(2), returnS(r)])),
    ),
    // return this function when the scheduler needs to come into action (yield,
    // delay etc); the returning thread must push all relevant registers to the
    // stack frame, and will be resumed by calling the stack top
    closure(js, ci(hdRescheduleStr, ciRegs(0, []), "reschedule", ciLayoutFixed(0, []), ciThunk), () => returnS(hdReschedule)),
    // debug thing, insert on stack to dump current result, should be boxed
    closure(js, ci(hdDumpResStr, ciRegs(0, [ptr]), "dumpRes", ciLayoutFixed(1, [objV]), ciThunk), () =>
      jVar(js, (re) =>
        mconcatJStgStat([
          appS(hdLogStr, [jAdd(jString("h$dumpRes result: "), stackAt(1))]),
          appS(hdLogStr, [r1]),
          appS(hdLogStr, [app(hdCollectProps, [r1])]),
          jwhenS(land_(sel_(r1, fStr), sel_(sel_(r1, fStr), nStr)), appS(hdLogStr, [jAdd(jString("name: "), sel_(sel_(r1, fStr), nStr))])),
          jwhenS({ tag: "ApplExpr", fn: sel_(r1, hasOwnProperty), args: [jString(closureField1_)] }, appS(hdLogStr, [jAdd(jString("d1: "), closureField1(r1))])),
          jwhenS({ tag: "ApplExpr", fn: sel_(r1, hasOwnProperty), args: [jString(closureField2_)] }, appS(hdLogStr, [jAdd(jString("d2: "), closureField2(r1))])),
          jwhenS(
            sel_(r1, fStr),
            mconcatJStgStat([
              assign_(re, New(app("RegExp", [jString("([^\\n]+)\\n(.|\\n)*")]))),
              appS(hdLogStr, [
                jAdd(jString("function"), {
                  tag: "ApplExpr",
                  fn: sel_({ tag: "ApplExpr", fn: sel_(jAdd(jString(""), sel_(r1, fStr)), substring), args: [jInt(0), jInt(50)] }, replace),
                  args: [r1, jString("$1")],
                }),
              ]),
            ]),
          ),
          adjSpN_(2),
          assign_(r1, null_),
          returnS(topOfStack),
        ]),
      ),
    ),
    closure(js, ci(hdResumeEntryStr, ciRegs(0, [ptr]), resume, ciLayoutFixed(0, []), ciThunk), () =>
      jVar(js, (ss) => {
        const updateStk = loop_(js, jInt(0), (i) => lt_(i, sel_(ss, lngth)), (i) =>
          mconcatJStgStat([assign_(idx_(stack, jAdd(jAdd(sp, jInt(1)), i)), idx_(ss, i)), postIncrS(i)]),
        );
        return mconcatJStgStat([
          assign_(ss, closureField1(r1)),
          updateThunk_(s),
          updateStk,
          assign_(sp, jAdd(sp, sel_(ss, lngth))),
          assign_(r1, null_),
          returnS(topOfStack),
        ]);
      }),
    ),
    closure(js, ci(hdUnMaskFrameStr, ciRegs(0, [ptr]), unMask, ciLayoutFixed(0, []), ciStackFrame), () =>
      mconcatJStgStat([
        assign_(sel_(hdCurrentThread, maskStr), jInt(0)),
        adjSpN_(1),
        // back to scheduler to give us async exception if pending
        ifS(
          gt_(sel_(sel_(hdCurrentThread, excepStr), lngth), jInt(0)),
          mconcatJStgStat([push_(s, [r1, hdReturn]), returnS(hdReschedule)]),
          returnS(topOfStack),
        ),
      ]),
    ),
    maskFrame(js, hdMaskFrameStr, maskStr, 2),
    maskFrame(js, hdMaskUnintFrameStr, "maskUnint", 1),
    closure(js, ci(hdUnboxFFIResultStr, ciRegs(0, [ptr]), "unboxFFI", ciLayoutFixed(0, []), ciStackFrame), () =>
      jVar(js, (d) => {
        const setRegs = loop_(js, jInt(0), (i) => lt_(i, sel_(d, lngth)), (i) =>
          mconcatJStgStat([appS(hdSetRegStr, [jAdd(i, jInt(1)), idx_(d, i)]), postIncrS(i)]),
        );
        return mconcatJStgStat([assign_(d, closureField1(r1)), setRegs, adjSpN_(1), returnS(topOfStack)]);
      }),
    ),
    closure(js, ci(hdUnboxEntryStr, ciRegs(0, [ptr]), "unboxed value", ciLayoutFixed(1, [JSRep.DoubleV]), ciThunk), () =>
      mconcatJStgStat([assign_(r1, closureField1(r1)), returnS(topOfStack)]),
    ),
    closure(js, ci(hdRetryInterruptedStr, ciRegs(0, [objV]), "retry interrupted operation", ciLayoutFixed(1, [objV]), ciStackFrame), () =>
      jVar(js, (a) =>
        mconcatJStgStat([
          assign_(a, stackAt(1)),
          adjSpN_(2),
          returnS({
            tag: "ApplExpr",
            fn: sel_(idx_(a, jInt(0)), "apply"),
            args: [this_, { tag: "ApplExpr", fn: sel_(a, slice), args: [jInt(1)] }],
          }),
        ]),
      ),
    ),
    closure(js, ci(hdAtomicallyEntryStr, ciRegs(0, [ptr]), "atomic operation", ciLayoutFixed(1, [ptr]), ciStackFrame), () =>
      ifS(
        app(hdStmValidateTransactionStr, []),
        mconcatJStgStat([appS(hdStmCommitTransactionStr, []), adjSpN_(2), returnS(topOfStack)]),
        returnS(app(hdStmStartTransactionStr, [stackAt(1)])),
      ),
    ),
    closure(js, ci(hdStmCatchRetryEntryStr, ciRegs(0, [ptr]), "catch retry", ciLayoutFixed(1, [ptr]), ciStackFrame), () =>
      mconcatJStgStat([adjSpN_(2), appS(hdStmCommitTransactionStr, []), returnS(topOfStack)]),
    ),
    closure(js, ci(hdStmCatchEntryStr, ciRegs(0, [ptr]), "STM catch", ciLayoutFixed(3, [objV, ptr, objV]), ciStackFrame), () =>
      mconcatJStgStat([adjSpN_(4), appS(hdStmCommitTransactionStr, []), returnS(topOfStack)]),
    ),
    closure(js, ci(hdStgResumeRetryEntryStr, ciRegs(0, [ptr]), "resume retry", ciLayoutFixed(0, []), ciStackFrame), () =>
      jVar(js, (blocked) =>
        mconcatJStgStat([
          jwhenS(strictNeq_(stackAt(2), hdAtomicallyEntry), appS(throwStr, [jString("h$stmResumeRetry_e: unexpected value on stack")])),
          assign_(blocked, stackAt(1)),
          adjSpN_(2),
          appS(hdStmRemoveBlockedThreadStr, [blocked, hdCurrentThread]),
          returnS(app(hdStmStartTransactionStr, [stackAt(1)])),
        ]),
      ),
    ),
    closure(js, ci(hdLazyEntryStr, ciRegs(0, [ptr]), "generic lazy value", ciLayoutFixed(0, []), ciThunk), () =>
      jVar(js, (x) =>
        mconcatJStgStat([
          assign_(x, { tag: "ApplExpr", fn: closureField1(r1), args: [] }),
          appS(hdBhStr, []),
          profStat(s, enterCostCentreThunk),
          assign_(r1, x),
          returnS(topOfStack),
        ]),
      ),
    ),
    overflowFrame(js, hdReportHeapOverflowStr, "h$reportHeapOverflow: Heap Overflow!"),
    overflowFrame(js, hdReportStackOverflowStr, "h$reportStackOverflow: Stack Overflow!"),
    // Top-level statements to generate only in profiling mode
    profStat(
      s,
      closure(js, ci(hdSetCcsEntryStr, ciRegs(0, [ptr]), "set cost centre stack", ciLayoutFixed(1, [objV]), ciStackFrame), () =>
        mconcatJStgStat([appS(hdRestoreCCSStr, [stackAt(1)]), adjSpN_(2), returnS(topOfStack)]),
      ),
    ),
  ]);
}

/** rts - the whole generated RTS: `rtsDecls <> rts_gen cfg`. */
export function rts(js: JSM, cfg: StgToJSConfig = defaultStgToJSConfig): JStgStat {
  return js.withTag("h$RTS", (env) =>
    mconcatJStgStat([
      rtsDecls(env),
      garbageCollector(env),
      closureTypeConstants(cfg),
      closureConstructors(env, cfg),
      stackManip(env),
      rtsImpure(env, cfg),
    ]),
  );
}

/** Render `rts.js` exactly as GHC.StgToJS.Linker.Linker does. */
export function renderRts(cfg: StgToJSConfig = defaultStgToJSConfig): string {
  const js = initJSM();
  return renderStat(jsOptimize(jStgStatToJS(rts(js, cfg))));
}

function range(from: number, to: number): number[] {
  return Array.from({ length: to - from + 1 }, (_, i) => from + i);
}
function take<T>(gen: Generator<T>, n: number): T[] {
  const out: T[] = [];
  for (const value of gen) {
    if (out.length >= n) break;
    out.push(value);
  }
  return out;
}
