/** Ported from GHC/StgToJS/Apply.hs - expression application in JavaScript.
 *
 * This module carries the pre-generated "apply" machinery bundled with the RTS
 * (`rtsApply`): the specialized `h$ap_N_M`/`h$ap_N_M_fast` families, the PAP
 * entry points, the generic `h$ap_gen`/`h$ap_gen_fast` fallbacks, `h$e`, the
 * update frames, the thunk selectors and `h$moveRegs2`.
 *
 * The Core-facing half of Apply.hs (genApp, jumpToII, jumpToFast, pushCont,
 * getIdFields, storeIdFields) is NOT ported: it needs ExprCtx, Ids, the `G`
 * monad, Core `Id` and `StgArg`, none of which exist in ghcts yet. Everything
 * those functions consume from this module - ApplySpec, specApplyName,
 * specTagExpr, selectApply - is ported and exported, so genApp can be dropped
 * in later without touching this file.
 *
 * Two other small dependencies are inlined rather than given their own module,
 * since only Apply.hs uses them here: GHC.StgToJS.Profiling's `profStat` /
 * `jCurrentCCS` / `pushRestoreCCS` / `enterCostCentreFun`, and
 * GHC.StgToJS.DataCon's `allocDynamic` / `allocDynamicE`.
 */
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { global, memptyJStgStat, mconcatJStgStat } from "../js/jstg-syntax.js";
import type { JSM } from "../js/jstg-monad.js";
import {
  app,
  appS,
  assign_,
  bor_,
  gt_,
  ge_,
  ifBlockS,
  ifS,
  jAdd,
  jFunctionSized,
  jFunction_,
  jInt,
  jMul,
  jString,
  jSub,
  jVar,
  jVars,
  jwhenS,
  lor_,
  land_,
  lt_,
  mask8,
  null_,
  postDecrS,
  postIncrS,
  preIncrS,
  returnS,
  returnStack,
  sel_,
  shl_,
  shr_,
  strictEq_,
  strictNeq_,
  toJExpr,
  loop_,
  idx_,
  zero_,
} from "../js/make.js";
import {
  allocClsA,
  assignClosure,
  closure,
  copyClosure,
  CopyCC,
  jsClosureCount,
  mkClosure,
  newClosure,
  type Closure,
} from "./closure.js";
import {
  closureField1,
  closureField2,
  closureInfo,
  closureMeta,
  closureCC,
  funOrPapArity,
  infoClosureType,
  infoFunArity,
  isBlackhole,
  isFun_,
  isPap_,
  isThunk,
  jTyObject,
  papArity,
} from "./heap.js";
import {
  highReg_expr,
  jsReg,
  jsRegsFromR2,
  maxLowReg,
  R1,
  regNumber,
  register,
  sp,
  stack,
} from "./regs.js";
import { assertRts, clName, traceRts } from "./rts-types.js";
import { adjSpN_, popSkip, push_ } from "./stack.js";
import {
  hdApGenStr,
  hdApplyStr,
  hdApply,
  hdApGen,
  hdAp00,
  hdBlockOnBlackHoleStr,
  hdCSelStr,
  hdCurrentThread,
  hdEntryStr,
  hdGetRegStr,
  hdInitClosure,
  hdMoveRegs2,
  hdPapGenStr,
  hdPaps,
  hdPapsStr,
  hdPapStr_,
  hdReturn,
  hdSetRegStr,
  hdUnboxEntry,
  hdWakeupThread,
} from "./symbols.js";
import {
  ciLayoutFixed,
  ciLayoutUnknown,
  ciLayoutVariable,
  ciRegs,
  ciRegsUnknown,
  ClosureType,
  closureTypeToJExpr,
  JSRep,
  noStatic,
  type ClosureInfo,
  type StgToJSConfig,
} from "./types.js";

// ---------------------------------------------------------------------------
// Names GHC computes rather than exporting as literals from Symbols.hs.
// ---------------------------------------------------------------------------

/** `hdApGenFastStr = hdApGenStr ++ "_fast"` */
const hdApGenFastStr = `${hdApGenStr}_fast`;

/** `hdUpdFrameStr = name $ fsLit "h$upd_frame"` */
const hdUpdFrameStr = "h$upd_frame";

/** GHC writes `appS throwStr` with the JS keyword, not an h$ RTS symbol. */
const throwStr = "throw";

/** GHC.StgToJS.Symbols.typeof - `app typeof [x]` renders as `typeof(x)`. */
const typeofStr = "typeof";

const r1: JStgExpr = register(R1);

// ---------------------------------------------------------------------------
// GHC.StgToJS.Profiling (inlined - see the module header)
// ---------------------------------------------------------------------------

const hdEnterFunCCS: JStgExpr = global("h$enterFunCCS");
const hdPushRestoreCCS: JStgExpr = global("h$pushRestoreCCS");

export const jCurrentCCS: JStgExpr = sel_(hdCurrentThread, "ccs");

export const pushRestoreCCS: JStgStat = { tag: "ApplStat", fn: hdPushRestoreCCS, args: [] };

/** `enterCostCentreFun currentCCS` - the only instantiation Apply.hs uses, so
 * the `isCurrentCCS` branch is the only one that can be taken. */
export const enterCostCentreFunCurrentCCS: JStgStat = {
  tag: "ApplStat",
  fn: hdEnterFunCCS,
  args: [jCurrentCCS, sel_(r1, "cc")],
};

export const profStat = (cfg: StgToJSConfig, e: JStgStat): JStgStat => (cfg.prof ? e : memptyJStgStat);

// ---------------------------------------------------------------------------
// GHC.StgToJS.DataCon (inlined - see the module header)
// ---------------------------------------------------------------------------

function allocDynamicE(inlineAlloc: boolean, entry: JStgExpr, free: JStgExpr[], cc?: JStgExpr): JStgExpr {
  if (inlineAlloc || free.length > jsClosureCount) return newClosure(mkClosure(entry, free, zero_, cc));
  return { tag: "ApplExpr", fn: allocClsA(free.length), args: [entry, ...free, ...(cc === undefined ? [] : [cc])] };
}

function allocDynamic(
  s: StgToJSConfig,
  needDecl: boolean,
  to: Ident,
  entry: JStgExpr,
  free: JStgExpr[],
  cc?: JStgExpr,
): JStgStat {
  const value = allocDynamicE(s.inlineAlloc, entry, free, cc);
  return needDecl ? { tag: "DeclStat", ident: to, value } : assign_(toJExpr(to), value);
}

// ---------------------------------------------------------------------------
//                              rtsApply
// ---------------------------------------------------------------------------

/** Pre-generated functions for fast Apply. These are bundled with the RTS. */
export function rtsApply(js: JSM, cfg: StgToJSConfig): JStgStat {
  return mconcatJStgStat([
    mconcatJStgStat(applySpec.map((spec) => specApply(js, cfg, spec))),
    mconcatJStgStat(specPap.map((r) => pap(js, cfg, r))),
    mkApplyArr(js),
    genericStackApply(js, cfg),
    genericFastApply(js, cfg),
    zeroApply(js, cfg),
    updates(js, cfg),
    papGen(js, cfg),
    selectors(js, cfg),
    moveRegs2(js),
  ]);
}

// ---------------------------------------------------------------------------
//                             Apply specs
// ---------------------------------------------------------------------------

/** Calling convention for an apply function. */
export enum ApplyConv {
  /** Fast calling convention: use registers */
  RegsConv = 0,
  /** Slow calling convention: use the stack */
  StackConv = 1,
}

/** Apply specification */
export interface ApplySpec {
  /** Calling convention */
  specConv: ApplyConv;
  /** number of Haskell arguments */
  specArgs: number;
  /** number of JavaScript variables for the arguments */
  specVars: number;
}

/** Name of the generic apply function */
export const genericApplyName = (conv: ApplyConv): string =>
  conv === ApplyConv.RegsConv ? hdApGenFastStr : hdApGenStr;

/** Expr of the generic apply function */
export const genericApplyExpr = (conv: ApplyConv): JStgExpr => global(genericApplyName(conv));

/** Return the name of the specialized apply function for the given number of
 * args, number of arg variables, and calling convention. */
export function specApplyName(spec: ApplySpec): string {
  return `h$ap_${spec.specArgs}_${spec.specVars}${spec.specConv === ApplyConv.RegsConv ? "_fast" : ""}`;
}

/** Return the expression of the specialized apply function.
 *
 * Warning: the returned function may not be generated! Use
 * specApplyExprMaybe if you want to ensure that it exists. */
export const specApplyExpr = (spec: ApplySpec): JStgExpr => global(specApplyName(spec));

/** As specApplyExpr, but undefined if the function isn't generated. */
export function specApplyExprMaybe(spec: ApplySpec): JStgExpr | undefined {
  return applySpec.some((s) => specEq(s, spec)) ? specApplyExpr(spec) : undefined;
}

const specEq = (a: ApplySpec, b: ApplySpec): boolean =>
  a.specConv === b.specConv && a.specArgs === b.specArgs && a.specVars === b.specVars;

/** List of specialized apply function templates */
export const applySpec: ApplySpec[] = (() => {
  const out: ApplySpec[] = [];
  for (const conv of [ApplyConv.RegsConv, ApplyConv.StackConv])
    for (let nargs = 0; nargs <= 4; nargs++)
      for (let nvars = Math.max(0, nargs - 1); nvars <= nargs * 2; nvars++)
        out.push({ specConv: conv, specArgs: nargs, specVars: nvars });
  return out;
})();

/** Generate a tag for the given ApplySpec.
 *
 * Warning: tag doesn't take into account the calling convention. */
export const specTag = (spec: ApplySpec): number => (spec.specVars << 8) | spec.specArgs;

/** Generate a tag expression for the given ApplySpec */
export const specTagExpr = (spec: ApplySpec): JStgExpr => jInt(specTag(spec));

/** Find a specialized application function if there is one. Returns the
 * function to call plus whether it is the generic one (Haskell's Either:
 * Left = generic, Right = specialized). */
export function selectApply(spec: ApplySpec): { generic: boolean; fun: JStgExpr } {
  const e = specApplyExprMaybe(spec);
  return e === undefined ? { generic: true, fun: genericApplyExpr(spec.specConv) } : { generic: false, fun: e };
}

/** Build functions to quickly lookup apply functions
 *
 *  h$apply(r << 8 | n) = function application for r regs, n args
 *  h$paps(r)           = partial application for r registers (number of args
 *                        is in the object)
 */
export function mkApplyArr(js: JSM): JStgStat {
  const casePap = (p: number): [JStgExpr, JStgStat] => [jInt(p), returnS(global(`${hdPapStr_}${p}`))];
  // Both fast/slow (regs/stack) specialized apply functions have the same
  // tags. We store the stack ones in the array because they are used as
  // continuation stack frames.
  const caseApply = (spec: ApplySpec): Array<[JStgExpr, JStgStat]> =>
    spec.specConv === ApplyConv.StackConv ? [[specTagExpr(spec), returnS(specApplyExpr(spec))]] : [];

  const papsFun = jFunctionSized(js, name(hdPapsStr), 1, ([i]) => ({
    tag: "SwitchStat",
    scrut: i!,
    cases: specPap.map(casePap),
    default: returnS(global(hdPapGenStr)),
  }));
  const applyFun = jFunctionSized(js, name(hdApplyStr), 1, ([i]) => ({
    tag: "SwitchStat",
    scrut: i!,
    cases: applySpec.flatMap(caseApply),
    default: returnS(hdApGen),
  }));
  return mconcatJStgStat([papsFun, applyFun]);
}

// ---------------------------------------------------------------------------
//                           Generic apply
// ---------------------------------------------------------------------------

/** Generic stack apply function (h$ap_gen) that can do everything, but less
 * efficiently than other more specialized functions.
 *
 * Stack layout:
 *  -3: ...
 *  -2: args
 *  -1: tag (number of arg slots << 8 | number of args)
 *
 * Regs:
 *  R1 = applied closure
 */
export function genericStackApply(js: JSM, cfg: StgToJSConfig): JStgStat {
  const info: ClosureInfo = {
    var: hdApGenStr,
    regs: ciRegs(0, [JSRep.PtrV]), // closure to apply to
    name: hdApGenStr,
    layout: ciLayoutVariable,
    type: { tag: "CIStackFrame" },
    static: noStatic,
  };

  const defaultCase = (cf: JStgExpr): JStgStat =>
    appS(throwStr, [jAdd(jString("h$ap_gen: unexpected closure type "), infoClosureType(cf))]);

  const thunkCase = (cf: JStgExpr): JStgStat =>
    mconcatJStgStat([profStat(cfg, pushRestoreCCS), returnS(cf)]);

  const blackholeCase = (): JStgStat =>
    mconcatJStgStat([push_(cfg, [r1, hdReturn]), returnS(app(hdBlockOnBlackHoleStr, [r1]))]);

  const funCase = (c: JStgExpr, arity: JStgExpr): JStgStat =>
    jVars(js, 9, ([tag, neededArgs, neededRegs, givenArgs, givenRegs, newTag, newAp, p, dat]) => {
      const buildPapPayload = loop_(js, zero_, (i) => lt_(i, givenRegs!), (i) =>
        mconcatJStgStat([
          { tag: "ApplStat", fn: sel_(dat!, "push"), args: [idx_(stack, jSub(jSub(sp, i), jInt(2)))] },
          postIncrS(i),
        ]),
      );
      const loadRegValues = loop_(js, zero_, (i) => lt_(i, neededRegs!), (i) =>
        mconcatJStgStat([
          traceRts(cfg, jAdd(jString("h$ap_gen: loading register: "), i)),
          appS(hdSetRegStr, [jAdd(i, jInt(2)), idx_(stack, jSub(jSub(sp, jInt(2)), i))]),
          postIncrS(i),
        ]),
      );
      const setRegValues = loop_(js, zero_, (i) => lt_(i, givenRegs!), (i) =>
        mconcatJStgStat([
          appS(hdSetRegStr, [jAdd(i, jInt(2)), idx_(stack, jSub(jSub(sp, jInt(2)), i))]),
          postIncrS(i),
        ]),
      );
      return mconcatJStgStat([
        assign_(tag!, idx_(stack, jSub(sp, jInt(1)))), // tag on the stack
        assign_(givenArgs!, mask8(tag!)), // indicates the number of passed args
        assign_(givenRegs!, shr_(tag!, jInt(8))), // and the number of passed values for registers
        assign_(neededArgs!, mask8(arity)),
        assign_(neededRegs!, shr_(arity, jInt(8))),
        traceRts(
          cfg,
          jAdd(jAdd(jAdd(jString("h$ap_gen: args: "), givenArgs!), jString(" regs: ")), givenRegs!),
        ),
        ifBlockS(
          strictEq_(givenArgs!, neededArgs!),
          // exactly saturated application
          [
            traceRts(cfg, jString("h$ap_gen: exact")),
            // Set registers to register values on the stack
            setRegValues,
            // drop register values from the stack
            assign_(sp, jSub(jSub(sp, givenRegs!), jInt(2))),
            // enter closure in R1
            returnS(c),
          ],
          [
            ifBlockS(
              gt_(givenArgs!, neededArgs!),
              // oversaturated application
              [
                traceRts(
                  cfg,
                  jAdd(jAdd(jAdd(jString("h$ap_gen: oversat: arity: "), neededArgs!), jString(" regs: ")), neededRegs!),
                ),
                // load needed register values
                loadRegValues,
                // compute new tag with consumed register values and args removed
                assign_(newTag!, bor_(shl_(jSub(givenRegs!, neededRegs!), jInt(8)), jSub(givenArgs!, neededArgs!))),
                // find application function for the remaining regs/args
                assign_(newAp!, { tag: "ApplExpr", fn: hdApply, args: [newTag!] }),
                traceRts(cfg, jAdd(jString("h$ap_gen: next: "), sel_(newAp!, "n"))),
                // Drop used registers from the stack.
                // Test if the application function needs a tag and push it.
                ifS(
                  strictEq_(newAp!, hdApGen),
                  mconcatJStgStat([
                    assign_(sp, jSub(sp, neededRegs!)),
                    assign_(idx_(stack, jSub(sp, jInt(1))), newTag!),
                  ]),
                  assign_(sp, jSub(jSub(sp, neededRegs!), jInt(1))),
                ),
                // Push generic application function as continuation
                assign_(idx_(stack, sp), newAp!),
                // Push "current thread CCS restore" function as continuation
                profStat(cfg, pushRestoreCCS),
                // enter closure in R1
                returnS(c),
              ],
              // undersaturated application
              [
                traceRts(cfg, jString("h$ap_gen: undersat")),
                // find PAP entry function corresponding to given_regs count
                assign_(p!, { tag: "ApplExpr", fn: hdPaps, args: [givenRegs!] }),
                // build PAP payload: R1 + tag + given register values
                assign_(newTag!, bor_(shl_(jSub(neededRegs!, givenRegs!), jInt(8)), jSub(neededArgs!, givenArgs!))),
                assign_(dat!, toJExpr([r1, newTag!])),
                buildPapPayload,
                // remove register values from the stack.
                assign_(sp, jSub(jSub(sp, givenRegs!), jInt(2))),
                // alloc PAP closure, store reference to it in R1.
                assign_(r1, initClosure(cfg, p!, dat!, jCurrentCCS)),
                // return to the continuation on the stack
                returnStack,
              ],
            ),
          ],
        ),
      ]);
    });

  return closure(js, info, () =>
    jVar(js, (cf) =>
      mconcatJStgStat([
        traceRts(cfg, jString(hdApGenStr)),
        assign_(cf, closureInfo(r1)),
        // switch on closure type
        {
          tag: "SwitchStat",
          scrut: infoClosureType(cf),
          cases: [
            [closureTypeToJExpr(ClosureType.Thunk), thunkCase(cf)],
            [closureTypeToJExpr(ClosureType.Fun), funCase(cf, infoFunArity(cf))],
            [closureTypeToJExpr(ClosureType.Pap), funCase(cf, papArity(r1))],
            [closureTypeToJExpr(ClosureType.Blackhole), blackholeCase()],
          ],
          default: defaultCase(cf),
        },
      ]),
    ),
  );
}

/** Generic fast apply function (h$ap_gen_fast) that can do everything, but
 * less efficiently than other more specialized functions.
 *
 * Signature tag in argument. Tag: (regs << 8 | arity)
 *
 * Regs:
 *  R1 = closure to apply to
 */
export function genericFastApply(js: JSM, s: StgToJSConfig): JStgStat {
  const maxLowRegN = regNumber(maxLowReg);
  // R1 isn't used for arguments
  const lowRegsDesc: number[] = [];
  for (let n = maxLowRegN; n >= 2; n--) lowRegsDesc.push(n);

  const pushAllRegs = (tag: JStgExpr): JStgStat =>
    jVar(js, (regs) => {
      // rN stored in stack[sp - N - 2] so that r2 is stored in stack[sp], etc.
      const pushReg = (r: number): [JStgExpr, JStgStat] => [
        jInt(r),
        assign_(idx_(stack, jSub(sp, jInt(r - 2))), jsReg(r)),
      ];
      return mconcatJStgStat([
        assign_(regs, shr_(tag, jInt(8))),
        assign_(sp, jAdd(sp, regs)),
        // increment the number of regs by 1, so that it matches register
        // numbers (R1 is not used for args)
        postIncrS(regs),
        // copy high registers with a loop
        {
          tag: "WhileStat",
          isDo: false,
          cond: gt_(regs, jInt(maxLowRegN)),
          body: mconcatJStgStat([
            assign_(idx_(stack, jSub(jSub(sp, regs), jInt(2))), highReg_expr(regs)),
            postDecrS(regs),
          ]),
        },
        { tag: "SwitchStat", scrut: regs, cases: lowRegsDesc.map(pushReg), default: memptyJStgStat },
      ]);
    });

  // thunk: push everything to stack frame, enter thunk first
  const pushStackApply = (_c: JStgExpr, tag: JStgExpr): JStgStat =>
    jVar(js, (ap) =>
      mconcatJStgStat([
        pushAllRegs(tag),
        assign_(ap, { tag: "ApplExpr", fn: hdApply, args: [tag] }),
        ifS(
          strictEq_(ap, hdApGen),
          mconcatJStgStat([assign_(sp, jAdd(sp, jInt(2))), assign_(idx_(stack, jSub(sp, jInt(1))), tag)]),
          assign_(sp, jAdd(sp, jInt(1))),
        ),
        assign_(idx_(stack, sp), ap),
        profStat(s, pushRestoreCCS),
      ]),
    );

  const pushArgs = (start: JStgExpr, end: JStgExpr): JStgStat =>
    loop_(js, end, (i) => ge_(i, start), (i) =>
      mconcatJStgStat([
        traceRts(s, jAdd(jString("pushing register: "), i)),
        assign_(idx_(stack, jSub(jAdd(sp, start), i)), app(hdGetRegStr, [jAdd(i, jInt(1))])),
        postDecrS(i),
      ]),
    );

  const funCase = (c: JStgExpr, tag: JStgExpr, arity: JStgExpr): JStgStat =>
    jVars(js, 8, ([ar, myAr, myRegs, regsStart, newTag, newAp, dat, p]) => {
      const getRegs = loop_(js, zero_, (i) => lt_(i, myRegs!), (i) =>
        mconcatJStgStat([
          { tag: "ApplStat", fn: sel_(dat!, "push"), args: [app(hdGetRegStr, [jAdd(i, jInt(2))])] },
          postIncrS(i),
        ]),
      );
      return mconcatJStgStat([
        assign_(ar!, mask8(arity)),
        assign_(myAr!, mask8(tag)),
        assign_(myRegs!, shr_(tag, jInt(8))),
        traceRts(s, jAdd(jAdd(jAdd(jString("h$ap_gen_fast: args: "), myAr!), jString(" regs: ")), myRegs!)),
        ifS(
          strictEq_(myAr!, ar!),
          // call the function directly
          mconcatJStgStat([traceRts(s, jString("h$ap_gen_fast: exact")), returnS(c)]),
          ifBlockS(
            gt_(myAr!, ar!),
            // push stack frame with remaining args, then call fun
            [
              traceRts(s, jAdd(jString("h$ap_gen_fast: oversat "), sp)),
              assign_(regsStart!, jAdd(shr_(arity, jInt(8)), jInt(1))),
              assign_(sp, jAdd(jSub(jAdd(sp, myRegs!), regsStart!), jInt(1))),
              traceRts(s, jAdd(jString("h$ap_gen_fast: oversat "), sp)),
              pushArgs(regsStart!, myRegs!),
              assign_(newTag!, bor_(shl_(jSub(myRegs!, shr_(arity, jInt(8))), jInt(8)), jSub(myAr!, ar!))),
              assign_(newAp!, { tag: "ApplExpr", fn: hdApply, args: [newTag!] }),
              ifS(
                strictEq_(newAp!, hdApGen),
                mconcatJStgStat([
                  assign_(sp, jAdd(sp, jInt(2))),
                  assign_(idx_(stack, jSub(sp, jInt(1))), newTag!),
                ]),
                assign_(sp, jAdd(sp, jInt(1))),
              ),
              assign_(idx_(stack, sp), newAp!),
              profStat(s, pushRestoreCCS),
              returnS(c),
            ],
            [
              traceRts(s, jAdd(jAdd(jAdd(jString("h$ap_gen_fast: undersat: "), myRegs!), jString(" ")), tag)),
              jwhenS(
                strictNeq_(tag, zero_),
                mconcatJStgStat([
                  assign_(p!, { tag: "ApplExpr", fn: hdPaps, args: [myRegs!] }),
                  assign_(
                    dat!,
                    toJExpr([
                      r1,
                      jSub(jAdd(jMul(jSub(shr_(arity, jInt(8)), myRegs!), jInt(256)), ar!), myAr!),
                    ]),
                  ),
                  getRegs,
                  assign_(r1, initClosure(s, p!, dat!, jCurrentCCS)),
                ]),
              ),
              returnStack,
            ],
          ),
        ),
      ]);
    });

  return jFunctionSized(js, name(hdApGenFastStr), 1, ([tag]) =>
    jVar(js, (c) => {
      const pushStkApp = pushStackApply(c, tag!);
      const fastFun = jVar(js, (farity) =>
        mconcatJStgStat([
          assign_(farity, infoFunArity(c)),
          traceRts(s, jAdd(jString("h$ap_gen_fast: fun "), farity)),
          funCase(c, tag!, farity),
        ]),
      );
      const fastPap = jVar(js, (parity) =>
        mconcatJStgStat([
          assign_(parity, papArity(r1)),
          traceRts(s, jAdd(jString("h$ap_gen_fast: pap "), parity)),
          funCase(c, tag!, parity),
        ]),
      );
      return mconcatJStgStat([
        traceRts(s, jAdd(jString("h$ap_gen_fast: "), tag!)),
        assign_(c, closureInfo(r1)),
        {
          tag: "SwitchStat",
          scrut: infoClosureType(c),
          cases: [
            [
              closureTypeToJExpr(ClosureType.Thunk),
              mconcatJStgStat([traceRts(s, jString("h$ap_gen_fast: thunk")), pushStkApp, returnS(c)]),
            ],
            [closureTypeToJExpr(ClosureType.Fun), fastFun],
            [closureTypeToJExpr(ClosureType.Pap), fastPap],
            [
              closureTypeToJExpr(ClosureType.Con),
              mconcatJStgStat([
                traceRts(s, jString("h$ap_gen_fast: con")),
                jwhenS(strictNeq_(tag!, zero_), appS(throwStr, [jString("h$ap_gen_fast: invalid apply")])),
                returnS(c),
              ]),
            ],
            [
              closureTypeToJExpr(ClosureType.Blackhole),
              mconcatJStgStat([
                traceRts(s, jString("h$ap_gen_fast: blackhole")),
                pushStkApp,
                push_(s, [r1, hdReturn]),
                returnS(app(hdBlockOnBlackHoleStr, [r1])),
              ]),
            ],
          ],
          default: appS(throwStr, [
            jAdd(jString("h$ap_gen_fast: unexpected closure type: "), infoClosureType(c)),
          ]),
        },
      ]);
    }),
  );
}

// ---------------------------------------------------------------------------
//                        Specialized apply
// ---------------------------------------------------------------------------

/** Make specialized apply function for the given ApplySpec */
export function specApply(js: JSM, cfg: StgToJSConfig, spec: ApplySpec): JStgStat {
  const funName = specApplyName(spec);
  return spec.specConv === ApplyConv.RegsConv
    ? fastApply(js, cfg, funName, spec.specArgs, spec.specVars)
    : stackApply(js, cfg, funName, spec.specArgs, spec.specVars);
}

/** The Ident behind a variable expression produced by jVar/jVars. Haskell
 * pattern-matches `ValExpr (JVar pap)` on those same fresh variables; TS has
 * no pattern match on the EDSL, so the ident is projected out instead. */
function varIdent(e: JStgExpr): Ident {
  if (e.tag === "ValExpr" && e.value.tag === "JVar") return e.value.ident;
  throw new Error("apply: expected a variable expression");
}

/** Make specialized apply function with Stack calling convention */
export function stackApply(js: JSM, s: StgToJSConfig, funName: string, nargs: number, nvars: number): JStgStat {
  const info: ClosureInfo = {
    var: funName,
    regs: ciRegs(0, [JSRep.PtrV]),
    name: funName,
    layout: ciLayoutUnknown(nvars),
    type: { tag: "CIStackFrame" },
    static: noStatic,
  };
  const info0: ClosureInfo = {
    var: funName,
    regs: ciRegs(0, [JSRep.PtrV]),
    name: funName,
    layout: ciLayoutFixed(0, []),
    type: { tag: "CIStackFrame" },
    static: noStatic,
  };

  const stackArgs: JStgExpr[] = Array.from({ length: nvars }, (_, k) => idx_(stack, jSub(sp, jInt(k + 1))));
  const funExact = (c: JStgExpr): JStgStat =>
    mconcatJStgStat([popSkip(1, take(jsRegsFromR2(), nvars).reverse()), returnS(c)]);

  // oversat: call the function but keep enough on the stack for the next
  const oversatCase = (c: JStgExpr, arity: JStgExpr, arity0: JStgExpr): JStgStat =>
    jVars(js, 2, ([rs, newAp]) => {
      const switchAlts: Array<[JStgExpr, JStgStat]> = [];
      for (let x = nvars; x >= 1; x--)
        switchAlts.push([jInt(x), assign_(jsReg(x + 1), idx_(stack, jSub(sp, jInt(x))))]);
      const loadRegs: JStgStat = { tag: "SwitchStat", scrut: rs!, cases: switchAlts, default: memptyJStgStat };
      return mconcatJStgStat([
        assign_(rs!, shr_(arity, jInt(8))),
        loadRegs,
        assign_(sp, jSub(sp, rs!)),
        assign_(newAp!, {
          tag: "ApplExpr",
          fn: hdApply,
          args: [bor_(jSub(jInt(nargs), arity0), shl_(jSub(jInt(nvars), rs!), jInt(8)))],
        }),
        assign_(idx_(stack, sp), newAp!),
        profStat(s, pushRestoreCCS),
        traceRts(s, jAdd(jString(`${funName}: new stack frame: `), sel_(newAp!, "n"))),
        returnS(c),
      ]);
    });

  const papCase = (c: JStgExpr): JStgStat =>
    jVars(js, 3, ([expr, arity0, arity]) => {
      const papI = varIdent(expr!);
      return mconcatJStgStat([
        assign_(arity0!, papArity(r1)),
        assign_(arity!, mask8(arity0!)),
        traceRts(s, jAdd(jString(`${funName}: found pap, arity: `), arity!)),
        ifS(
          strictEq_(jInt(nargs), arity!),
          mconcatJStgStat([traceRts(s, jString(`${funName}: exact`)), funExact(c)]),
          ifS(
            gt_(jInt(nargs), arity!),
            mconcatJStgStat([traceRts(s, jString(`${funName}: oversat`)), oversatCase(c, arity0!, arity!)]),
            mconcatJStgStat([
              traceRts(s, jString(`${funName}: undersat`)),
              mkPap(s, papI, r1, jInt(nargs), stackArgs),
              assign_(sp, jSub(sp, jInt(nvars + 1))),
              assign_(r1, toJExpr(papI)),
              returnStack,
            ]),
          ),
        ),
      ]);
    });

  const funCase = (c: JStgExpr): JStgStat =>
    jVars(js, 3, ([expr, ar0, ar]) => {
      const papI = varIdent(expr!);
      return mconcatJStgStat([
        assign_(ar0!, infoFunArity(c)),
        assign_(ar!, mask8(ar0!)),
        ifS(
          strictEq_(jInt(nargs), ar!),
          mconcatJStgStat([traceRts(s, jString(`${funName}: exact`)), funExact(c)]),
          ifS(
            gt_(jInt(nargs), ar!),
            mconcatJStgStat([traceRts(s, jString(`${funName}: oversat`)), oversatCase(c, ar0!, ar!)]),
            mconcatJStgStat([
              traceRts(s, jString(`${funName}: undersat`)),
              mkPap(s, papI, register(R1), jInt(nargs), stackArgs),
              assign_(sp, jSub(sp, jInt(nvars + 1))),
              assign_(r1, toJExpr(papI)),
              returnStack,
            ]),
          ),
        ),
      ]);
    });

  // special case for h$ap_0_0
  if (nargs === 0 && nvars === 0)
    return closure(js, info0, () => mconcatJStgStat([adjSpN_(1), enter(js, s, r1)]));

  return closure(js, info, () =>
    jVar(js, (c) =>
      mconcatJStgStat([
        assign_(c, closureInfo(r1)),
        traceRts(
          s,
          jAdd(
            jAdd(jAdd(jAdd(jAdd(jString(funName), jString(" ")), sel_(c, "n")), jString(" sp: ")), sp),
            jAdd(jString(" a: "), sel_(c, "a")),
          ),
        ),
        {
          tag: "SwitchStat",
          scrut: infoClosureType(c),
          cases: [
            [
              closureTypeToJExpr(ClosureType.Thunk),
              mconcatJStgStat([
                traceRts(s, jString(`${funName}: thunk`)),
                profStat(s, pushRestoreCCS),
                returnS(c),
              ]),
            ],
            [
              closureTypeToJExpr(ClosureType.Fun),
              mconcatJStgStat([traceRts(s, jString(`${funName}: fun`)), funCase(c)]),
            ],
            [
              closureTypeToJExpr(ClosureType.Pap),
              mconcatJStgStat([traceRts(s, jString(`${funName}: pap`)), papCase(c)]),
            ],
            [
              closureTypeToJExpr(ClosureType.Blackhole),
              mconcatJStgStat([push_(s, [r1, hdReturn]), returnS(app(hdBlockOnBlackHoleStr, [r1]))]),
            ],
          ],
          default: appS(throwStr, [
            jAdd(jString(`panic: ${funName}, unexpected closure type: `), infoClosureType(c)),
          ]),
        },
      ]),
    ),
  );
}

/** Make specialized apply function with Regs calling convention.
 *
 * h$ap_n_r_fast is entered if a function of unknown arity is called, n
 * arguments are already in r registers. */
export function fastApply(js: JSM, s: StgToJSConfig, funName: string, nargs: number, nvars: number): JStgStat {
  const func = name(funName);
  const regArgs = take(jsRegsFromR2(), nvars);
  const mkAp = (n: number, r: number): JStgExpr[] => [
    specApplyExpr({ specConv: ApplyConv.StackConv, specArgs: n, specVars: r }),
  ];

  const oversatCase = (c: JStgExpr, arity: JStgExpr): JStgStat =>
    jVars(js, 2, ([rs, rsRemain]) => {
      const switchAlts: Array<[JStgExpr, JStgStat]> = [];
      for (let x = 0; x < nvars; x++)
        switchAlts.push([jInt(x), assign_(idx_(stack, jAdd(sp, jInt(nvars - x))), jsReg(x + 2))]);
      const saveRegs: JStgStat = { tag: "SwitchStat", scrut: rs!, cases: switchAlts, default: memptyJStgStat };
      return mconcatJStgStat([
        assign_(rs!, shr_(arity, jInt(8))),
        assign_(rsRemain!, jSub(jInt(nvars), rs!)),
        traceRts(
          s,
          jAdd(jAdd(jAdd(jString(`${funName} regs oversat `), rs!), jString(" remain: ")), rsRemain!),
        ),
        saveRegs,
        assign_(sp, jAdd(jAdd(sp, rsRemain!), jInt(1))),
        assign_(idx_(stack, sp), {
          tag: "ApplExpr",
          fn: hdApply,
          args: [bor_(shl_(rsRemain!, jInt(8)), jSub(jInt(nargs), mask8(arity)))],
        }),
        profStat(s, pushRestoreCCS),
        returnS(c),
      ]);
    });

  const funCase = (c: JStgExpr, arity: JStgExpr): JStgStat =>
    jVars(js, 2, ([arg, ar]) => {
      const papI = varIdent(arg!);
      return mconcatJStgStat([
        assign_(ar!, mask8(arity)),
        ifS(
          strictEq_(jInt(nargs), ar!),
          mconcatJStgStat([traceRts(s, jString(`${funName}: exact`)), returnS(c)]),
          ifS(
            gt_(jInt(nargs), ar!),
            mconcatJStgStat([traceRts(s, jString(`${funName}: oversat`)), oversatCase(c, arity)]),
            mconcatJStgStat([
              traceRts(s, jString(`${funName}: undersat`)),
              mkPap(s, papI, r1, jInt(nargs), regArgs),
              assign_(r1, toJExpr(papI)),
              returnStack,
            ]),
          ),
        ),
      ]);
    });

  // special case for h$ap_0_0_fast
  if (nargs === 0 && nvars === 0) return jFunction_(func, enter(js, s, r1));

  return jFunction_(
    func,
    jVars(js, 3, ([c, farity, arity]) =>
      mconcatJStgStat([
        assign_(c!, closureInfo(r1)),
        traceRts(s, jAdd(jString(`${funName}: sp `), sp)),
        {
          tag: "SwitchStat",
          scrut: infoClosureType(c!),
          cases: [
            [
              closureTypeToJExpr(ClosureType.Fun),
              mconcatJStgStat([
                traceRts(
                  s,
                  jAdd(
                    jAdd(jAdd(jString(`${funName}: `), clName(c!)), jString(" (arity: ")),
                    jAdd(sel_(c!, "a"), jString(")")),
                  ),
                ),
                assign_(farity!, infoFunArity(c!)),
                funCase(c!, farity!),
              ]),
            ],
            [
              closureTypeToJExpr(ClosureType.Pap),
              mconcatJStgStat([
                traceRts(s, jString(`${funName}: pap`)),
                assign_(arity!, papArity(r1)),
                funCase(c!, arity!),
              ]),
            ],
            [
              closureTypeToJExpr(ClosureType.Thunk),
              mconcatJStgStat([
                traceRts(s, jString(`${funName}: thunk`)),
                push_(s, [...[...regArgs].reverse(), ...mkAp(nargs, nvars)]),
                profStat(s, pushRestoreCCS),
                returnS(c!),
              ]),
            ],
            [
              closureTypeToJExpr(ClosureType.Blackhole),
              mconcatJStgStat([
                traceRts(s, jString(`${funName}: blackhole`)),
                push_(s, [...[...regArgs].reverse(), ...mkAp(nargs, nvars)]),
                push_(s, [r1, global("h$return")]),
                returnS(app("h$blockOnBlackhole", [r1])),
              ]),
            ],
          ],
          default: appS(throwStr, [
            jAdd(jString(`${funName}: unexpected closure type: `), infoClosureType(c!)),
          ]),
        },
      ]),
    ),
  );
}

// ---------------------------------------------------------------------------
//                        h$e, updates, selectors
// ---------------------------------------------------------------------------

export function zeroApply(js: JSM, s: StgToJSConfig): JStgStat {
  return jFunctionSized(js, name(hdEntryStr), 1, ([c]) =>
    mconcatJStgStat([assign_(r1, c!), enter(js, s, c!)]),
  );
}

/** Carefully enter a closure that might be a thunk or a function.
 *
 * `ex` may be a local var, but must've been copied to R1 before calling this. */
export function enter(js: JSM, s: StgToJSConfig, ex: JStgExpr): JStgStat {
  return jVar(js, (c) =>
    mconcatJStgStat([
      jwhenS(strictNeq_(app(typeofStr, [ex]), jTyObject), returnStack),
      assign_(c, closureInfo(ex)),
      jwhenS(strictEq_(c, hdUnboxEntry), mconcatJStgStat([assign_(r1, closureField1(ex)), returnStack])),
      {
        tag: "SwitchStat",
        scrut: infoClosureType(c),
        cases: [
          [closureTypeToJExpr(ClosureType.Con), memptyJStgStat],
          [closureTypeToJExpr(ClosureType.Fun), memptyJStgStat],
          [closureTypeToJExpr(ClosureType.Pap), returnStack],
          [
            closureTypeToJExpr(ClosureType.Blackhole),
            mconcatJStgStat([
              push_(s, [hdAp00, ex, hdReturn]),
              returnS(app(hdBlockOnBlackHoleStr, [ex])),
            ]),
          ],
        ],
        default: returnS(c),
      },
    ]),
  );
}

export function updates(js: JSM, s: StgToJSConfig): JStgStat {
  const unboxClosure = (f1: JStgExpr): Closure => ({
    clInfo: hdUnboxEntry,
    clField1: f1,
    clField2: null_,
    clMeta: zero_,
  });

  const updLoop_ = (ss_: JStgExpr, si_: JStgExpr, sir_: JStgExpr): JStgStat =>
    loop_(js, zero_, (i) => lt_(i, sel_(ss_, "length")), (i) =>
      mconcatJStgStat([
        assign_(si_, idx_(ss_, i)),
        assign_(sir_, { tag: "ApplExpr", fn: closureField2(si_), args: [r1] }),
        ifS(
          strictEq_(app(typeofStr, [sir_]), jTyObject),
          copyClosure(CopyCC.DontCopyCC, si_, sir_),
          assignClosure(si_, unboxClosure(sir_)),
        ),
        postIncrS(i),
      ]),
    );

  const updateFrame = closure(
    js,
    {
      var: hdUpdFrameStr,
      regs: ciRegs(0, [JSRep.PtrV]),
      name: hdUpdFrameStr,
      layout: ciLayoutFixed(1, [JSRep.PtrV]),
      type: { tag: "CIStackFrame" },
      static: noStatic,
    },
    () =>
      jVars(js, 5, ([updatee, waiters, ss, si, sir]) => {
        const updLoop = updLoop_(ss!, si!, sir!);
        const wakeThreadLoop = loop_(js, zero_, (i) => lt_(i, sel_(waiters!, "length")), (i) =>
          mconcatJStgStat([appS(hdWakeupThread, [idx_(waiters!, i)]), postIncrS(i)]),
        );
        return mconcatJStgStat([
          assign_(updatee!, idx_(stack, jSub(sp, jInt(1)))),
          traceRts(s, jAdd(jString("h$upd_frame updatee alloc: "), sel_(updatee!, "alloc"))),
          // wake up threads blocked on blackhole
          assign_(waiters!, closureField2(updatee!)),
          jwhenS(strictNeq_(waiters!, null_), wakeThreadLoop),
          // update selectors
          jwhenS(
            land_(strictEq_(app(typeofStr, [closureMeta(updatee!)]), jTyObject), sel_(closureMeta(updatee!), "sel")),
            mconcatJStgStat([assign_(ss!, sel_(closureMeta(updatee!), "sel")), updLoop]),
          ),
          // overwrite the object
          ifS(
            strictEq_(app(typeofStr, [r1]), jTyObject),
            mconcatJStgStat([
              traceRts(s, jAdd(jString("$upd_frame: boxed: "), sel_(closureInfo(r1), "n"))),
              copyClosure(CopyCC.DontCopyCC, updatee!, r1),
            ]),
            // the heap object is represented by another type of value (e.g. a
            // JS number or string) so the unboxing closure will simply return it
            assignClosure(updatee!, unboxClosure(r1)),
          ),
          profStat(s, assign_(closureCC(updatee!), jCurrentCCS)),
          adjSpN_(2),
          traceRts(
            s,
            jAdd(jAdd(jAdd(jString("h$upd_frame: updating: "), updatee!), jString(" -> ")), r1),
          ),
          returnStack,
        ]);
      }),
  );

  const updateFrameLne = closure(
    js,
    {
      var: "h$upd_frame_lne",
      regs: ciRegs(0, [JSRep.PtrV]),
      name: "h$upd_frame_lne",
      layout: ciLayoutFixed(1, [JSRep.PtrV]),
      type: { tag: "CIStackFrame" },
      static: noStatic,
    },
    () =>
      jVar(js, (updateePos) =>
        mconcatJStgStat([
          assign_(updateePos, idx_(stack, jSub(sp, jInt(1)))),
          assign_(idx_(stack, updateePos), r1),
          adjSpN_(2),
          traceRts(
            s,
            jAdd(jAdd(jAdd(jString("h$upd_frame_lne: updating: "), updateePos), jString(" -> ")), r1),
          ),
          returnStack,
        ]),
      ),
  );

  return { tag: "BlockStat", stats: [updateFrame, updateFrameLne] };
}

export function selectors(js: JSM, s: StgToJSConfig): JStgStat {
  const mkSel = (name_: string, sel: (e: JStgExpr) => JStgExpr): JStgStat => {
    const n = (ext: string): string => `${hdCSelStr}${name_}${ext}`;
    const createName = n("");
    const resName = n("_res");
    const entryName = n("_e");
    const frameName = n("_frame_e");
    return mconcatJStgStat([
      jFunctionSized(js, name(createName), 1, ([r]) =>
        mconcatJStgStat([
          traceRts(s, jAdd(jString(`selector create: ${name_} for `), sel_(r!, "alloc"))),
          ifS(
            lor_(isThunk(r!), isBlackhole(r!)),
            returnS(app("h$mkSelThunk", [r!, global(entryName), global(resName)])),
            returnS(sel(r!)),
          ),
        ]),
      ),
      jFunctionSized(js, name(resName), 1, ([r]) =>
        mconcatJStgStat([
          traceRts(s, jAdd(jString(`selector result: ${name_} for `), sel_(r!, "alloc"))),
          returnS(sel(r!)),
        ]),
      ),
      closure(
        js,
        {
          var: entryName,
          regs: ciRegs(0, [JSRep.PtrV]),
          name: `select ${name_}`,
          layout: ciLayoutFixed(1, [JSRep.PtrV]),
          type: { tag: "CIThunk" },
          static: noStatic,
        },
        () =>
          jVar(js, (tgt) =>
            mconcatJStgStat([
              assign_(tgt, closureField1(r1)),
              traceRts(s, jAdd(jString(`selector entry: ${name_} for `), sel_(tgt, "alloc"))),
              ifS(
                lor_(isThunk(tgt), isBlackhole(tgt)),
                mconcatJStgStat([
                  preIncrS(sp),
                  assign_(idx_(stack, sp), global(frameName)),
                  returnS(app(hdEntryStr, [tgt])),
                ]),
                returnS(app(hdEntryStr, [sel(tgt)])),
              ),
            ]),
          ),
      ),
      closure(
        js,
        {
          var: frameName,
          regs: ciRegs(0, [JSRep.PtrV]),
          name: `select ${name_} frame`,
          layout: ciLayoutFixed(0, []),
          type: { tag: "CIStackFrame" },
          static: noStatic,
        },
        () =>
          mconcatJStgStat([
            traceRts(s, jString(`selector frame: ${name_}`)),
            postDecrS(sp),
            returnS(app(hdEntryStr, [sel(r1)])),
          ]),
      ),
    ]);
  };

  const mkSelN = (x: number): JStgStat =>
    mkSel(String(x), (e) => sel_(closureField2(e), `d${x - 1}`));

  return mconcatJStgStat([
    mkSel("1", closureField1),
    mkSel("2a", closureField2),
    mkSel("2b", (e) => closureField1(closureField2(e))),
    ...Array.from({ length: 14 }, (_, k) => mkSelN(k + 3)),
  ]);
}

// ---------------------------------------------------------------------------
//                                 PAPs
// ---------------------------------------------------------------------------

/** arity is the remaining arity after our supplied arguments are applied */
export function mkPap(
  s: StgToJSConfig,
  tgt: Ident,
  fun: JStgExpr,
  n: JStgExpr,
  values: JStgExpr[],
): JStgStat {
  const papAr = jSub(jSub(funOrPapArity(fun, undefined), jInt(values.length * 256)), n);
  const values_ = values.length === 0 ? [null_] : values;
  const entry = values.length > numSpecPap ? name(hdPapGenStr) : specPapIdents[values.length]!;
  return mconcatJStgStat([
    traceRts(s, jString(`making pap with: ${values.length} items`)),
    allocDynamic(s, true, tgt, toJExpr(entry), [fun, papAr, ...values_], s.prof ? jCurrentCCS : undefined),
  ]);
}

/** Number of specialized PAPs (pre-generated for a given number of args) */
export const numSpecPap = 6;

/** specialized (faster) pap generated for [0..numSpecPap]; others use
 * h$pap_gen */
export const specPap: number[] = Array.from({ length: numSpecPap + 1 }, (_, k) => k);

/** Cache of specialized PAP idents */
export const specPapIdents: Ident[] = specPap.map((r) => name(`${hdPapStr_}${r}`));

export function pap(js: JSM, s: StgToJSConfig, r: number): JStgStat {
  const funcName = `${hdPapStr_}${r}`;
  const maxLowRegN = regNumber(maxLowReg);
  // R1 isn't used for arguments
  const lowRegsDesc: number[] = [];
  for (let m = maxLowRegN; m >= 2; m--) lowRegsDesc.push(m);

  const moveBy = (extra: JStgExpr): JStgStat =>
    mconcatJStgStat([
      // increment the number of args by 1, so that it matches register
      // numbers (R1 is not used for args)
      postIncrS(extra),
      // copy high registers with a loop
      {
        tag: "WhileStat",
        isDo: false,
        cond: gt_(extra, jInt(maxLowRegN)),
        body: mconcatJStgStat([
          assign_(highReg_expr(jAdd(extra, jInt(r))), highReg_expr(extra)),
          postDecrS(extra),
        ]),
      },
      // then copy low registers with a case
      {
        tag: "SwitchStat",
        scrut: extra,
        cases: lowRegsDesc.map((m): [JStgExpr, JStgStat] => [jInt(m), assign_(jsReg(m + r), jsReg(m))]),
        default: memptyJStgStat,
      },
    ]);

  const dField = (d: JStgExpr, n: number): JStgExpr => sel_(d, `d${n - 1}`);
  const loadOwnArgs = (d: JStgExpr): JStgStat =>
    mconcatJStgStat(Array.from({ length: r }, (_, k) => assign_(jsReg(k + 2), dField(d, k + 3))));

  return closure(
    js,
    {
      var: funcName,
      regs: ciRegsUnknown,
      name: funcName,
      layout: ciLayoutUnknown(r + 2),
      type: { tag: "CIPap" },
      static: noStatic,
    },
    () =>
      jVars(js, 4, ([c, d, f, extra]) =>
        mconcatJStgStat([
          assign_(c!, closureField1(r1)),
          assign_(d!, closureField2(r1)),
          assign_(f!, closureInfo(c!)),
          assertRts(s, lor_(isFun_(f!), isPap_(f!)), jString(`${funcName}: expected function or pap`)),
          profStat(s, enterCostCentreFunCurrentCCS),
          assign_(extra!, jSub(shr_(funOrPapArity(c!, f!), jInt(8)), jInt(r))),
          traceRts(s, jAdd(jString(`${funcName}: pap extra args moving: `), extra!)),
          // in pap_0 we don't shift any register
          r === 0 ? memptyJStgStat : moveBy(extra!),
          loadOwnArgs(d!),
          assign_(r1, c!),
          returnS(f!),
        ]),
      ),
  );
}

/** Construct a generic PAP */
export function papGen(js: JSM, cfg: StgToJSConfig): JStgStat {
  const funcName = hdPapGenStr;
  const maxLowRegN = regNumber(maxLowReg);
  const lowRegsDesc: number[] = [];
  for (let m = maxLowRegN; m >= 2; m--) lowRegsDesc.push(m);

  const loadOwnArgs = (d: JStgExpr, r: JStgExpr): JStgStat =>
    mconcatJStgStat([
      // increment the number of args by 1, so that it matches register numbers
      // (R1 is not used for args) and PAP fields (starting from d2)
      postIncrS(r),
      // copy high registers with a loop
      {
        tag: "WhileStat",
        isDo: false,
        cond: gt_(r, jInt(maxLowRegN)),
        body: mconcatJStgStat([assign_(highReg_expr(r), idx_(d, jAdd(jString("d"), r))), postDecrS(r)]),
      },
      // then copy low registers with a case.
      {
        tag: "SwitchStat",
        scrut: r,
        cases: lowRegsDesc.map((n): [JStgExpr, JStgStat] => [jInt(n), assign_(jsReg(n), sel_(d, `d${n}`))]),
        default: memptyJStgStat,
      },
    ]);

  return closure(
    js,
    {
      var: funcName,
      regs: ciRegsUnknown,
      name: funcName,
      layout: ciLayoutVariable,
      type: { tag: "CIPap" },
      static: noStatic,
    },
    () =>
      jVars(js, 6, ([c, f, d, pr, or_, r]) =>
        mconcatJStgStat([
          assign_(c!, closureField1(r1)),
          assign_(d!, closureField2(r1)),
          assign_(f!, closureInfo(c!)),
          assign_(pr!, shr_(funOrPapArity(c!, f!), jInt(8))),
          assign_(or_!, shr_(papArity(r1), jInt(8))),
          assign_(r!, jSub(pr!, or_!)),
          assertRts(cfg, lor_(isFun_(f!), isPap_(f!)), jString("h$pap_gen: expected function or pap")),
          profStat(cfg, enterCostCentreFunCurrentCCS),
          traceRts(cfg, jAdd(jString("h$pap_gen: generic pap extra args moving: "), or_!)),
          // shift newly applied arguments into appropriate registers
          appS(hdMoveRegs2, [or_!, r!]),
          // load stored arguments into lowest argument registers (i.e. starting from R2)
          loadOwnArgs(d!, r!),
          assign_(r1, c!),
          returnS(f!),
        ]),
      ),
  );
}

// ---------------------------------------------------------------------------
//                          general utilities
// ---------------------------------------------------------------------------

/** move the first n registers, starting at R2, m places up (do not use with
 * negative m) */
export function moveRegs2(js: JSM): JStgStat {
  const moveRegFast = (n: number, m: number): JStgStat => assign_(jsReg(n + m), jsReg(n));
  const switchCase = (n: number, m: number): [JStgExpr, JStgStat] => {
    const moves: JStgStat[] = [];
    for (let k = n + 1; k >= 2; k--) moves.push(moveRegFast(k, m));
    return [jInt((n << 8) | m), mconcatJStgStat([...moves, { tag: "BreakStat" }])];
  };
  // fast cases
  const switchCases: Array<[JStgExpr, JStgStat]> = [];
  for (let n = 1; n <= 5; n++) for (let m = 1; m <= 4; m++) switchCases.push(switchCase(n, m));

  return jFunctionSized(js, name(hdMoveRegs2), 2, ([n, m]) => ({
    tag: "SwitchStat",
    scrut: bor_(shl_(n!, jInt(8)), m!),
    cases: switchCases,
    // fallback
    default: loop_(js, n!, (i) => gt_(i, zero_), (i) =>
      mconcatJStgStat([
        appS(hdSetRegStr, [jAdd(jAdd(i, jInt(1)), m!), app(hdGetRegStr, [jAdd(i, jInt(1))])]),
        postDecrS(i),
      ]),
    ),
  }));
}

/** Initalize a variable sized object from an array of values */
export function initClosure(cfg: StgToJSConfig, info: JStgExpr, values: JStgExpr, ccs: JStgExpr): JStgExpr {
  return app(hdInitClosure, [
    newClosure({
      clInfo: info,
      clField1: null_,
      clField2: null_,
      clMeta: zero_,
      clCC: cfg.prof ? ccs : undefined,
    }),
    values,
  ]);
}

function take<T>(gen: Generator<T>, n: number): T[] {
  const out: T[] = [];
  for (const value of gen) {
    if (out.length >= n) break;
    out.push(value);
  }
  return out;
}
