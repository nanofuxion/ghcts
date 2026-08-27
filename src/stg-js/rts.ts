/** Ported from GHC/StgToJS/Rts/Rts.hs - the generated half of the JS RTS.
 *
 * GHC's `rts.js` is exactly `jsOptimize (jStgStatToJS <$> rts cfg)` and
 * nothing else: the static `rts/js/*.js` files are ordinary package JS
 * sources, which the linker concatenates into `lib.js` instead. That split
 * makes this module a self-contained, diffable target - the oracle's rts.js
 * is 611 symbols, and scripts/oracle-diff.mjs scores against it.
 */
import { global, memptyJStgStat, mconcatJStgStat, type JStgExpr, type JStgStat } from "../js/jstg-syntax.js";
import { name, type Ident } from "../js/ident.js";
import { initJSM, type JSM } from "../js/jstg-monad.js";
import { jsOptimize } from "../js/optimizer.js";
import { renderStat } from "../js/ppr.js";
import { jStgStatToJS } from "../js/transform.js";
import { assign_, decl, idx_, jAdd, jBlock, jFunctionSized, jInt, jString, jSub, jVar, jwhenS, returnS, strictEq_, undefined_, zero_ } from "../js/make.js";
import {
  hdCAFsResetStr,
  hdCAFsStr,
  hdClosureTypeNameStr,
  hdCurrentThreadStr,
  hdGetRegStr,
  hdInitStaticStr,
  hdRegsStr,
  hdSetRegStr,
  hdStackPtrStr,
  hdStackStr,
  hdStaticThunksArrStr,
  hdStaticThunksStr,
  hdC0Str,
  hdCStr,
  hdResetRegisters,
  hdResetResultVars,
} from "./symbols.js";
import { jsRegToInt, lowRegs, regsFromR1, register, retRegs, sp, stack } from "./regs.js";
import { clsName, dataFieldName, dataName, jsClosureCount, mkClosure, newClosure } from "./closure.js";
import { closureCC_ } from "./heap.js";
import { pushN, pushNN } from "./stack.js";
import { rtsApply } from "./apply.js";
import { ClosureType, closureTypeName as closureTypeNameOf, closureTypeToJExpr, ctNum, defaultStgToJSConfig, JSRep, type StgToJSConfig } from "./types.js";

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
  return jFunctionSized(js, name(hdClosureTypeNameStr), 1, ([c]) =>
    mconcatJStgStat([
      ...allClosureTypes.map((ct) => jwhenS(strictEq_(c!, closureTypeToJExpr(ct)), returnS(jString(closureTypeNameOf(ct))))),
      returnS(jString("InvalidClosureType")),
    ]),
  );
}

/** The `h$ct_*` closure tags and `h$vt_*` representation tags that generated
 * code compares against. `ctNum` - not the derived Enum - supplies the values
 * here, which is why `h$ct_stackframe` is -1. */
export const closureTypeConstants: JStgStat = mconcatJStgStat([
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

/** rts - the whole generated RTS.
 *
 * Still incomplete: the apply machinery (`h$ap_*`, `h$pap_*`, `h$apply`) lands
 * with apply.ts. Run `node scripts/oracle-diff.mjs` for the exact per-family
 * score against GHC's own rts.js. */
export function rts(js: JSM, cfg: StgToJSConfig = defaultStgToJSConfig): JStgStat {
  return js.withTag("h$RTS", (env) =>
    mconcatJStgStat([
      rtsDecls(env),
      garbageCollector(env),
      closureTypeConstants,
      closureConstructors(env, cfg),
      stackManip(env),
      rtsApply(env, cfg),
      closureTypes(env),
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
