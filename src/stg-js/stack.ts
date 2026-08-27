/** Ported from GHC/StgToJS/Stack.hs.
 *
 * Utilities and wrappers for stack manipulation in JS land. Functions suffixed
 * with a tick in Haskell do the actual work; `'` is not a TS identifier
 * character, so they are spelled with a trailing underscore here (`adjSp_`
 * etc). Likewise the "I" variants that work on Ident rather than JStgExpr keep
 * their Haskell names (`loadSkipI`, `popSkipI`).
 *
 * The stack lives in the JS array `h$stack`, the stack pointer in `h$sp`, so
 * the top of stack is `h$stack[h$sp]`; `h$stack[h$sp + i]` for i > 0 moves
 * deeper into older entries and `h$sp - i` moves towards the top.
 *
 * The layout algorithm is peculiar on purpose: it remembers recently popped
 * values *above* the stack pointer so a subsequent push can skip the slots it
 * knows already hold the right value. That is why push may remove slots and
 * pop may add them.
 *
 * Haskell threads the stack knowledge through the `G` (GenState) monad. That
 * state lives in GHC.StgToJS.Monad, which is not ported yet, so the two fields
 * Stack.hs actually touches are modelled by the narrow `StackState` below and
 * passed explicitly; `getSettings` likewise becomes an explicit
 * StgToJSConfig parameter.
 */
import type { Ident } from "../js/ident.js";
import { name } from "../js/ident.js";
import type { JStgExpr, JStgStat } from "../js/jstg-syntax.js";
import { Var } from "../js/jstg-syntax.js";
import { memptyJStgStat, mconcatJStgStat } from "../js/jstg-syntax.js";
import { assign_, declAssign_, idx_, jAdd, jInt, jSub, null_ } from "../js/make.js";
import { closureField1_, closureField2_, closureInfo_ } from "./heap.js";
import { R1, register, sp, stack } from "./regs.js";
import { hdBh, hdBlackHole, hdCurrentThread } from "./symbols.js";
import type { StgToJSConfig } from "./types.js";
import type { StackSlot } from "./monad.js";
import { slotUnknown } from "./monad.js";
import { sel_ } from "../js/make.js";

/** GHC.StgToJS.Symbols computes this one rather than exporting a literal, so
 * it is not among symbols.ts's generated names. */
const hdUpdFrame: JStgExpr = Var(name("h$upd_frame"));

/** GHC.StgToJS.Types owns `StackSlot`; in ghcts it lives in monad.ts with the
 * rest of GenState's vocabulary. Stack.hs only ever moves slots around
 * opaquely, so nothing here inspects the payload. */
export type { StackSlot } from "./monad.js";
export { slotUnknown } from "./monad.js";

/** The two GenGroupState fields Stack.hs reads and writes (GHC.StgToJS.Monad
 * owns the full state). Mutated in place, since `G` is a state monad. */
export interface StackState {
  stackDepth: number;
  slots: StackSlot[];
}

export const emptyStackState = (): StackState => ({ stackDepth: 0, slots: [] });

/** Run the action, 'm', with no stack info */
export function resetSlots<A>(g: StackState, m: () => A): A {
  const s = getSlots(g);
  const d = getStackDepth(g);
  setSlots(g, []);
  const a = m();
  setSlots(g, s);
  setStackDepth(g, d);
  return a;
}

/** run the action, 'm', with current stack info, but don't let modifications
 * propagate */
export function isolateSlots<A>(g: StackState, m: () => A): A {
  const s = getSlots(g);
  const d = getStackDepth(g);
  const a = m();
  setSlots(g, s);
  setStackDepth(g, d);
  return a;
}

/** Set stack depth */
export function setStackDepth(g: StackState, d: number): void {
  g.stackDepth = d;
}

/** Get stack depth */
export const getStackDepth = (g: StackState): number => g.stackDepth;

/** Modify stack depth */
export function modifyStackDepth(g: StackState, f: (d: number) => number): void {
  g.stackDepth = f(g.stackDepth);
}

/** overwrite our stack knowledge */
export function setSlots(g: StackState, xs: StackSlot[]): void {
  g.slots = xs;
}

/** retrieve our current stack knowledge */
export const getSlots = (g: StackState): StackSlot[] => g.slots;

/** Modify stack slots */
export function modifySlots(g: StackState, f: (xs: StackSlot[]) => StackSlot[]): void {
  g.slots = f(g.slots);
}

/** add `n` unknown slots to our stack knowledge */
export function addUnknownSlots(g: StackState, n: number): void {
  addSlots(g, Array.from({ length: n }, () => slotUnknown));
}

/** add knowledge about the stack slots */
export function addSlots(g: StackState, xs: StackSlot[]): void {
  const s = getSlots(g);
  setSlots(g, [...xs, ...s]);
}

/** drop 'n' slots from our stack knowledge */
export function dropSlots(g: StackState, n: number): void {
  modifySlots(g, (xs) => xs.slice(n));
}

export function push(g: StackState, cs: StgToJSConfig, xs: JStgExpr[]): JStgStat {
  dropSlots(g, xs.length);
  modifyStackDepth(g, (d) => d + xs.length);
  return push_(cs, xs);
}

export function push_(cs: StgToJSConfig, xs: JStgExpr[]): JStgStat {
  if (xs.length === 0) return memptyJStgStat;
  const l = xs.length;
  const offset = (i: number): JStgExpr => (i === l ? sp : jSub(sp, jInt(l - i)));
  if (cs.inlinePush || l > 32 || l < 2) {
    const items = xs.map((e, k) => assign_(idx_(stack, offset(k + 1)), e));
    return mconcatJStgStat([adjSp_(l), ...items]);
  }
  return { tag: "ApplStat", fn: Var(pushN[l]), args: xs };
}

/** Grow the stack pointer by 'n' without modifying the stack depth. The stack
 * is just a JS array so we add to grow (instead of the traditional subtract) */
export function adjSp_(n: number): JStgStat {
  if (n === 0) return memptyJStgStat;
  return assign_(sp, jAdd(sp, jInt(n)));
}

/** Shrink the stack pointer by 'n'. The stack grows downward so substract */
export function adjSpN_(n: number): JStgStat {
  if (n === 0) return memptyJStgStat;
  return assign_(sp, jSub(sp, jInt(n)));
}

/** Wrapper which adjusts the stack pointer /and/ modifies the tracked stack
 * depth. See also 'adjSp_' which actually does the stack pointer
 * manipulation. */
export function adjSp(g: StackState, n: number): JStgStat {
  if (n === 0) return memptyJStgStat;
  // grow depth by n
  modifyStackDepth(g, (d) => d + n);
  return adjSp_(n);
}

/** Shrink the stack and stack pointer. NB: This function is unsafe when the
 * input 'n', is negative. */
export function adjSpN(g: StackState, n: number): JStgStat {
  if (n === 0) return memptyJStgStat;
  modifyStackDepth(g, (x) => x - n);
  return adjSpN_(n);
}

/** A constant array that holds global function symbols which do N pushes onto
 * the stack. For example:
 *
 *     function h$p1(x1) { ++h$sp; h$stack[(h$sp - 0)] = x1; };
 *     function h$p2(x1, x2) { h$sp += 2; h$stack[(h$sp - 1)] = x1;
 *                             h$stack[(h$sp - 0)] = x2; };
 *
 * and so on up to 32. Haskell uses `listArray (1,32)`; TS arrays are
 * 0-indexed, so index 0 is a filler and `pushN[l]` indexes the same way `!`
 * does. */
export const pushN: Ident[] = [name(""), ...Array.from({ length: 32 }, (_, k) => name(`h$p${k + 1}`))];

/** Convert all function symbols in 'pushN' to global top-level functions. This
 * is a hack which converts the function symbols to variables. This hack is
 * caught in GHC.StgToJS.Printer.prettyBlock' to turn these into global
 * functions. */
export const pushN_: JStgExpr[] = pushN.map(Var);

/** Partial push functions. Like 'pushN' except these push functions skip
 * slots. For example,
 *
 *     function h$pp33(x1, x2) { h$sp += 6; h$stack[(h$sp - 5)] = x1;
 *                               h$stack[(h$sp - 0)] = x2; };
 *
 * The 33rd entry skips slots 1-4 to bind the top of the stack and the 6th
 * slot. Same 1-based indexing convention as 'pushN'. */
export const pushNN: Ident[] = [name(""), ...Array.from({ length: 255 }, (_, k) => name(`h$pp${k + 1}`))];

/** Like 'pushN_' but for the partial push functions */
export const pushNN_: JStgExpr[] = pushNN.map(Var);

/** optimized push that reuses existing values on stack automatically chooses
 * an optimized partial push (h$ppN) function when possible.
 *
 * @param xs contents of the slots, `true` if same value is already there */
export function pushOptimized(g: StackState, cs: StgToJSConfig, xs: Array<[JStgExpr, boolean]>): JStgStat {
  if (xs.length === 0) return memptyJStgStat;
  const l = xs.length;
  dropSlots(g, l);
  modifyStackDepth(g, (d) => d + xs.length);

  const offset = (i: number): JStgExpr => (i === l ? sp : jSub(sp, jInt(l - i)));
  const pushSlot = (i: number, [ex, known]: [JStgExpr, boolean]): JStgStat =>
    known ? memptyJStgStat : assign_(idx_(stack, offset(i)), ex);
  const inlinePush = (): JStgStat => mconcatJStgStat([adjSp_(l), ...xs.map((x, k) => pushSlot(k + 1, x))]);

  if (cs.inlinePush) return inlinePush();
  if (xs.every(([, b]) => b)) return adjSp_(l);
  if (xs.every(([, b]) => !b) && l <= 32) return { tag: "ApplStat", fn: pushN_[l], args: xs.map(([e]) => e) };
  if (l <= 8 && !xs[l - 1][1]) {
    // one bit per slot that must actually be written; the h$ppN symbol encodes
    // which slots the callee skips
    const sig = xs.reduce((acc, [, b], i) => acc | (b ? 0 : 1 << i), 0);
    return { tag: "ApplStat", fn: pushNN_[sig], args: xs.filter(([, b]) => !b).map(([e]) => e) };
  }
  return inlinePush();
}

/** Pop things, don't update the stack knowledge */
export function popSkip(n: number, tgt: JStgExpr[]): JStgStat {
  if (tgt.length === 0) return n === 0 ? memptyJStgStat : adjSpN_(n);
  return mconcatJStgStat([loadSkip(n, tgt), adjSpN_(tgt.length + n)]);
}

/** Load `xs.length` things from the stack at offset `n`. This function does no
 * stack pointer manipulation, it merely indexes into the stack and loads
 * payloads into `xs`. */
export function loadSkip(n: number, xs: JStgExpr[]): JStgStat {
  return loadSkipFrom(sp, n, xs);
}

function loadSkipFrom(fr: JStgExpr, n: number, xs: JStgExpr[]): JStgStat {
  const offset = (i: number): JStgExpr => (i === 0 ? fr : jSub(fr, jInt(i)));
  const items = [...xs].reverse().map((ex, i) => assign_(ex, idx_(stack, offset(i + n))));
  return mconcatJStgStat(items.reverse());
}

/** Pop but preserve the first N slots */
export function popSkipI(g: StackState, n: number, xs: Array<[Ident, StackSlot]>): JStgStat {
  if (xs.length === 0) return n === 0 ? memptyJStgStat : popN(g, n);
  // add N unknown slots
  addUnknownSlots(g, n);
  // now add the slots from xs, after this line the stack should look like
  // [xs] ++ [Unknown...] ++ old_stack
  addSlots(g, xs.map(([, s]) => s));
  // move stack pointer into the stack by (length xs + n), basically resetting
  // the stack pointer
  const a = adjSpN(g, xs.length + n);
  // now load skipping first N slots
  return mconcatJStgStat([loadSkipI(n, xs.map(([i]) => i)), a]);
}

/** Just like 'loadSkip' but operate on 'Ident's rather than 'JStgExpr' */
export function loadSkipI(n: number, xs: Ident[]): JStgStat {
  return loadSkipIFrom(sp, n, xs);
}

function loadSkipIFrom(fr: JStgExpr, n: number, xs: Ident[]): JStgStat {
  const offset = (i: number): JStgExpr => (i === 0 ? fr : jSub(fr, jInt(i)));
  const items = [...xs].reverse().map((ex, i) => declAssign_(ex, idx_(stack, offset(i + n))));
  return mconcatJStgStat(items.reverse());
}

/** Blindly pop N slots */
export function popN(g: StackState, n: number): JStgStat {
  addUnknownSlots(g, n);
  return adjSpN(g, n);
}

/** Generate statements to update the current node with a blackhole */
export function bhStats(s: StgToJSConfig, pushUpd: boolean): JStgStat {
  const r1 = register(R1);
  return mconcatJStgStat([
    pushUpd ? push_(s, [r1, hdUpdFrame]) : memptyJStgStat,
    assign_(sel_(r1, closureInfo_), hdBlackHole),
    assign_(sel_(r1, closureField1_), hdCurrentThread),
    assign_(sel_(r1, closureField2_), null_), // will be filled with waiters array
  ]);
}

/** Wrapper around 'updateThunk_', performs the stack manipulation before
 * updating the Thunk. */
export function updateThunk(g: StackState, settings: StgToJSConfig): JStgStat {
  // update frame size
  const adjPushStack = (n: number): void => {
    modifyStackDepth(g, (d) => d + n);
    dropSlots(g, n);
  };
  adjPushStack(2);
  return updateThunk_(settings);
}

/** Update a thunk by checking 'StgToJSConfig'. If the config inlines black
 * holes then update inline, else make an explicit call to the black hole
 * handler. */
export function updateThunk_(settings: StgToJSConfig): JStgStat {
  return settings.inlineBlackhole ? bhStats(settings, true) : { tag: "ApplStat", fn: hdBh, args: [] };
}
