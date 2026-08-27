/** Core, cut down from `references/ghc/compiler/GHC/Core.hs`.
 *
 * GHC's Core is an explicitly typed lambda calculus: `Var`, `Lit`, `App`,
 * `Lam`, `Let`, `Case`, `Cast`, `Tick`, `Type`, `Coercion`. A JS backend that
 * has already been type-checked upstream needs none of the last five - there
 * is no unboxing decision left to make from a type, no coercion to erase, and
 * no ticks to preserve - so this keeps the first six and drops the rest.
 *
 * Two deliberate departures from GHC:
 *
 *   - data constructors and primops are their own nodes rather than `Var`s
 *     wrapping an `Id` with a `DataConWorkId`/`PrimOpId` unfolding. STG needs
 *     them saturated and distinguishable, and giving them nodes with an
 *     `args` list means the desugarer - which knows every arity - can
 *     establish that invariant once, at the only place the information
 *     exists. `Con` and `Op` are therefore ALWAYS saturated; an unsaturated
 *     occurrence is eta-expanded into a `Lam` by the desugarer.
 *   - binders are `src/stg.ts`'s `Binder`, not a separate Core `Id`. Core to
 *     STG is then identity on names, so a variable cannot be captured or
 *     renamed by accident on the way down.
 */
import type { Binder, DataCon, Literal, StgOp } from "./stg.js";

export type CoreAltCon =
  | { tag: "DataAlt"; con: DataCon }
  | { tag: "LitAlt"; lit: Literal }
  | { tag: "DEFAULT" };

export interface CoreAlt {
  con: CoreAltCon;
  /** Fields bound by a DataAlt, in constructor field order. */
  binders: Binder[];
  body: CoreExpr;
}

export type CoreExpr =
  | { tag: "Var"; binder: Binder }
  | { tag: "Lit"; lit: Literal }
  | { tag: "App"; fn: CoreExpr; arg: CoreExpr }
  | { tag: "Lam"; binder: Binder; body: CoreExpr }
  | { tag: "Let"; bind: CoreBind; body: CoreExpr }
  /** The binder names the evaluated scrutinee, exactly as in GHC. */
  | { tag: "Case"; scrutinee: CoreExpr; binder: Binder; alts: CoreAlt[] }
  /** Saturated by construction - see the header. */
  | { tag: "Con"; con: DataCon; args: CoreExpr[] }
  /** Saturated by construction. `arity` is kept so eta-expansion and STG
   * conversion agree on how many arguments the op consumes. */
  | { tag: "Op"; op: StgOp; arity: number; args: CoreExpr[] };

export type CoreBind =
  | { tag: "NonRec"; binder: Binder; rhs: CoreExpr }
  | { tag: "Rec"; pairs: Array<[Binder, CoreExpr]> };

export interface CoreProgram {
  name: string;
  binds: CoreBind[];
  /** Every constructor the module declares or uses. The STG pass turns each
   * into the top-level worker binding codegen expects to find. */
  dataCons: DataCon[];
}

export const mkApps = (fn: CoreExpr, args: CoreExpr[]): CoreExpr =>
  args.reduce<CoreExpr>((f, arg) => ({ tag: "App", fn: f, arg }), fn);

export const mkLams = (binders: Binder[], body: CoreExpr): CoreExpr =>
  binders.reduceRight<CoreExpr>((b, binder) => ({ tag: "Lam", binder, body: b }), body);

/** Free variables, by binder identity. Used to decide whether a `let` group
 * is genuinely recursive; STG conversion recomputes this on its own output. */
export function coreFreeVars(expr: CoreExpr, bound: Set<Binder> = new Set()): Set<Binder> {
  const free = new Set<Binder>();
  const go = (e: CoreExpr, scope: Set<Binder>): void => {
    switch (e.tag) {
      case "Var":
        if (!scope.has(e.binder)) free.add(e.binder);
        return;
      case "Lit":
        return;
      case "App":
        go(e.fn, scope);
        go(e.arg, scope);
        return;
      case "Lam":
        go(e.body, new Set([...scope, e.binder]));
        return;
      case "Let": {
        const bound_ =
          e.bind.tag === "NonRec" ? [e.bind.binder] : e.bind.pairs.map(([b]) => b);
        // A Rec group's binders scope over the right-hand sides too.
        const rhsScope = e.bind.tag === "NonRec" ? scope : new Set([...scope, ...bound_]);
        if (e.bind.tag === "NonRec") go(e.bind.rhs, rhsScope);
        else for (const [, rhs] of e.bind.pairs) go(rhs, rhsScope);
        go(e.body, new Set([...scope, ...bound_]));
        return;
      }
      case "Case": {
        go(e.scrutinee, scope);
        const inner = new Set([...scope, e.binder]);
        for (const alt of e.alts) go(alt.body, new Set([...inner, ...alt.binders]));
        return;
      }
      case "Con":
      case "Op":
        for (const arg of e.args) go(arg, scope);
        return;
    }
  };
  go(expr, bound);
  return free;
}
