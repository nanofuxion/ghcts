/** Core-to-Core: erase newtype constructors, as GHC does.
 *
 * In GHC a newtype's constructor is a coercion: `IO f` is `f`, and `case m of
 * IO f -> e` binds `f` to `m` without evaluating anything. Until this pass
 * ghcts compiled every newtype as a one-field data type, so each `>>=` in IO
 * allocated an `IO` box and each `unIO` entered one - misogram allocated
 * 174,568 `IO` boxes on a single re-render, a fifth of everything it built.
 *
 * Runs on the desugarer's output, so nothing after it ever sees a newtype
 * constructor. A newtype over a primitive (`newtype X = X JSValPrim`) is left
 * alone: the foreign-call marshalling (`boxTypes`) treats that as the box it
 * is, and so does codegen.
 */
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "./core.js";
import { copy } from "./core-opt/inline.js";
import type { Binder } from "./stg.js";

const trivial = (e: CoreExpr): boolean => e.tag === "Var" || e.tag === "Lit";

export function eraseNewtypes(program: CoreProgram): CoreProgram {
  let changed = false;
  const go = (e: CoreExpr): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App":
        return { tag: "App", fn: go(e.fn), arg: go(e.arg) };
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: go(e.body) };
      case "Let":
        return { tag: "Let", bind: bind(e.bind), body: go(e.body) };
      case "Con":
        if (e.con.newtype) {
          changed = true;
          return go(e.args[0]!);
        }
        return { tag: "Con", con: e.con, args: e.args.map(go) };
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map(go) };
      case "Case": {
        const alt = e.alts.find((a) => a.con.tag === "DataAlt" && a.con.con.newtype);
        if (!alt) {
          const alts: CoreAlt[] = e.alts.map((a) => ({ ...a, body: go(a.body) }));
          return { tag: "Case", scrutinee: go(e.scrutinee), binder: e.binder, alts };
        }
        changed = true;
        const scrutinee = go(e.scrutinee);
        const body = go(alt.body);
        const field = alt.binders[0]!;
        // `case m of IO f -> e` is `let f = m in e`: the field IS the
        // scrutinee, unevaluated. A trivial scrutinee is substituted outright.
        if (trivial(scrutinee)) return copy(body, new Map([[field.unique, scrutinee], [e.binder.unique, scrutinee]]), new Map());
        const rhs: CoreExpr = { tag: "Var", binder: e.binder };
        return { tag: "Let", bind: { tag: "NonRec", binder: e.binder, rhs: scrutinee }, body: copy(body, new Map([[field.unique, rhs]]), new Map()) };
      }
    }
  };
  const bind = (b: CoreBind): CoreBind =>
    b.tag === "NonRec"
      ? { tag: "NonRec", binder: b.binder, rhs: go(b.rhs) }
      : { tag: "Rec", pairs: b.pairs.map(([x, r]) => [x, go(r)] as [Binder, CoreExpr]) };
  const binds = program.binds.map(bind);
  return changed ? { ...program, binds } : program;
}
