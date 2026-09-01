/** Core-to-Core: give every constant constructor one home.
 *
 * `orZero Nothing = 0` returns the box `I# 0#`. Written inside the branch it
 * is a fresh allocation on every call, and there is no reason for it to be:
 * the value never changes and Haskell data never changes under it. GHC lifts
 * it out to a top-level binding - `scripts/stg-diff.mjs` shows GHC's `orZero`
 * returning `Main.orZero1` where ghcts builds the box again - so the branch
 * returns a pointer to something the program allocated once, at load.
 *
 * This is the constant half of GHC's `FloatOut`/full laziness. Only fully
 * literal constructor applications move, including nullary ones, so what is
 * shared is decided by looking at the term and nothing else: `Nothing`, `[]`,
 * `True`, `I# 0#`, `C# 'x'#`. Anything with a variable in it stays where it
 * is, where its scope keeps it honest.
 *
 * Identical constants share one binding, so a module that mentions `0` in
 * forty branches allocates one box rather than forty.
 */
import type { CoreAlt, CoreBind, CoreExpr, CoreProgram } from "../core.js";
import { coreFreeVars } from "../core.js";
import { mkBinder, type Binder, type Literal } from "../stg.js";

const litKey = (l: Literal): string =>
  l.tag === "LitLabel" ? `${l.tag}:${l.name}` : `${l.tag}:${String((l as { value?: unknown }).value ?? "")}`;

/** A one-field box of an `Int`/`Char`/`Double`/… is not an allocation on this
 * backend - the value is the number itself - and `GHC.StgToJS.Sinker` unfloats
 * exactly these again, so lifting one out buys nothing and leaves a top-level
 * name for the sinker to remove out from under its own references. */
const UNBOXED_REP = new Set([
  "Int", "Int8", "Int16", "Int32", "Word", "Word8", "Word16", "Word32",
  "Char", "Float", "Double",
]);

const constKey = (e: Extract<CoreExpr, { tag: "Con" }>): string | undefined => {
  if (e.args.length === 1 && UNBOXED_REP.has(e.con.typeName)) return undefined;
  const parts: string[] = [];
  for (const a of e.args) {
    if (a.tag !== "Lit") return undefined;
    parts.push(litKey(a.lit));
  }
  return `${e.con.typeName}|${e.con.name}|${parts.join(",")}`;
};

/** A structural name for a closed expression, so two spellings of the same
 * constant reach the same binding. Returns `undefined` for anything whose
 * meaning is not fixed by its shape. */
function shapeKey(e: CoreExpr): string | undefined {
  switch (e.tag) {
    case "Var":
      return `v${e.binder.unique}`;
    case "Lit":
      return `l${litKey(e.lit)}`;
    case "App": {
      const f = shapeKey(e.fn);
      const a = shapeKey(e.arg);
      return f && a ? `(${f} ${a})` : undefined;
    }
    case "Con": {
      const as = e.args.map(shapeKey);
      return as.every((x) => x) ? `C${e.con.typeName}.${e.con.name}[${as.join(",")}]` : undefined;
    }
    default:
      return undefined;
  }
}

/** A literal, or a constructor built only out of those. */
const constArg = (e: CoreExpr): boolean =>
  e.tag === "Lit" || (e.tag === "Con" && e.args.every(constArg));

/** `f "a" ['b']`: a known function applied to nothing but constants. */
const constApp = (e: CoreExpr): boolean => {
  let head = e;
  while (head.tag === "App") {
    if (!constArg(head.arg)) return false;
    head = head.fn;
  }
  return head.tag === "Var";
};

const nodes = (e: CoreExpr): number => {
  switch (e.tag) {
    case "Var":
    case "Lit":
      return 1;
    case "App":
      return 1 + nodes(e.fn) + nodes(e.arg);
    case "Con":
    case "Op":
      return 1 + e.args.reduce((n, a) => n + nodes(a), 0);
    default:
      return 1000;
  }
};

/** Bodies bigger than this are left where they are: floating one would trade a
 * repeated computation for a permanently retained one, and the terms worth
 * sharing - `fromString "Miso.patches"` and its kind - are small. */
const MAX_FLOAT = 300;

export function floatConstants(program: CoreProgram): CoreProgram {
  const shared = new Map<string, Binder>();
  const floated: CoreBind[] = [];
  const tops = new Set<number>();
  for (const b of program.binds)
    if (b.tag === "NonRec") tops.add(b.binder.unique);
    else for (const [x] of b.pairs) tops.add(x.unique);
  const closed = (e: CoreExpr): boolean =>
    [...coreFreeVars(e)].every((v) => tops.has(v.unique));

  /** Full laziness, narrowed to calls on constants. `pack "Miso.patches"`
   * inside a function is recomputed on every call - the counter app packs 311
   * constant strings per tap, where GHC packs none - because GHC's `FloatOut`
   * lifts a closed subexpression out of the lambda that encloses it and
   * evaluates it once, as a top-level thunk. Only expressions under a lambda
   * are worth moving: one at the top of a binding already runs once.
   *
   * `closed` is not enough on its own to decide that two occurrences are the
   * same value. Miso frees its own JavaScript handles - `(#)` in
   * `references/miso/src/Miso/DSL.hs` calls `freeJSVal` on the argument array
   * it built, calling it "a temporary nobody else can reach" - so giving two
   * occurrences one shared handle makes the second call read a handle the
   * first one released. That is what `classes is not iterable` was. A call on
   * nothing but literals is the shape this pass was written for and the shape
   * that stays true under sharing. */
  const lift = (e: CoreExpr): CoreExpr | undefined => {
    if (e.tag !== "App" || nodes(e) > MAX_FLOAT || !closed(e) || !constApp(e)) return undefined;
    const key = shapeKey(e);
    if (key === undefined) return undefined;
    let binder = shared.get(key);
    if (!binder) {
      binder = mkBinder("lvl", { internal: true });
      shared.set(key, binder);
      floated.push({ tag: "NonRec", binder, rhs: e });
    }
    return { tag: "Var", binder };
  };

  const go = (e: CoreExpr, underLam = false): CoreExpr => {
    switch (e.tag) {
      case "Var":
      case "Lit":
        return e;
      case "App": {
        if (underLam) {
          const lifted = lift(e);
          if (lifted) return lifted;
        }
        return { tag: "App", fn: go(e.fn, underLam), arg: go(e.arg, underLam) };
      }
      case "Lam":
        return { tag: "Lam", binder: e.binder, body: go(e.body, true) };
      case "Let": {
        const bind: CoreBind =
          e.bind.tag === "NonRec"
            ? { tag: "NonRec", binder: e.bind.binder, rhs: go(e.bind.rhs, underLam) }
            : {
                tag: "Rec",
                pairs: e.bind.pairs.map(([b, r]) => [b, go(r, underLam)] as [Binder, CoreExpr]),
              };
        return { tag: "Let", bind, body: go(e.body, underLam) };
      }
      case "Case": {
        const alts: CoreAlt[] = e.alts.map((a) => ({ ...a, body: go(a.body, underLam) }));
        return { tag: "Case", scrutinee: go(e.scrutinee, underLam), binder: e.binder, alts };
      }
      case "Op":
        return { tag: "Op", op: e.op, arity: e.arity, args: e.args.map((a) => go(a, underLam)) };
      case "Con": {
        const key = constKey(e);
        if (key === undefined) return { tag: "Con", con: e.con, args: e.args.map((a) => go(a, underLam)) };
        let binder = shared.get(key);
        if (!binder) {
          // GHC names these `lvl`; keeping the name makes the two dumps line
          // up when they are read side by side.
          binder = mkBinder("lvl", { internal: true });
          shared.set(key, binder);
          floated.push({ tag: "NonRec", binder, rhs: e });
        }
        return { tag: "Var", binder };
      }
    }
  };

  // A top-level binding whose whole right-hand side is already a constant is
  // its own home: rewriting it to point at a copy of itself would be a loop.
  const binds = program.binds.map((b) =>
    b.tag === "NonRec"
      ? { tag: "NonRec" as const, binder: b.binder, rhs: b.rhs.tag === "Con" ? b.rhs : go(b.rhs) }
      : {
          tag: "Rec" as const,
          pairs: b.pairs.map(([bd, r]) => [bd, r.tag === "Con" ? r : go(r)] as [Binder, CoreExpr]),
        },
  );
  return floated.length === 0 ? program : { ...program, binds: [...floated, ...binds] };
}
