/** Port of GHC.JS.Opt.Simple: the first optimization pass run over freshly
 * generated JS, invoked on the top-level statement but only actually
 * traversing into function bodies (nested functions are left alone). It:
 *   - renames local variables to shorter names
 *   - removes unused variables
 *   - removes trivial assignments: x = x
 *   - "floats" expressions without side effects into their single use site
 *
 * Optimization is disabled for a function if it contains an `eval`, and
 * variables declared in nested scopes are never renamed - both ported
 * faithfully from the Haskell "Limitations" section. */
import type { Ident } from "./ident.js";
import type { JStat, JExpr, JVal, AOp } from "./syntax.js";
import { optExprs } from "./opt-expr.js";

type Multiplicity = "Zero" | "One" | "Many";
const combineMultiplicity = (a: Multiplicity, b: Multiplicity): Multiplicity => (a === "Zero" ? b : b === "Zero" ? a : "Many");

type VarValue =
  | { tag: "Unassigned" }
  | { tag: "AssignedOnce" }
  | { tag: "AssignedOnceKnown"; expr: JExpr }
  | { tag: "AssignedMany" };
const combineVarValue = (a: VarValue, b: VarValue): VarValue => (a.tag === "Unassigned" ? b : b.tag === "Unassigned" ? a : { tag: "AssignedMany" });

type VarDecl =
  | { tag: "NoDecl" }
  | { tag: "ArgDecl"; n: number }
  | { tag: "LocalDecl"; n: number };
const isLocalOrArg = (d: VarDecl): boolean => d.tag === "LocalDecl" || d.tag === "ArgDecl";
const isDecl = (d: VarDecl): boolean => d.tag !== "NoDecl";
function combineVarDecl(a: VarDecl, b: VarDecl): VarDecl {
  if (a.tag === "NoDecl") return b;
  if (b.tag === "NoDecl") return a;
  if (a.tag === "ArgDecl" && b.tag === "ArgDecl") return { tag: "ArgDecl", n: Math.min(a.n, b.n) };
  if (a.tag === "LocalDecl" && b.tag === "LocalDecl") return { tag: "LocalDecl", n: Math.min(a.n, b.n) };
  return a.tag === "ArgDecl" ? a : b.tag === "ArgDecl" ? b : a;
}
/** VarDecl's Ord instance: NoDecl < ArgDecl _ < LocalDecl _, ties by n. */
function compareVarDecl(a: VarDecl, b: VarDecl): number {
  if (a.tag === "NoDecl" && b.tag === "NoDecl") return 0;
  if (a.tag === "NoDecl") return -1;
  if (b.tag === "NoDecl") return 1;
  if (a.tag === "ArgDecl" && b.tag === "ArgDecl") return a.n - b.n;
  if (a.tag === "ArgDecl") return -1;
  if (b.tag === "ArgDecl") return 1;
  return (a as { n: number }).n - (b as { n: number }).n;
}

interface VarUsage {
  varUsed: Multiplicity;
  varAssigned: VarValue;
  varDeclared: VarDecl;
  varDeepDeclared: boolean;
}
const mkUsage = (used: Multiplicity, assigned: VarValue, declared: VarDecl, deep: boolean): VarUsage => ({ varUsed: used, varAssigned: assigned, varDeclared: declared, varDeepDeclared: deep });
const combineUsage = (x: VarUsage, y: VarUsage): VarUsage => ({
  varUsed: combineMultiplicity(x.varUsed, y.varUsed),
  varAssigned: combineVarValue(x.varAssigned, y.varAssigned),
  varDeclared: combineVarDecl(x.varDeclared, y.varDeclared),
  varDeepDeclared: x.varDeepDeclared || y.varDeepDeclared,
});
const assignedMultiple = (vu: VarUsage): boolean => vu.varAssigned.tag === "AssignedMany";

interface SimpleRewrite {
  renameVar: Map<Ident, Ident>;
  varUsage: Map<Ident, VarUsage>;
}

interface JFunction {
  args: Ident[];
  body: JStat;
}

const RESERVED = new Set([
  "abstract", "arguments", "await", "boolean",
  "break", "byte", "case", "catch",
  "char", "class", "const", "continue",
  "debugger", "default", "delete", "do",
  "double", "else", "enum", "eval",
  "export", "extends", "false", "final",
  "finally", "float", "for", "function",
  "goto", "if", "implements", "import",
  "in", "instanceof", "int", "interface",
  "let", "long", "native", "new",
  "null", "package", "private", "protected",
  "public", "return", "short", "static",
  "super", "switch", "synchronized", "this",
  "throw", "throws", "transient", "true",
  "try", "typeof", "var", "void",
  "volatile", "while", "with", "yield",
  "as", "async", "from", "get",
  "of", "NaN", "prototype", "undefined",
]);

const CHARS0 = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
const CHARS = CHARS0 + "0123456789";

/** GHC.JS.Opt.Simple.newLocals: an infinite stream of candidate identifiers
 * (a, b, ..., Z, aa, ab, ..., aA, ...), skipping JS reserved words. */
function* newLocals(): Generator<Ident> {
  for (const c of CHARS0) if (!RESERVED.has(c)) yield c;
  for (let n = 1; ; n++) {
    for (const c0 of CHARS0) {
      for (const suffix of fixedLengthStrings(CHARS, n)) {
        const candidate = c0 + suffix;
        if (!RESERVED.has(candidate)) yield candidate;
      }
    }
  }
}

function* fixedLengthStrings(alphabet: string, n: number): Generator<string> {
  if (n === 0) { yield ""; return; }
  for (const c of alphabet) for (const rest of fixedLengthStrings(alphabet, n - 1)) yield c + rest;
}

function mkRewrite(doRename: boolean, a: AnalysisResult): SimpleRewrite | undefined {
  if (a.bailout) return undefined;
  const declaredEntries = [...a.varUsage.entries()].filter(([, u]) => isDecl(u.varDeclared));
  const localVars = declaredEntries
    .slice()
    .sort(([, ua], [, ub]) => compareVarDecl(ua.varDeclared, ub.varDeclared))
    .map(([v]) => v);
  const blockedNames = new Set(
    [...a.varUsage.entries()].filter(([, u]) => !isDecl(u.varDeclared) || u.varDeepDeclared).map(([v]) => v),
  );
  const renameVar = new Map<Ident, Ident>();
  if (doRename) {
    const gen = newLocals();
    for (const v of localVars) {
      let candidate = gen.next().value as string;
      while (blockedNames.has(candidate)) candidate = gen.next().value as string;
      renameVar.set(v, candidate);
    }
  }
  return { renameVar, varUsage: a.varUsage };
}

function simpleRewrite(rw: SimpleRewrite, jf: JFunction): JFunction {
  const varReplace = (v: Ident): Ident => rw.renameVar.get(v) ?? v;

  const zeroUsed = (e: JExpr): boolean => {
    if (e.tag !== "ValExpr" || e.value.tag !== "JVar") return false;
    const vu = rw.varUsage.get(e.value.ident);
    return vu !== undefined && vu.varUsed === "Zero" && isDecl(vu.varDeclared);
  };

  const mayBeFloatedV = (v: JVal): boolean => {
    switch (v.tag) {
      case "JVar": {
        const vu = rw.varUsage.get(v.ident);
        return vu !== undefined && isDecl(vu.varDeclared) && !assignedMultiple(vu);
      }
      case "JList": return v.values.every(mayBeFloated);
      case "JDouble": case "JInt": case "JStr": case "JRegEx": case "JBool": return true;
      case "JHash": return v.entries.every(([, e]) => mayBeFloated(e));
      case "JFunc": return false;
    }
  };
  function mayBeFloated(e: JExpr): boolean {
    switch (e.tag) {
      case "ValExpr": return mayBeFloatedV(e.value);
      case "SelExpr": return false;
      case "IdxExpr": return false;
      case "InfixExpr": return mayBeFloated(e.left) && mayBeFloated(e.right);
      case "UOpExpr": return false;
      case "IfExpr": return mayBeFloated(e.cond) && mayBeFloated(e.then) && mayBeFloated(e.else);
      case "ApplExpr": return e.fn.tag === "ValExpr" && e.fn.value.tag === "JVar" && isClosureAllocator(e.fn.value.ident) && e.args.every(mayBeFloated);
      case "RawExpr": return false;
    }
  }

  const mayDuplicate = (e: JExpr): boolean => {
    if (e.tag === "ValExpr" && e.value.tag === "JVar") {
      const vu = rw.varUsage.get(e.value.ident);
      return vu !== undefined && isLocalOrArg(vu.varDeclared);
    }
    if (e.tag === "ValExpr" && e.value.tag === "JInt") return e.value.value < 0n ? -e.value.value < 1000000n : e.value.value < 1000000n;
    if (e.tag === "ValExpr" && e.value.tag === "JDouble") return true;
    return false;
  };

  const zeroAssigned = (v: Ident): boolean => rw.varUsage.get(v)?.varAssigned.tag === "Unassigned";

  const assignedAtMostOnce = (v: Ident): boolean => {
    const vu = rw.varUsage.get(v);
    return vu === undefined || vu.varAssigned.tag !== "AssignedMany";
  };

  const goV = (v: JVal): JVal => {
    switch (v.tag) {
      case "JVar": return { tag: "JVar", ident: varReplace(v.ident) };
      case "JList": return { ...v, values: v.values.map((e) => goE(true, e)) };
      case "JHash": return { ...v, entries: v.entries.map(([k, e]): [string, JExpr] => [k, goE(true, e)]) };
      case "JFunc": case "JDouble": case "JInt": case "JStr": case "JRegEx": case "JBool": return v;
    }
  };

  const goE = (rhs: boolean, e: JExpr): JExpr => {
    if (rhs && e.tag === "ValExpr" && e.value.tag === "JVar") {
      const vu = rw.varUsage.get(e.value.ident);
      if (vu && vu.varAssigned.tag === "AssignedOnceKnown") {
        const ee = vu.varAssigned.expr;
        if ((vu.varUsed === "One" || mayDuplicate(ee)) && isDecl(vu.varDeclared) && mayBeFloated(ee)) return goE(rhs, ee);
      }
    }
    switch (e.tag) {
      case "ValExpr": return { tag: "ValExpr", value: goV(e.value) };
      case "SelExpr": return { ...e, obj: goE(rhs, e.obj) };
      case "IdxExpr": return { ...e, obj: goE(rhs, e.obj), index: goE(rhs, e.index) };
      case "InfixExpr": return { ...e, left: goE(rhs, e.left), right: goE(rhs, e.right) };
      case "UOpExpr": return { ...e, value: goE(rhs, e.value) };
      case "IfExpr": return { ...e, cond: goE(rhs, e.cond), then: goE(rhs, e.then), else: goE(rhs, e.else) };
      case "ApplExpr": return { ...e, fn: goE(rhs, e.fn), args: e.args.map((a) => goE(rhs, a)) };
      case "RawExpr": return e;
    }
  };

  const go = (s: JStat): JStat => {
    switch (s.tag) {
      case "DeclStat": {
        const v = s.ident;
        if (zeroUsed({ tag: "ValExpr", value: { tag: "JVar", ident: v } })) {
          if (s.value === undefined) return zeroAssigned(v) ? { tag: "BlockStat", stats: [] } : { tag: "DeclStat", ident: varReplace(v) };
          if (!mayHaveSideEffects(s.value) && assignedAtMostOnce(v)) return { tag: "BlockStat", stats: [] };
          return { tag: "DeclStat", ident: varReplace(v), value: goE(true, s.value) };
        }
        return { tag: "DeclStat", ident: varReplace(v), value: s.value && goE(true, s.value) };
      }
      case "AssignStat": {
        if (s.lhs.tag === "ValExpr" && s.lhs.value.tag === "JVar" && isTrivialAssignment(s.lhs.value.ident, s.op, s.rhs)) return { tag: "BlockStat", stats: [] };
        if (zeroUsed(s.lhs) && !mayHaveSideEffects(s.rhs)) return { tag: "BlockStat", stats: [] };
        return { ...s, lhs: goE(false, s.lhs), rhs: goE(true, s.rhs) };
      }
      case "ReturnStat": return { ...s, value: goE(true, s.value) };
      case "BlockStat": return flattenBlock(s.stats.map(go));
      case "IfStat": return { ...s, cond: goE(true, s.cond), then: go(s.then), else: go(s.else) };
      case "WhileStat": return { ...s, cond: goE(true, s.cond), body: go(s.body) };
      case "ForStat": return { ...s, init: go(s.init), cond: goE(true, s.cond), step: go(s.step), body: go(s.body) };
      case "ForInStat": return { ...s, ident: varReplace(s.ident), obj: goE(true, s.obj), body: go(s.body) };
      case "SwitchStat": return { ...s, scrut: goE(true, s.scrut), cases: s.cases.map(([c, cs]): [JExpr, JStat] => [c, go(cs)]), default: go(s.default) };
      case "TryStat": return { ...s, body: go(s.body), ident: varReplace(s.ident), catch: go(s.catch), finally: go(s.finally) };
      case "ApplStat": return { ...s, fn: goE(true, s.fn), args: s.args.map((a) => goE(true, a)) };
      case "UOpStat": return { ...s, value: goE(false, s.value) };
      case "LabelStat": return { ...s, body: go(s.body) };
      case "BreakStat": case "ContinueStat": case "RawStat": return s;
      case "FuncStat": return { ...s, args: s.args.map(varReplace), body: go(s.body) };
      case "ThrowStat": return { ...s, value: goE(true, s.value) };
    }
  };

  return { args: jf.args.map(varReplace), body: go(jf.body) };
}

function flattenBlock(stats: JStat[]): JStat {
  const filtered = stats.filter((s) => !(s.tag === "BlockStat" && s.stats.length === 0));
  return filtered.length === 0 ? { tag: "BlockStat", stats: [] } : filtered.length === 1 ? filtered[0] : { tag: "BlockStat", stats: filtered };
}

interface AnalysisResult {
  bailout: boolean;
  varUsage: Map<Ident, VarUsage>;
  declaredCount: number;
}

function simpleAnalyze(jf: JFunction): AnalysisResult {
  const varUsage = new Map<Ident, VarUsage>();
  jf.args.forEach((v, n) => varUsage.set(v, mkUsage("Zero", { tag: "Unassigned" }, { tag: "ArgDecl", n }, false)));
  let result: AnalysisResult = { bailout: false, varUsage, declaredCount: 0 };

  const add = (i: Ident, vu: VarUsage, r: AnalysisResult): AnalysisResult => {
    const existing = r.varUsage.get(i);
    r.varUsage.set(i, existing ? combineUsage(existing, vu) : vu);
    return r;
  };

  const declare = (deep: boolean, i: Ident, assign: JExpr | undefined, r: AnalysisResult): AnalysisResult => {
    if (deep) return add(i, mkUsage("Zero", { tag: "AssignedMany" }, { tag: "NoDecl" }, true), r);
    const already = r.varUsage.get(i);
    const newCount = already && already.varDeclared.tag === "LocalDecl" ? r.declaredCount : r.declaredCount + 1;
    const vassign: VarValue = assign !== undefined ? { tag: "AssignedOnceKnown", expr: assign } : { tag: "Unassigned" };
    add(i, mkUsage("Zero", vassign, { tag: "LocalDecl", n: r.declaredCount }, false), r);
    r.declaredCount = newCount;
    return r;
  };

  const goV = (r: AnalysisResult, v: JVal): AnalysisResult => {
    switch (v.tag) {
      case "JVar": return add(v.ident, mkUsage("One", { tag: "Unassigned" }, { tag: "NoDecl" }, false), r);
      case "JList": return v.values.reduce(goE, r);
      case "JDouble": case "JInt": case "JStr": case "JRegEx": case "JBool": return r;
      case "JHash": return v.entries.reduce((acc, [, e]) => goE(acc, e), r);
      case "JFunc": {
        const withArgs = v.args.reduce((acc, arg) => add(arg, mkUsage("Zero", { tag: "AssignedOnce" }, { tag: "NoDecl" }, true), acc), r);
        return go(true, withArgs, v.body);
      }
    }
  };

  function goE(r: AnalysisResult, e: JExpr): AnalysisResult {
    switch (e.tag) {
      case "ValExpr": return goV(r, e.value);
      case "SelExpr": return goE(r, e.obj);
      case "IdxExpr": return goE(goE(r, e.obj), e.index);
      case "InfixExpr": return goE(goE(r, e.left), e.right);
      case "UOpExpr": return goE(r, e.value);
      case "IfExpr": return goE(goE(goE(r, e.cond), e.then), e.else);
      case "ApplExpr": {
        if (e.fn.tag === "ValExpr" && e.fn.value.tag === "JVar" && e.fn.value.ident === "eval") return { ...r, bailout: true };
        return e.args.reduce(goE, goE(r, e.fn));
      }
      case "RawExpr": return r;
    }
  }

  function go(deep: boolean, r: AnalysisResult, s: JStat): AnalysisResult {
    switch (s.tag) {
      case "DeclStat": return declare(deep, s.ident, s.value, s.value ? goE(r, s.value) : r);
      case "AssignStat": {
        if (s.lhs.tag === "ValExpr" && s.lhs.value.tag === "JVar") {
          const use: Multiplicity = s.op === "AssignOp" ? "Zero" : "One";
          return add(s.lhs.value.ident, mkUsage(use, { tag: "AssignedOnceKnown", expr: s.rhs }, { tag: "NoDecl" }, false), goE(r, s.rhs));
        }
        return goE(goE(r, s.lhs), s.rhs);
      }
      case "ReturnStat": return goE(r, s.value);
      case "BlockStat": return s.stats.reduce((acc, st) => go(deep, acc, st), r);
      case "IfStat": return go(deep, go(deep, goE(r, s.cond), s.then), s.else);
      case "WhileStat": return go(deep, goE(r, s.cond), s.body);
      case "ForStat": return go(deep, go(deep, goE(go(deep, r, s.init), s.cond), s.step), s.body);
      case "ForInStat": {
        const withDecl = s.isEach ? declare(deep, s.ident, undefined, r) : r;
        return add(s.ident, mkUsage("Zero", { tag: "AssignedMany" }, { tag: "NoDecl" }, true), go(deep, go(deep, goE(withDecl, s.obj), s.body), s.body));
      }
      case "SwitchStat": return go(deep, goE(s.cases.reduce((acc, [, cs]) => go(deep, acc, cs), r), s.scrut), s.default);
      case "TryStat": return add(s.ident, mkUsage("Zero", { tag: "AssignedMany" }, { tag: "NoDecl" }, true), go(deep, go(deep, go(deep, r, s.body), s.catch), s.finally));
      case "ApplStat": {
        if (s.fn.tag === "ValExpr" && s.fn.value.tag === "JVar" && s.fn.value.ident === "eval") return { ...r, bailout: true };
        return s.args.reduce(goE, goE(r, s.fn));
      }
      case "UOpStat": {
        if (s.value.tag === "ValExpr" && s.value.value.tag === "JVar" && (s.op === "PreIncOp" || s.op === "PostIncOp" || s.op === "PreDecOp" || s.op === "PostDecOp")) {
          return add(s.value.value.ident, mkUsage("One", { tag: "AssignedOnce" }, { tag: "NoDecl" }, false), r);
        }
        return goE(r, s.value);
      }
      case "LabelStat": return go(deep, r, s.body);
      case "BreakStat": case "ContinueStat": case "RawStat": return r;
      case "ThrowStat": return goE(r, s.value);
      case "FuncStat": {
        const withArgs = s.args.reduce((acc, arg) => add(arg, mkUsage("Zero", { tag: "AssignedOnce" }, { tag: "NoDecl" }, true), acc), r);
        return go(true, withArgs, s.body);
      }
    }
  }

  result = go(false, result, jf.body);
  return result;
}

/** A trivial assignment is an assignment of a variable to itself: x = x */
function isTrivialAssignment(v: Ident, aop: AOp, e: JExpr): boolean {
  return aop === "AssignOp" && e.tag === "ValExpr" && e.value.tag === "JVar" && e.value.ident === v;
}

/** Does the expression have side effects? Only returns false if it
 * definitely does not - i.e. it can be removed with no semantic change if
 * unused. Carries GHC's RTS-specific assumptions (h$stack indexing, dN
 * property reads) verbatim. */
function mayHaveSideEffects(e: JExpr): boolean {
  if (e.tag === "IdxExpr" && e.obj.tag === "ValExpr" && e.obj.value.tag === "JVar" && e.obj.value.ident === "h$stack") return mayHaveSideEffects(e.index);
  if (e.tag === "SelExpr" && isHeapObjectProperty(e.field)) return mayHaveSideEffects(e.obj);
  switch (e.tag) {
    case "ValExpr": return mayHaveSideEffectsV(e.value);
    case "SelExpr": return true;
    case "IdxExpr": return true;
    case "UOpExpr": {
      const pure = e.op === "NotOp" || e.op === "BNotOp" || e.op === "NegOp" || e.op === "PlusOp" || e.op === "TypeofOp";
      return !pure || mayHaveSideEffects(e.value);
    }
    case "InfixExpr": return mayHaveSideEffects(e.left) || mayHaveSideEffects(e.right);
    case "IfExpr": return mayHaveSideEffects(e.cond) || mayHaveSideEffects(e.then) || mayHaveSideEffects(e.else);
    case "ApplExpr": return true;
    case "RawExpr": return true;
  }
}

function mayHaveSideEffectsV(v: JVal): boolean {
  switch (v.tag) {
    case "JVar": return false;
    case "JList": return v.values.some(mayHaveSideEffects);
    case "JDouble": case "JInt": case "JStr": case "JRegEx": case "JBool": return false;
    case "JHash": return v.entries.some(([, e]) => mayHaveSideEffects(e));
    case "JFunc": return true;
  }
}

const isHeapObjectProperty = (ident: Ident): boolean => /^d([1-9]|1[0-9]|2[0-4])$/.test(ident);
const isClosureAllocator = (ident: Ident): boolean => /^h\$c([1-9]|1[0-9]|2[0-4])$/.test(ident);

function functionOptExprs(jf: JFunction): JFunction {
  return { args: jf.args, body: optExprs(jf.body) };
}

function simpleOptFunction(jf: JFunction): JFunction {
  const analysis0 = simpleAnalyze(jf);
  const rw0 = mkRewrite(false, analysis0);
  const opt0 = functionOptExprs(rw0 ? simpleRewrite(rw0, jf) : jf);

  const analysis1 = simpleAnalyze(opt0);
  const rw1 = mkRewrite(true, analysis1);
  return functionOptExprs(rw1 ? simpleRewrite(rw1, opt0) : opt0);
}

/** Always false in GHC.JS.Opt.Simple too - kept for shape parity with the
 * Haskell module's dead debugging switch. */
const disableOpt = false;

/** GHC.JS.Opt.Simple.simpleOpt: only descends into function bodies at the
 * top level; everything else is left untouched. */
export function simpleOpt(s: JStat): JStat {
  if (disableOpt) return s;
  if (s.tag === "BlockStat") return { ...s, stats: s.stats.map(simpleOpt) };
  if (s.tag === "AssignStat" && s.op === "AssignOp" && s.rhs.tag === "ValExpr" && s.rhs.value.tag === "JFunc") {
    const { args, body } = simpleOptFunction({ args: s.rhs.value.args, body: s.rhs.value.body });
    return { ...s, rhs: { tag: "ValExpr", value: { tag: "JFunc", args, body } } };
  }
  if (s.tag === "FuncStat") {
    const { args, body } = simpleOptFunction({ args: s.args, body: s.body });
    return { ...s, args, body };
  }
  return s;
}
