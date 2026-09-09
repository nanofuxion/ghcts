/**
 * A C preprocessor, in JavaScript, for the one subprocess GHC insists on.
 *
 * `{-# LANGUAGE CPP #-}` makes GHC hand the file to a real cpp before it
 * parses anything, and a browser has no subprocesses to hand it to. This is
 * what answers instead: conditionals, object- and function-like macros, and
 * `#include`, which is all a Haskell source has ever needed from one.
 *
 * Line numbers are what GHC's error messages are made of, so every directive
 * and every skipped line leaves a blank line where it was, and the output
 * opens with a `# 1 "<file>"` marker naming the real source rather than the
 * temporary file GHC reads back.
 *
 * Identifiers here may end in `'`, so `foo'` is one name and never the macro
 * `foo` with a stray quote after it.
 */

const IDENT = /[A-Za-z_][A-Za-z0-9_']*/y;

/** `NAME`, `NAME value`, or `NAME(a, b) value` - the parenthesis counts only
 * when it touches the name, which is how C tells the two apart. */
export function parseDefine(text) {
  const m = /^([A-Za-z_][A-Za-z0-9_]*)(?:\(([^)]*)\))?\s*([\s\S]*)$/.exec(text.trim());
  if (!m) return undefined;
  const params = m[2] === undefined ? undefined : m[2].trim() ? m[2].split(",").map((s) => s.trim()) : [];
  return [m[1], { params, body: m[3].trim() }];
}

/** The arguments of a function-like use, from the `(` at `at`. */
function readArgs(text, at) {
  const args = [];
  let depth = 0;
  let current = "";
  for (let i = at; i < text.length; i++) {
    const ch = text[i];
    if (ch === "(" && ++depth === 1) continue;
    if (ch === ")" && --depth === 0) return { args: [...args, current], end: i + 1 };
    if (ch === "," && depth === 1) { args.push(current); current = ""; continue; }
    current += ch;
  }
  return { args, end: -1 };
}

/** Replace every macro in `text`, refusing to re-enter one already being
 * expanded, which is what stops `#define x x + 1` from running forever. */
export function expand(text, macros, blocked = new Set()) {
  let out = "";
  let i = 0;
  while (i < text.length) {
    IDENT.lastIndex = i;
    const m = IDENT.exec(text);
    if (!m) { out += text[i++]; continue; }
    const name = m[0];
    i += name.length;
    const macro = macros.get(name);
    if (!macro || blocked.has(name)) { out += name; continue; }
    if (!macro.params) { out += expand(macro.body, macros, new Set([...blocked, name])); continue; }
    let j = i;
    while (j < text.length && /\s/.test(text[j])) j++;
    if (text[j] !== "(") { out += name; continue; }
    const { args, end } = readArgs(text, j);
    if (end === -1) { out += name; continue; }
    i = end;
    const bound = new Map(macro.params.map((p, k) => [p, expand((args[k] ?? "").trim(), macros, blocked)]));
    const body = macro.body.replace(/[A-Za-z_][A-Za-z0-9_']*/g, (id) => (bound.has(id) ? bound.get(id) : id));
    out += expand(body, macros, new Set([...blocked, name]));
  }
  return out;
}

const OPS = ["||", "&&", "==", "!=", "<=", ">=", "<<", ">>", "|", "^", "&", "<", ">", "+", "-", "*", "/", "%", "(", ")", "!", "~"];
const LEVELS = [["||"], ["&&"], ["|"], ["^"], ["&"], ["==", "!="], ["<", ">", "<=", ">="], ["<<", ">>"], ["+", "-"], ["*", "/", "%"]];
const APPLY = {
  "||": (a, b) => (a || b ? 1 : 0), "&&": (a, b) => (a && b ? 1 : 0),
  "|": (a, b) => a | b, "^": (a, b) => a ^ b, "&": (a, b) => a & b,
  "==": (a, b) => (a === b ? 1 : 0), "!=": (a, b) => (a !== b ? 1 : 0),
  "<": (a, b) => (a < b ? 1 : 0), ">": (a, b) => (a > b ? 1 : 0),
  "<=": (a, b) => (a <= b ? 1 : 0), ">=": (a, b) => (a >= b ? 1 : 0),
  "<<": (a, b) => a << b, ">>": (a, b) => a >> b,
  "+": (a, b) => a + b, "-": (a, b) => a - b,
  "*": (a, b) => a * b, "/": (a, b) => (b === 0 ? 0 : Math.trunc(a / b)), "%": (a, b) => (b === 0 ? 0 : a % b),
};

/** Integer arithmetic only, which is all `#if` has. */
export function evalExpr(text) {
  const tokens = [];
  for (let i = 0; i < text.length; ) {
    if (/\s/.test(text[i])) { i++; continue; }
    const num = /^(0[xX][0-9a-fA-F]+|\d+)[uUlL]*/.exec(text.slice(i));
    if (num) { tokens.push(Number(num[1])); i += num[0].length; continue; }
    const op = OPS.find((o) => text.startsWith(o, i));
    if (!op) throw new Error(`cannot read ${JSON.stringify(text.slice(i, i + 20))}`);
    tokens.push(op);
    i += op.length;
  }
  let at = 0;
  const unary = () => {
    const t = tokens[at];
    if (t === "(") { at++; const v = binary(0); if (tokens[at] === ")") at++; return v; }
    if (t === "!") { at++; return unary() ? 0 : 1; }
    if (t === "~") { at++; return ~unary(); }
    if (t === "-") { at++; return -unary(); }
    if (t === "+") { at++; return unary(); }
    if (typeof t !== "number") throw new Error(`unexpected ${t ?? "end of expression"}`);
    at++;
    return t;
  };
  const binary = (level) => {
    if (level >= LEVELS.length) return unary();
    let value = binary(level + 1);
    while (LEVELS[level].includes(tokens[at])) {
      const op = tokens[at++];
      value = APPLY[op](value, binary(level + 1));
    }
    return value;
  };
  const result = binary(0);
  if (at !== tokens.length) throw new Error(`trailing ${tokens[at]}`);
  return result;
}

/**
 * @param {string} source
 * @param {object} o
 * @param {string} o.path                 what the output's line markers name
 * @param {string[]} [o.defines]          `-D` values, as `NAME` or `NAME=body`
 * @param {string[]} [o.includes]         `-include` headers, read for their
 *                                        macros before the source and
 *                                        contributing no lines of their own
 * @param {(name: string) => {path: string, text: string} | undefined} [o.resolveInclude]
 * @returns {{text: string, errors: string[]}}
 */
export function preprocess(source, { path, defines = [], includes = [], resolveInclude = () => undefined }) {
  const macros = new Map();
  for (const d of defines) {
    const [name, macro] = parseDefine(d.replace("=", " ")) ?? [];
    if (name) macros.set(name, macro);
  }

  const out = [];
  const errors = [];
  /** One frame per open `#if`: whether this branch is on, and whether any
   * branch of it has been. */
  const stack = [];
  const live = () => stack.every((f) => f.on);

  const test = (expr) => {
    const withDefined = expr.replace(
      /defined\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)|defined\s+([A-Za-z_][A-Za-z0-9_]*)/g,
      (_, a, b) => (macros.has(a ?? b) ? "1" : "0"),
    );
    // Whatever is still a name after expansion is 0, which is what C says.
    const numbers = expand(withDefined, macros).replace(/[A-Za-z_][A-Za-z0-9_']*/g, "0");
    try {
      return evalExpr(numbers) !== 0;
    } catch (e) {
      errors.push(`${path}: cannot evaluate #if ${expr.trim()}: ${e.message}`);
      return false;
    }
  };

  const run = (text, file, depth) => {
    if (depth > 20) { errors.push(`${file}: #include nested too deeply`); return; }
    const lines = text.split("\n");
    for (let n = 0; n < lines.length; n++) {
      // A directive or a line of code may be continued with a trailing `\`.
      let line = lines[n];
      let eaten = 0;
      while (line.endsWith("\\") && n + eaten + 1 < lines.length) {
        line = `${line.slice(0, -1)} ${lines[n + ++eaten]}`;
      }
      const blanks = () => { for (let k = 0; k <= eaten; k++) out.push(""); };
      const directive = /^\s*#\s*([a-z_]+)\b[ \t]*([\s\S]*)$/.exec(line);
      if (!directive) {
        out.push(live() ? expand(line, macros) : "");
        for (let k = 0; k < eaten; k++) out.push("");
        n += eaten;
        continue;
      }
      const [, what, rest] = directive;
      switch (what) {
        case "if": stack.push({ on: live() && test(rest), taken: false }); stack.at(-1).taken = stack.at(-1).on; break;
        case "ifdef":
        case "ifndef": {
          const has = macros.has(rest.trim().split(/\s/)[0]);
          const on = live() && (what === "ifdef" ? has : !has);
          stack.push({ on, taken: on });
          break;
        }
        case "elif": {
          const f = stack.at(-1);
          if (!f) { errors.push(`${file}:${n + 1}: #elif without #if`); break; }
          f.on = !f.taken && stack.slice(0, -1).every((p) => p.on) && test(rest);
          f.taken ||= f.on;
          break;
        }
        case "else": {
          const f = stack.at(-1);
          if (!f) { errors.push(`${file}:${n + 1}: #else without #if`); break; }
          f.on = !f.taken && stack.slice(0, -1).every((p) => p.on);
          f.taken ||= f.on;
          break;
        }
        case "endif":
          if (!stack.pop()) errors.push(`${file}:${n + 1}: #endif without #if`);
          break;
        case "define":
          if (live()) { const d = parseDefine(rest); if (d) macros.set(d[0], d[1]); }
          break;
        case "undef":
          if (live()) macros.delete(rest.trim().split(/\s/)[0]);
          break;
        case "include": {
          if (!live()) break;
          const m = /^[<"]([^">]*)[>"]/.exec(rest.trim());
          const found = m && resolveInclude(m[1]);
          if (!found) { errors.push(`${file}:${n + 1}: cannot find ${rest.trim()}`); break; }
          blanks();
          run(found.text, found.path, depth + 1);
          // Markers reset the count, so an include never shifts what follows.
          out.push(`# ${n + eaten + 2} "${file}"`);
          n += eaten;
          continue;
        }
        case "error":
          if (live()) errors.push(`${file}:${n + 1}: ${expand(rest, macros).trim()}`);
          break;
        default: // #warning, #line, #pragma and anything else: nothing to do
          break;
      }
      blanks();
      n += eaten;
    }
  };

  for (const name of includes) run(`#include "${name}"`, name, 0);
  out.length = 0; // those headers are here for their macros, not their text
  out.push(`# 1 "${path}"`);
  run(source, path, 0);
  if (stack.length) errors.push(`${path}: ${stack.length} unterminated #if`);
  return { text: `${out.join("\n")}\n`, errors };
}
