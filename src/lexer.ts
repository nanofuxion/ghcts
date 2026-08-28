import type { Span } from './ast.js';
import { error } from './diagnostics.js';
import type { Diagnostic } from './types.js';
export interface Token { kind: 'ident' | 'int' | 'float' | 'string' | 'char' | 'symbol' | 'newline' | 'eof' | 'quasiquote'; text: string; span: Span; /** Punctuation inserted by the layout phase, never present in source. */ virtual?: true; quoter?: string; }
// Longest tokens must be considered before their prefixes.  This intentionally
// includes the ordinary symbolic identifiers used by Miso's lens API.
const symbols = new Set(['::', '->', '<-', '=>', '+=', '-=', '*=', '/=', '.=', '.~', '%~', '^.', '^?', '?~', '+~', '-~', '%=', '<&>', '<#', '#>', '//~', '==', '/=', '<=', '>=', '&&', '||', '++', '..', '(', ')', '[', ']', '{', '}', ',', ';', '=', '|', '\\', '`', '+', '-', '*', '/', '<', '>', '$', ':', '@', '~', '!', '&', '%', '^', '?', '#', '.']);
export function preprocess(source: string, defines: ReadonlySet<string> = new Set()): string {
  const stack: Array<{ parent: boolean; active: boolean; taken: boolean }> = []; const output: string[] = [];
  const active = () => stack.every(frame => frame.active);
  const evaluate = (kind: string, expression: string) => {
    if (kind === 'ifdef') return defines.has(expression.trim()); if (kind === 'ifndef') return !defines.has(expression.trim());
    // This deliberately supports the portable CPP subset used by Miso's
    // Cabal-selected branches. Numeric compiler-version comparisons are false
    // until a target toolchain supplies that macro.
    const normalized = expression.replace(/defined\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)/g, (_, name: string) => defines.has(name) ? 'true' : 'false').replace(/\b[A-Za-z_][A-Za-z0-9_]*\b/g, name => defines.has(name) ? 'true' : 'false').replace(/\b1\b/g, 'true').replace(/\b0\b/g, 'false');
    try { return /^[\s()!&|<>=truefals]+$/.test(normalized) && Boolean(Function(`return (${normalized.replace(/&&/g, '&&').replace(/\|\|/g, '||')})`)()); } catch { return false; }
  };
  for (const line of source.split('\n')) {
    if (/^\s*#(?:define|undef|include|pragma)\b/.test(line)) { output.push(''); continue; }
    const directive = /^\s*#(ifdef|ifndef|if|elif|else|endif)\b\s*(.*)$/.exec(line);
    if (!directive) { output.push(active() ? line : ''); continue; }
    const [, kind, expression] = directive; const parent = active();
    if (kind === 'if' || kind === 'ifdef' || kind === 'ifndef') { const branch = evaluate(kind, expression); stack.push({ parent, active: parent && branch, taken: branch }); }
    else if (kind === 'elif') { const frame = stack.at(-1); if (frame) { const branch = !frame.taken && evaluate('if', expression); frame.active = frame.parent && branch; frame.taken ||= branch; } }
    else if (kind === 'else') { const frame = stack.at(-1); if (frame) { const branch = !frame.taken; frame.active = frame.parent && branch; frame.taken = true; } }
    else stack.pop();
    output.push('');
  }
  return output.join('\n');
}
export function lex(source: string, file: string, defines: ReadonlySet<string> = new Set()): { tokens: Token[]; diagnostics: Diagnostic[] } {
  source = preprocess(source, defines);
  const tokens: Token[] = []; const diagnostics: Diagnostic[] = []; let index = 0; let line = 1; let column = 1;
  const emit = (kind: Token['kind'], text: string, start: number, startLine: number, startColumn: number) => tokens.push({ kind, text, span: { start, end: index, line: startLine, column: startColumn } });
  while (index < source.length) { const ch = source[index]; const start = index; const startLine = line; const startColumn = column;
    if (ch === ' ' || ch === '\t' || ch === '\r') { index++; column++; continue; }
    if (ch === '\n') { index++; line++; column = 1; emit('newline', '\n', start, startLine, startColumn); continue; }
    if (source.startsWith('--', index)) { while (index < source.length && source[index] !== '\n') { index++; column++; } continue; }
    if (source.startsWith('{-', index)) {
      let depth = 1; index += 2; column += 2;
      while (index < source.length && depth > 0) {
        if (source.startsWith('{-', index)) { depth++; index += 2; column += 2; continue; }
        if (source.startsWith('-}', index)) { depth--; index += 2; column += 2; continue; }
        if (source[index] === '\n') { index++; line++; column = 1; continue; }
        index++; column++;
      }
      if (depth) diagnostics.push(error('E_LEX', 'Unterminated block comment', file, startLine, startColumn));
      continue;
    }
    if (source.startsWith('{-#', index)) { const end = source.indexOf('#-}', index + 3); if (end < 0) { diagnostics.push(error('E_LEX', 'Unterminated pragma', file, line, column)); break; } column += end + 3 - index; index = end + 3; continue; }
    if (/\d/.test(ch)) {
      // `0x1F`, `0o17`, `0b1011` are one token each, and `Number` reads all
      // three prefixes exactly as Haskell writes them. Without this, `0xDBFF`
      // lexes as `0` followed by the identifier `xDBFF`.
      const base = ch === '0' ? /^[xX][0-9A-Fa-f]|^[oO][0-7]|^[bB][01]/.exec(source.slice(index + 1, index + 3)) : null;
      if (base) {
        const digits = /[xX]/.test(base[0]![0]!) ? /[0-9A-Fa-f]/ : /[0-7]/;
        index += 2; column += 2;
        while (index < source.length && digits.test(source[index]!)) { index++; column++; }
        emit('int', source.slice(start, index), start, startLine, startColumn);
        continue;
      }
      while (index < source.length && /\d/.test(source[index])) { index++; column++; }
      // A fraction (and an exponent, which only a fraction may carry here)
      // makes this a *different* literal, not a longer integer: `2.5` must not
      // reach Core as `LitNumInt 2`.
      let fractional = false;
      if (source[index] === '.' && /\d/.test(source[index + 1] ?? '')) {
        fractional = true;
        index++; column++;
        while (index < source.length && /\d/.test(source[index])) { index++; column++; }
      }
      if (fractional && /[eE]/.test(source[index] ?? '')) {
        const after = /[+-]/.test(source[index + 1] ?? '') ? index + 2 : index + 1;
        if (/\d/.test(source[after] ?? '')) {
          column += after - index; index = after;
          while (index < source.length && /\d/.test(source[index])) { index++; column++; }
        }
      }
      emit(fractional ? 'float' : 'int', source.slice(start, index), start, startLine, startColumn);
      continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      while (index < source.length && /[A-Za-z0-9_']/.test(source[index])) {
        index++;
        column++;
      }
      while (source[index] === ".") {
        const next = source[index + 1] ?? "";
        const text = source.slice(start, index);
        const segment = text.slice(text.lastIndexOf(".") + 1);
        if (!/^[A-Z]/.test(segment)) break;
        if (/[A-Za-z_]/.test(next)) {
          index++;
          column++;
          while (index < source.length && /[A-Za-z0-9_']/.test(source[index])) {
            index++;
            column++;
          }
          continue;
        }
        if (/[!#$%&*+/<=>?@\\^|~:-]/.test(next)) {
          index++;
          column++;
        }
        break;
      }
      emit("ident", source.slice(start, index), start, startLine, startColumn);
      continue;
    }
    // Interfaces can export symbolic Unicode names.  Keeping an unknown
    // codepoint as an identifier lets later name resolution issue a useful
    // diagnostic rather than making lexing the first (and noisy) failure.
    if (ch.charCodeAt(0) >= 0x80) { const codepoint = source.codePointAt(index)!; const width = codepoint > 0xffff ? 2 : 1; index += width; column += width; emit('ident', source.slice(start, index), start, startLine, startColumn); continue; }
    if (ch === '"') { index++; column++; let value = ''; let closed = false; while (index < source.length) { const c = source[index++]; column++; if (c === '"') { closed = true; break; } if (c === '\\' && index < source.length) { const escaped = source[index]; if (escaped === 'n') { index++; column++; value += '\n'; } else if (escaped === 't') { index++; column++; value += '\t'; } else if (escaped === 'r') { index++; column++; value += '\r'; } else if (/\d/.test(escaped)) { const digits = index; while (/\d/.test(source[index])) { index++; column++; } value += String.fromCodePoint(Number(source.slice(digits, index))); } else { index++; column++; value += escaped; } } else { if (c === '\n') { line++; column = 1; } value += c; } } if (!closed) diagnostics.push(error('E_LEX', 'Unterminated string literal', file, startLine, startColumn)); else emit('string', value, start, startLine, startColumn); continue; }
    if (ch === "'") {
      // Template Haskell type names (`''Model`) are two ticks, not a character.
      if (source[index + 1] === "'" && /[A-Za-z_]/.test(source[index + 2] ?? '')) {
        index += 2;
        column += 2;
        emit('symbol', "''", start, startLine, startColumn);
        continue;
      }
      // A leading quote promotes a data constructor at the type level
      // (`'Text`, `'Just`); it is not an unterminated character literal.
      if (/[A-Za-z_]/.test(source[index + 1] ?? '') && source[index + 2] !== "'") { index++; column++; emit('symbol', "'", start, startLine, startColumn); continue; }
      index++; column++; let value = ''; if (source[index] === '\\') { index++; column++; const escaped = source[index++]; column++; value = escaped === 'n' ? '\n' : escaped; } else if (index < source.length) { value = source[index++]; column++; } if (source[index] !== "'") diagnostics.push(error('E_LEX', 'Unterminated character literal', file, startLine, startColumn)); else { index++; column++; emit('char', value, start, startLine, startColumn); } continue;
    }
    if (ch === '[') {
      let look = index + 1;
      if (/[A-Za-z_]/.test(source[look] ?? '')) {
        while (look < source.length && /[A-Za-z0-9_']/.test(source[look])) look++;
        if (source[look] === '|') {
          const quoter = source.slice(index + 1, look);
          look++;
          const bodyStart = look;
          while (look < source.length && !(source[look] === '|' && source[look + 1] === ']')) look++;
          if (look >= source.length || source[look] !== '|') {
            diagnostics.push(error('E_LEX', 'Unterminated quasiquote', file, startLine, startColumn));
            break;
          }
          const end = look + 2;
          for (const character of source.slice(start, end)) {
            if (character === '\n') { line++; column = 1; }
            else column++;
          }
          tokens.push({ kind: 'quasiquote', text: source.slice(bodyStart, look), quoter, span: { start, end, line: startLine, column: startColumn } });
          index = end;
          continue;
        }
      }
    }
    const three = source.slice(index, index + 3); const two = source.slice(index, index + 2); let symbol = symbols.has(three) ? three : symbols.has(two) ? two : ch; let arbitraryOperator = false;
    // Haskell permits user-defined sequences of operator characters.  Keep
    // them as one token so declarations such as `(<>~)` and applications do
    // not cascade into unrelated parse errors.
    if (/[!#$%&*+./<=>?@\\^|~:-]/.test(ch)) { let end = index + 1; while (end < source.length && /[!#$%&*+./<=>?@\\^|~:-]/.test(source[end])) end++; const run = source.slice(index, end); if (run.length > symbol.length) { symbol = run; arbitraryOperator = true; } }
    if (symbols.has(symbol) || arbitraryOperator) { index += symbol.length; column += symbol.length; emit('symbol', symbol, start, startLine, startColumn); continue; }
    diagnostics.push(error('E_LEX', `Unexpected character ${JSON.stringify(ch)}`, file, line, column)); index++; column++;
  } tokens.push({ kind: 'eof', text: '', span: { start: index, end: index, line, column } }); return { tokens, diagnostics };
}

/**
 * Insert Haskell's implicit-layout punctuation while retaining original token
 * spans.  The parser can therefore distinguish source braces from virtual
 * braces and give diagnostics at the next physical token.
 */
export function applyLayout(tokens: Token[]): Token[] {
  const result: Token[] = []; const contexts: Array<{ indent: number; explicit: boolean; delimiterDepth: number }> = []; let pending = false; let delimiterDepth = 0;
  const virtual = (text: '{' | '}' | ';', anchor: Token): Token => ({ kind: 'symbol', text, virtual: true, span: { ...anchor.span, end: anchor.span.start } });
  const nextCode = (from: number) => { let index = from; while (tokens[index]?.kind === 'newline') index++; return tokens[index]; };
  // A character or string literal may have text such as `{`, but only source
  // punctuation participates in explicit-brace and delimiter handling.
  const isSymbol = (token: Token, text: string) => token.kind === 'symbol' && token.text === text;
  for (let index = 0; index < tokens.length; index++) {
    const token = tokens[index];
    if (token.kind === 'newline') {
      // A blank run represents one layout boundary.  Looking ahead already
      // finds its first real token, so processing every physical newline
      // would insert the same virtual separator repeatedly.
      if (tokens[index + 1]?.kind === 'newline') continue;
      const next = nextCode(index + 1);
      const context = contexts.at(-1);
      if (next && next.kind !== 'eof' && context && !context.explicit) {
        // Close exactly the blocks whose indentation was left.  The previous
        // implementation reprocessed this newline after every close; that
        // also closed a surrounding block at the *same* indentation.  Nested
        // `let`/`do` in real Miso then escaped their parent `do` block.
        while (contexts.length && !contexts.at(-1)!.explicit && next.span.column < contexts.at(-1)!.indent) {
          contexts.pop();
          result.push(virtual('}', next));
        }
        const parent = contexts.at(-1);
        if (parent && !parent.explicit && next.span.column === parent.indent) {
          // `where` attaches to the declaration that introduced the current
          // layout block; it is not another member of (for example) a `case`
          // alternative list at the same indentation.
          if (next.text === 'where') {
            contexts.pop();
            result.push(virtual('}', next));
          } else if (!['in', 'else', 'then'].includes(next.text)) result.push(virtual(';', next));
        }
      }
      continue;
    }
    if (pending) {
      pending = false;
      if (isSymbol(token, '{')) contexts.push({ indent: 0, explicit: true, delimiterDepth });
      else { contexts.push({ indent: token.span.column, explicit: false, delimiterDepth }); result.push(virtual('{', token)); }
    } else if (isSymbol(token, '{')) {
      contexts.push({ indent: 0, explicit: true, delimiterDepth });
    }
    // An implicit block nested in parentheses/brackets ends before the
    // matching physical delimiter, but a surrounding module block must stay
    // open.  Track delimiter depth to distinguish the two cases.
    if (isSymbol(token, ')') || isSymbol(token, ']')) { const nextDepth = Math.max(0, delimiterDepth - 1); while (contexts.length && !contexts.at(-1)!.explicit && contexts.at(-1)!.delimiterDepth > nextDepth) { contexts.pop(); result.push(virtual('}', token)); } delimiterDepth = nextDepth; }
    if (isSymbol(token, '}')) {
      while (contexts.length && !contexts.at(-1)!.explicit) {
        contexts.pop();
        result.push(virtual('}', token));
      }
      if (contexts.at(-1)?.explicit) contexts.pop();
    }
    result.push(token);
    if (isSymbol(token, '(') || isSymbol(token, '[')) delimiterDepth++;
    if (token.kind === 'ident' && (['where', 'let', 'of', 'do'].includes(token.text) || (token.text === 'case' && result.at(-2)?.text === '\\'))) pending = true;
  }
  const eof = tokens.at(-1)!; while (contexts.length && !contexts.at(-1)!.explicit) { contexts.pop(); result.splice(result.length - 1, 0, virtual('}', eof)); }
  return result;
}
