import type { Diagnostic } from './types.js';

export const error = (code: string, message: string, file?: string, line?: number, column?: number): Diagnostic =>
  ({ severity: 'error', code, message, file, line, column });

export const formatDiagnostic = (d: Diagnostic): string =>
  `${d.file ?? '<project>'}${d.line ? `:${d.line}:${d.column ?? 1}` : ''}: ${d.severity} ${d.code}: ${d.message}`;
