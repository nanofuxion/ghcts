export type Target = 'browser' | 'node';

export interface GhctsConfig {
  version: 1;
  sourceRoots: string[];
  entry: { module: string; export: string };
  dependencies?: string[];
  targets: Target[];
  outDir: string;
  /** Extra CPP symbols, Cabal-style (`NATIVE` or `-DNATIVE`). */
  cpp?: string[];
  /** Cabal flags to turn on when reading dependencies' `.cabal` files, the
   * equivalent of `-f native`.  A flag not named here takes the package's own
   * `default:`.  Distinct from `cpp`: a flag selects which stanza cabal reads,
   * a CPP symbol selects which lines the preprocessor keeps. */
  flags?: string[];
  /** Runtime code-generation mode. Defaults to the GHC-compatible fast path. */
  optimization?: "none" | "ghc" | "native";
}

export interface Diagnostic {
  severity: 'error' | 'warning';
  message: string;
  file?: string;
  line?: number;
  column?: number;
  code: string;
}

export interface CompileProjectOptions { project: string; emit?: boolean; }
export interface CompileResult {
  diagnostics: Diagnostic[];
  outputPaths: string[];
  config?: GhctsConfig;
  /** Parsed module identity → authoritative source file.  Consumers can use
   * this to audit local/package dependency origins before lowering. */
  moduleOrigins?: Record<string, string>;
}
