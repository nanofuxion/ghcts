import { spawn } from "node:child_process";
import { bundledCompiler, findGhcJs } from "./find-ghc.js";

export interface CompileOptions {
  /** GHC flags and source files, exactly as `ghc` takes them. */
  args: readonly string[];
  /** Override the compiler bundle (default: this package's `dist/ghc.js`). */
  ghc?: string;
  /** Override the libdir (default: this package's `dist/lib`). */
  libdir?: string;
  /** Package databases, in order. Becomes `GHC_PACKAGE_PATH`. */
  packageDbs?: readonly string[];
  cwd?: string;
  /** Where the compiler's own output goes. Default: this process's. */
  stdio?: "inherit" | "pipe";
}

export interface CompileResult {
  ok: boolean;
  code: number;
  /** Empty unless `stdio: "pipe"`. */
  stdout: string;
  stderr: string;
}

/**
 * GHC's JavaScript backend runs deeply recursive Haskell on the JS stack.
 * The default node stack overflows partway through a real module.
 */
const STACK_SIZE = 40000;

const resolveCompiler = (o: CompileOptions) => {
  const bundled = bundledCompiler();
  const ghc = o.ghc ?? bundled?.ghc;
  if (!ghc) throw new Error("No compiler bundle. Build one with `node build/build-compiler.mjs`.");
  const libdir = o.libdir ?? bundled?.libdir ?? libdirFromInstall();
  if (!libdir) throw new Error("No libdir. Build one, or pass `libdir`.");
  return { ghc, libdir };
};

const libdirFromInstall = (): string | undefined => findGhcJs()?.libdir;

/**
 * Run the compiler over `args`, the way the `ghcts` command does.
 *
 * `-ddisable-js-c-sources` is passed unless the caller already said something
 * about it: a package's C sources would otherwise be linked by `emcc`, a
 * native toolchain this compiler deliberately does not depend on.
 */
export function compile(options: CompileOptions): Promise<CompileResult> {
  const { ghc, libdir } = resolveCompiler(options);
  const args = [...options.args];
  if (!args.some((a) => a.includes("disable-js-c-sources"))) args.unshift("-ddisable-js-c-sources");

  const env = { ...process.env };
  if (options.packageDbs?.length) env.GHC_PACKAGE_PATH = options.packageDbs.join(":");

  return new Promise((resolvePromise, reject) => {
    const child = spawn(process.execPath, [`--stack-size=${STACK_SIZE}`, ghc, libdir, ...args], {
      cwd: options.cwd,
      env,
      stdio: options.stdio ?? "inherit",
    });
    let stdout = "";
    let stderr = "";
    child.stdout?.on("data", (d) => (stdout += d));
    child.stderr?.on("data", (d) => (stderr += d));
    child.on("error", reject);
    child.on("close", (code) => resolvePromise({ ok: code === 0, code: code ?? 1, stdout, stderr }));
  });
}
