/**
 * Run the compiler with a filesystem we provide instead of node's.
 *
 * GHC's RTS decides it is on node by looking for `global`, `process`,
 * `require` and `module`, then takes `fs`, `path`, `os` and `child_process`
 * from `require` once and keeps them. Handing it those four is the whole
 * trick: the compiler does not know or care where the files really are.
 *
 * The same function serves node (backed by real files, which is how the shim
 * is tested) and the browser (backed by fetched data and a directory the user
 * picked).
 */
import { processConstants } from "./constants.mjs";
import { makeFs, makeOs, makePath } from "./vfs.mjs";

/**
 * @param {object} o
 * @param {string} o.source        the compiler bundle's text
 * @param {import("./vfs.mjs").Vfs} o.vfs
 * @param {string[]} o.argv        libdir, then GHC's flags
 * @param {Record<string,string>} [o.env]
 * @param {(text: string) => void} [o.onOutput]
 * @returns {Promise<number>} the compiler's exit code
 */
export function runCompiler({ source, vfs, argv, env = {}, onOutput = () => {} }) {
  const decoder = new TextDecoder();
  const emit = (chunk) => {
    const text = typeof chunk === "string" ? chunk : decoder.decode(chunk);
    // The scheduler reports the exit sentinel on its way out. See EXIT below.
    if (text.startsWith("uncaught exception in Haskell") && text.trim().endsWith("thread:")) return;
    onOutput(text);
  };

  
  return new Promise((resolve, reject) => {
    let settled = false;
    const finish = (code) => {
      if (!settled) {
        settled = true;
        resolve(code ?? 0);
      }
    };
    // GHC's shutdown calls `process.exit` and expects never to return; on
    // node it does not. Here it has to unwind the scheduler tick it was
    // called from, so `exit` throws this and every callback we hand the RTS
    // swallows it. Without that GHC reports "shutdownHaskellAndExit did not
    // exit" and keeps going, forever.
    // `h$reportMainLoopException` prints whatever reaches the scheduler's
    // catch, our sentinel included; it reads `.toString()`, so this is what
    // the line would say. There is nothing to report about a clean exit.
    const EXIT = { ghcExit: true, toString: () => "" };
    const guard = (f) => (...a) => {
      try {
        return f(...a);
      } catch (e) {
        if (e !== EXIT) throw e;
      }
    };
    const fs = makeFs(vfs, { stdout: emit, stderr: emit, guard });
    const modules = { fs, path: makePath(), os: makeOs(), child_process: { spawn: () => { throw new Error("no subprocesses here"); } } };

    const sandbox = {};
    // GHC links its `unix` bindings expecting a C shim, which
    // `-ddisable-js-c-sources` leaves out. On node these are never reached;
    // here they are, because nothing about this environment looks like a
    // logged-in user on a machine with processors. Nothing here is
    // multi-user, multi-core, or holds a real terminal.
    Object.assign(sandbox, {
      h$geteuid: () => 0,
      h$getegid: () => 0,
      h$sysconf: () => 0,
      h$getpwuid_r: () => 0,
      h$getNumberOfProcessors: () => 1,
      h$setNumCapabilities: () => 0,
      h$fcntl: () => 0,
      h$readlink: () => -1,
      h$pipe: () => -1,
      // Timing and allocation accounting, which -v2 asks for.
      h$stg_getThreadAllocationCounterzh: () => 0,
      h$setHeapSize: () => 0,
      h$enableTimingStats: () => 0,
      h$getOrSetLibHSghcGlobalHasPprDebug: (v) => v,
      h$getOrSetLibHSghcGlobalHasNoDebugOutput: (v) => v,
      h$getOrSetLibHSghcGlobalHasNoStateHack: (v) => v,
      h$getOrSetLibHSghcFastStringTable: (v) => v,
    });
    sandbox.global = sandbox;
    sandbox.globalThis = sandbox;
    sandbox.console = { log: (...a) => emit(`${a.join(" ")}\n`), error: (...a) => emit(`${a.join(" ")}\n`), warn: () => {}, info: () => {} };
    sandbox.process = {
      // The RTS drops argv[0] and argv[1] the way node lays them out.
      argv: ["node", "ghc.cjs", ...argv],
      // GHC reads HOME and TMPDIR; without them it falls back to `getpwuid_r`.
      env: { HOME: "/root", TMPDIR: "/tmp", PATH: "/bin", ...env },
      platform: "linux",
      arch: "x64",
      version: "v20.0.0",
      versions: { node: "20.0.0" },
      cwd: () => vfs.cwd,
      chdir: (d) => { vfs.cwd = vfs.resolve(d); },
      exit: (code) => {
        finish(code);
        throw EXIT;
      },
      on: () => {},
      nextTick: (f, ...a) => queueMicrotask(guard(() => f(...a))),
      hrtime: Object.assign(() => [0, 0], { bigint: () => 0n }),
      cpuUsage: () => ({ user: 0, system: 0 }),
      uptime: () => 0,
      memoryUsage: () => ({ rss: 0, heapTotal: 0, heapUsed: 0, external: 0 }),
      pid: 1,
      // The RTS asks node's private constants table for file modes and errno.
      binding: (what) => {
        if (what === "constants") return processConstants;
        throw new Error(`the playground has no process.binding('${what}')`);
      },
      // The RTS wires stdin's 'end' event and reads `isTTY` off all three.
      stdin: { on: (event, f) => { if (event === "end") queueMicrotask(f); }, isTTY: false, fd: 0 },
      stdout: { write: (c) => (emit(c), true), isTTY: false, fd: 1 },
      stderr: { write: (c) => (emit(c), true), isTTY: false, fd: 2 },
      exitCode: 0,
    };
    sandbox.module = { exports: {} };
    sandbox.exports = sandbox.module.exports;
    sandbox.require = (name) => {
      const m = modules[name.replace(/^node:/, "")];
      if (!m) throw new Error(`the playground has no '${name}'`);
      return m;
    };
    sandbox.setTimeout = (f, ms, ...a) => setTimeout(guard(f), ms, ...a);
    sandbox.clearTimeout = clearTimeout;
    sandbox.setInterval = (f, ms, ...a) => setInterval(guard(f), ms, ...a);
    sandbox.clearInterval = clearInterval;
    sandbox.setImmediate = (f, ...a) => queueMicrotask(guard(() => f(...a)));
    sandbox.clearImmediate = () => {};
    sandbox.queueMicrotask = (f) => queueMicrotask(guard(f));
    sandbox.TextEncoder = TextEncoder;
    sandbox.TextDecoder = TextDecoder;
    // The RTS allocates a read/write staging buffer with `Buffer.alloc`.
    // A browser has no Buffer, and a Uint8Array is all this ever needs.
    sandbox.Buffer = globalThis.Buffer ?? { alloc: (n) => new Uint8Array(n), from: (x) => new Uint8Array(x), isBuffer: (x) => x instanceof Uint8Array };
    sandbox.performance = globalThis.performance;
    sandbox.URL = globalThis.URL;
    sandbox.crypto = globalThis.crypto;

    // A `with` block is what puts the sandbox's names in scope for a script
    // that expects to be a node module. It is exactly what node's own module
    // wrapper does, minus the process isolation.
    const names = Object.keys(sandbox);
    let run;
    try {
      run = new Function(...names, `"use strict";\n${source}\n;return typeof h$main === "function";`);
    } catch (e) {
      return reject(
        new Error(
          `the compiler bundle did not parse as JavaScript (${e.message}). ` +
            "Is assets/ghc.cjs the file build-compiler.mjs wrote? A 404 page served in its place is the usual cause.",
        ),
      );
    }
    try {
      guard(() => run(...names.map((n) => sandbox[n])))();
      // The compiler runs under its own scheduler and keeps going after this
      // returns; `process.exit` from GHC's shutdown is what ends it.
    } catch (e) {
      emit(`${e?.stack ?? e}\n`);
      finish(1);
    }
  });
}
