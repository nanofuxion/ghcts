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
import { preprocess } from "./cpp.mjs";
import { makeFs, makeOs, makePath } from "./vfs.mjs";

/** A stream the RTS can read to its end: `read()` once, then EOF. */
function readableOnce(bytes) {
  const listeners = {};
  let sent = false;
  queueMicrotask(() => listeners.end?.());
  return {
    on: (event, f) => { listeners[event] = f; },
    read: () => (sent ? null : ((sent = true), bytes.length ? bytes : null)),
  };
}

/**
 * An in-memory pipe with the shape the RTS reads and writes fds through:
 * `read` takes one of its byte arrays, an offset and a continuation, and
 * `write` takes bytes. Reads that arrive before the data simply wait.
 */
function makePipe() {
  const chunks = [];
  const waiting = [];
  let closed = false;
  let pumping = false;
  const pump = () => {
    if (pumping) return;
    pumping = true;
    // A continuation can read again from inside itself, so the loop has to
    // re-check rather than snapshot.
    while ((waiting.length && chunks.length) || (closed && waiting.length)) {
      const w = waiting.shift();
      if (!chunks.length) { w.c(0); continue; }
      const chunk = chunks[0];
      const n = Math.min(chunk.length, w.n);
      w.buf.u8.set(chunk.subarray(0, n), w.off);
      if (n === chunk.length) chunks.shift();
      else chunks[0] = chunk.subarray(n);
      w.c(n);
    }
    pumping = false;
  };
  return {
    write(bytes) { if (bytes.length) chunks.push(bytes); pump(); },
    read(buf, off, n, c) { waiting.push({ buf, off, n, c }); pump(); },
    close() { closed = true; pump(); },
  };
}

/** The fd pair `h$pipe` hands back, as the RTS's fd table wants them. */
function pipeFds(pipe) {
  return {
    read: { read: (fd, fdo, buf, off, n, c) => pipe.read(buf, off, n, c), close: (fd, fdo, c) => c(0), refs: 1 },
    write: { write: (fd, fdo, buf, off, n, c) => (pipe.write(buf.u8.slice(off, off + n)), c(n)), close: (fd, fdo, c) => c(0), refs: 1 },
  };
}

/**
 * What the compiler needs before it can start an interpreter, prepended to
 * its own bundle because both halves live in there: `h$base_fds` is a local
 * of the scope the bundle runs in, and `h$base_c_fcntl_write` is one of its
 * own functions. Only the queues behind the fds come from outside.
 *
 * The RTS's `fcntl` always fails, and GHC uses it to set close-on-exec on the
 * pipes it makes for the interpreter. Nothing here ever execs, so succeeding
 * is both harmless and what the caller is waiting for.
 */
const INTERP_SHIM = `h$base_c_fcntl_read = function () { return 0; };
h$base_c_fcntl_write = function () { return 0; };
function h$pipe(b, o) {
  var p = h$ghctsNewPipe();
  h$base_fds[p.r] = p.readFd;
  h$base_fds[p.w] = p.writeFd;
  b.i3[o >> 2] = p.r;
  b.i3[(o >> 2) + 1] = p.w;
  return 0;
}
`;

/**
 * A fresh global for the interpreter to live in: same-origin, so we can reach
 * into it, and its own scope, so a second RTS does not land on top of the
 * compiler's.
 *
 * `script` runs a whole file and `value` reads one expression, and they are
 * not the same thing. A file goes in as a real `<script>` rather than through
 * `eval`, because an indirect eval keeps its own `const` bindings to itself -
 * and the RTS declares a good many at the top level for the code loaded after
 * it to read.
 */
function iframeRealm() {
  const frame = document.createElement("iframe");
  frame.style.display = "none";
  document.body.appendChild(frame);
  const scope = frame.contentWindow;
  return {
    scope,
    script: (text) => {
      let failure;
      const onError = (e) => { failure = e.error ?? new Error(e.message); };
      scope.addEventListener("error", onError);
      const el = frame.contentDocument.createElement("script");
      el.textContent = text;
      frame.contentDocument.head.appendChild(el);
      el.remove();
      scope.removeEventListener("error", onError);
      if (failure) throw failure;
    },
    value: (expr) => scope.eval(expr),
    close: () => frame.remove(),
  };
}

/**
 * GHC's JS interpreter, here rather than in a node subprocess.
 *
 * Template Haskell needs somewhere to *run* a splice. GHC's answer for the
 * JavaScript target is `ghc-interp.js`: it starts node on that script, sends
 * it `LOAD <file>` lines to build up an RTS and the GHCi server, then
 * `RUN_SERVER <unit>`, and from there talks the ordinary GHCi protocol over a
 * pair of pipes it made with `pipe(2)`. See Note [The JS interpreter].
 *
 * A page has no processes and no pipes, but it does not need either: the
 * compiler is already JavaScript, so the interpreter can be a second global
 * in the same page and the pipes can be arrays. `args` is what GHC passes -
 * the script, then the fd it expects the interpreter to write on and the fd
 * it expects it to read from.
 */
function startInterpreter({ vfs, args, pipes, emit, guard, newRealm, onRealm }) {
  const [, writeFd, readFd] = args;
  const realm = newRealm();
  onRealm?.(realm);
  const dec = new TextDecoder();
  const load = (path) => realm.script(dec.decode(vfs.readFile(path)));

  const scope = realm.scope;
  const env = nodeEnv({
      vfs,
      argv: ["node", ...args],
      env: {},
      emit,
      guard,
      fifos: pipes,
      // The server exits when GHC is done with it; that is not news.
      exit: () => {},
      // Nothing inside the interpreter starts anything of its own.
      spawn: (cmd) => { throw new Error(`the interpreter cannot run ${cmd}`); },
  });
  // `global` and `globalThis` have to be the realm itself, not the object the
  // rest of these came in on, or code that reaches for one writes somewhere
  // nothing else can see.
  delete env.global;
  delete env.globalThis;
  // A window owns some of these already and will not give them up - `crypto`
  // is a getter with no setter. Those are the ones a realm supplies itself,
  // so leaving its own in place is the right answer anyway.
  for (const [name, value] of Object.entries(env)) {
    try {
      scope[name] = value;
    } catch {
      /* the realm keeps its own */
    }
  }
  scope.global = scope;
  try { scope.globalThis = scope; } catch { /* a realm may already own it */ }
  // ghc-interp.js publishes these two for the loaded code to call back into.
  scope.h$loadJS = (path) => load(path);
  scope.h$lookupClosure = (name) => {
    const found = realm.value(name);
    return found ? scope.h$makeStablePtr(found) : 0;
  };

  /** Wire the interpreter's end of GHC's two pipes into its fd table. The
   * table only exists once the RTS has been loaded, so this waits for it. */
  let wired = false;
  const wire = () => {
    if (wired || !scope.h$base_fds) return;
    wired = true;
    scope.h$base_fds[writeFd] = pipeFds(pipes.get(Number(writeFd))).write;
    scope.h$base_fds[readFd] = pipeFds(pipes.get(Number(readFd))).read;
  };

  // GHC sends `LOAD` and `RUN_SERVER` as lines on the child's stdin.
  let pending = "";
  const command = (line) => {
    if (line.startsWith("LOAD ")) return load(line.slice(5));
    if (line.startsWith("RUN_SERVER ")) {
      wire();
      return scope.h$main(realm.value(`h$${line.slice(11)}ZCGHCiziServerzidefaultServer`));
    }
    throw new Error(`the interpreter got an unknown command: ${line}`);
  };

  const listeners = {};
  return {
    pid: 1,
    stdio: [
      {
        on: () => {},
        write: (bytes, done) => {
          pending += dec.decode(bytes);
          let at;
          while ((at = pending.indexOf("\n")) !== -1) {
            const line = pending.slice(0, at);
            pending = pending.slice(at + 1);
            command(line);
          }
          done?.();
          return true;
        },
        end: () => {},
      },
      readableOnce(new Uint8Array(0)),
      readableOnce(new Uint8Array(0)),
    ],
    on: (event, f) => { listeners[event] = f; },
    // GHC shuts the interpreter down when it is done with it. There is no
    // process to signal, only a realm to stop hearing from.
    kill: () => {
      queueMicrotask(guard(() => listeners.exit?.(0, null)));
      return true;
    },
  };
}

/**
 * The C compiler GHC reaches for, which here is not a process either.
 *
 * With `-E` it is the preprocessor, for a source with `{-# LANGUAGE CPP #-}`
 * in it, and cpp.mjs does that work in JavaScript over this same filesystem.
 * Without it, it is emscripten linking a package's C sources into a
 * `clibs.js` - which `-ddisable-js-c-sources` skips for an ordinary compile,
 * but which GHC asks for unconditionally when it links its interpreter. An
 * empty file leaves that interpreter in exactly the state the compiler
 * itself is already in: the handful of C shims it would have held come from
 * `nodeEnv` instead.
 */
function runCc(vfs, cmd, argv, guard) {
  const dec = new TextDecoder();
  const read = (path) => {
    try {
      return dec.decode(vfs.readFile(path));
    } catch {
      return undefined;
    }
  };
  // A long command line goes into a response file instead, and `@file` means
  // "the arguments are in there" - one per line, quoted and backslash-escaped.
  const responseArgs = (text) => {
    const out = [];
    for (const m of text.matchAll(/"((?:[^"\\]|\\.)*)"|(\S+)/g)) out.push(m[1] === undefined ? m[2] : m[1].replace(/\\(.)/g, "$1"));
    return out;
  };
  const args = argv.flatMap((a) => (a.startsWith("@") ? responseArgs(read(a.slice(1)) ?? "") : [a]));
  const defines = [];
  const dirs = [];
  const preIncludes = [];
  let input;
  let output;
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    const value = (flag) => (a === flag ? args[++i] : a.slice(flag.length));
    if (a.startsWith("-D")) defines.push(value("-D"));
    else if (a.startsWith("-I")) dirs.push(value("-I"));
    else if (a.startsWith("-include")) preIncludes.push(value("-include"));
    else if (a === "-o") output = args[++i];
    else if (a === "-x") i++; // `-x assembler-with-cpp`, the language name
    else if (!a.startsWith("-")) input = a;
  }
  if (!output) throw new Error(`the playground cannot run ${cmd} ${JSON.stringify(args)}`);

  const done = (errors) => {
    const listeners = {};
    queueMicrotask(guard(() => listeners.exit?.(errors.length ? 1 : 0, null)));
    return {
      pid: 1,
      stdio: [{ on: () => {}, write: (_b, c) => (c?.(), true), end: () => {} }, readableOnce(new Uint8Array(0)), readableOnce(new TextEncoder().encode(errors.join("\n")))],
      on: (event, f) => { listeners[event] = f; },
      kill: () => true,
    };
  };

  if (!args.includes("-E")) {
    vfs.writeFile(output, new Uint8Array(0), Date.now());
    return done([]);
  }
  if (!input) throw new Error(`the playground cannot run ${cmd} ${JSON.stringify(args)}`);

  const resolveInclude = (name) => {
    for (const path of name.startsWith("/") ? [name] : [...dirs, "."].map((d) => `${d}/${name}`)) {
      const text = read(path);
      if (text !== undefined) return { path, text };
    }
    return undefined;
  };

  // `-include file` is a `#include` in front of the source, and GHC uses it
  // for the header holding __GLASGOW_HASKELL__ and the MIN_VERSION_* macros.
  const { text, errors } = preprocess(read(input) ?? "", { path: input, defines, includes: preIncludes, resolveInclude });
  if (!errors.length) vfs.writeFile(output, new TextEncoder().encode(text), Date.now());
  return done(errors);
}

/**
 * A `process.stdin` the page can push typed lines into. The RTS reads it with
 * `read()` and comes back for more on a `readable` event, so those two and
 * `end` are the whole stream as far as it is concerned.
 */
export function makeStdin() {
  const chunks = [];
  const listeners = { readable: [], end: [] };
  return {
    isTTY: true,
    fd: 0,
    read: () => chunks.shift() ?? null,
    on: (event, f) => listeners[event]?.push(f),
    /** Hand the program a line someone typed. @param {Uint8Array} bytes */
    write(bytes) {
      chunks.push(bytes);
      for (const f of listeners.readable) f();
    },
    /** No more input is coming. */
    end() {
      for (const f of listeners.end) f();
    },
  };
}

/**
 * Everything GHC's runtime looks for before it decides it is running on node.
 * The compiler gets one of these, and so does the interpreter it starts.
 */
function nodeEnv({ vfs, argv, env, emit, guard, exit, spawn, stdin, fifos, extra = {} }) {
  const fs = makeFs(vfs, { stdout: emit, stderr: emit, guard, fifos });
  const modules = { fs, path: makePath(), os: makeOs(), child_process: { spawn } };
  const sandbox = {
    // GHC links its `unix` bindings expecting a C shim, which
    // `-ddisable-js-c-sources` leaves out. On node these are never reached;
    // here they are, because nothing about this environment looks like a
    // logged-in user on a machine with processors. Nothing here is
    // multi-user, multi-core, or holds a real terminal.
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
    ...extra,
  };
  sandbox.global = sandbox;
  sandbox.globalThis = sandbox;
  sandbox.console = { log: (...a) => emit(`${a.join(" ")}\n`), error: (...a) => emit(`${a.join(" ")}\n`), warn: () => {}, info: () => {} };
  sandbox.process = {
    // The RTS drops argv[0] and argv[1] the way node lays them out.
    argv,
    // GHC reads HOME and TMPDIR; without them it falls back to `getpwuid_r`.
    env: { HOME: "/root", TMPDIR: "/tmp", PATH: "/bin", ...env },
    platform: "linux",
    arch: "x64",
    version: "v20.0.0",
    versions: { node: "20.0.0" },
    cwd: () => vfs.cwd,
    chdir: (d) => { vfs.cwd = vfs.resolve(d); },
    exit,
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
    // `isTTY` is what GHC's handles read to pick their buffering, so a run
    // with a keyboard behind it says yes: block-buffered output would only
    // appear once the program ended, long after it asked for a line.
    stdin: stdin ?? { on: (event, f) => { if (event === "end") queueMicrotask(f); }, isTTY: false, fd: 0 },
    stdout: { write: (c) => (emit(c), true), isTTY: !!stdin, fd: 1 },
    stderr: { write: (c) => (emit(c), true), isTTY: !!stdin, fd: 2 },
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
  return sandbox;
}

/**
 * @param {object} o
 * @param {string} o.source        the compiler bundle's text
 * @param {import("./vfs.mjs").Vfs} o.vfs
 * @param {string[]} o.argv        libdir, then GHC's flags
 * @param {Record<string,string>} [o.env]
 * @param {(text: string) => void} [o.onOutput]
 * @param {object} [o.stdin]       a `makeStdin()` stream; the default is an
 *                                 empty one that reports EOF straight away,
 *                                 which is what the compiler itself wants.
 * @param {() => {scope: object, script: (text: string) => void, value: (expr: string) => any}} [o.newRealm]
 *                                 where Template Haskell's interpreter lives;
 *                                 a hidden same-origin iframe by default.
 * @returns {Promise<number>} the compiler's exit code
 */
export function runCompiler({ source, vfs, argv, env = {}, onOutput = () => {}, stdin, newRealm = iframeRealm }) {
  const decoder = new TextDecoder();
  const emit = (chunk) => {
    const text = typeof chunk === "string" ? chunk : decoder.decode(chunk);
    // The scheduler reports the exit sentinel on its way out. See EXIT below.
    if (text.startsWith("uncaught exception in Haskell") && text.trim().endsWith("thread:")) return;
    onOutput(text);
  };

  return new Promise((resolve, reject) => {
    let settled = false;
    // An interpreter outlives the message that started it, and its own
    // scheduler keeps running; a compile that has finished must not leave one
    // behind for the next one to trip over.
    const realms = [];
    const finish = (code) => {
      if (!settled) {
        settled = true;
        for (const realm of realms) realm.close?.();
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

    /** Both ends of every pipe `h$pipe` has handed out, by fd number, so the
     * interpreter can pick up the ends GHC passed it on its command line. */
    const pipes = new Map();
    // From the filesystem's own counter, so an fd here can never be the same
    // number as one `open` hands out later - the RTS keeps both in one table,
    // and a collision means an open file quietly replaces a pipe.
    const newPipe = () => {
      const pipe = makePipe();
      const r = vfs.nextFd++;
      const w = vfs.nextFd++;
      pipes.set(r, pipe);
      pipes.set(w, pipe);
      const fds = pipeFds(pipe);
      return { r, w, readFd: fds.read, writeFd: fds.write };
    };

    const spawn = (cmd, args) =>
      args[0]?.endsWith("ghc-interp.js")
        ? startInterpreter({ vfs, args, pipes, emit, guard, newRealm, onRealm: (r) => realms.push(r) })
        : runCc(vfs, cmd, args, guard);

    const sandbox = nodeEnv({
      vfs,
      argv: ["node", "ghc.cjs", ...argv],
      env,
      emit,
      guard,
      stdin,
      spawn,
      fifos: pipes,
      exit: (code) => {
        finish(code);
        throw EXIT;
      },
      extra: { h$ghctsNewPipe: newPipe },
    });

    // A `with` block is what puts the sandbox's names in scope for a script
    // that expects to be a node module. It is exactly what node's own module
    // wrapper does, minus the process isolation.
    const names = Object.keys(sandbox);
    let run;
    try {
      run = new Function(...names, `"use strict";\n${INTERP_SHIM}${source}\n;return typeof h$main === "function";`);
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
