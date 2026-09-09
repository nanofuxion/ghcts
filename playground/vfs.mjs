/**
 * The filesystem GHC sees when it is not running on node.
 *
 * GHC's JavaScript RTS reaches the outside world through exactly four node
 * modules, taken once at startup from `require`. `fs` is the only one it
 * really uses: 28 functions, listed in `SURFACE` below. Give it those and the
 * compiler runs anywhere, which is what makes a browser playground possible.
 *
 * A `Vfs` is a plain tree of directories and `Uint8Array` files. Files can be
 * *lazy*: a `load()` that returns the bytes on first read. The browser uses
 * that to avoid holding the whole 78 MB of boot libraries in memory, and node
 * uses it to back the tree with real files while testing this shim.
 */

import { processConstants } from "./constants.mjs";

const DIR = 0o040755;
const FILE = 0o100644;

/**
 * Times matter: GHC decides what to recompile by comparing a source's
 * modification time against its interface's. Everything starting at 0 makes
 * every object look up to date, and the link then fails looking for objects
 * nothing ever wrote.
 */
let clock = 1_600_000_000_000;
const now = () => (clock += 1000);

class Node {
  constructor(mode, mtime) {
    this.mode = mode;
    this.mtime = mtime ?? now();
  }
}

class Dir extends Node {
  constructor() {
    super(DIR);
    this.children = new Map();
  }
}

class File extends Node {
  /** @param {Uint8Array | { size: number, load: () => Uint8Array }} content */
  constructor(content, mtime) {
    super(FILE, mtime);
    if (content instanceof Uint8Array) this.bytes = content;
    else this.lazy = content;
  }
  get size() {
    return this.bytes ? this.bytes.length : this.lazy.size;
  }
  read() {
    if (!this.bytes) {
      this.bytes = this.lazy.load();
      this.lazy = undefined;
    }
    return this.bytes;
  }
}

export const touch = now;

const split = (p) => p.split("/").filter((s) => s.length > 0 && s !== ".");

const err = (code, path, syscall) => {
  const e = new Error(`${code}: ${syscall} '${path}'`);
  e.code = code;
  e.errno = { ENOENT: -2, EEXIST: -17, ENOTDIR: -20, EISDIR: -21, ENOTEMPTY: -66 }[code] ?? -1;
  e.path = path;
  e.syscall = syscall;
  return e;
};

export class Vfs {
  constructor() {
    this.rootNode = new Dir();
    this.cwd = "/";
    /** Open file descriptors. 0-2 are stdin/stdout/stderr, never in here. */
    this.fds = new Map();
    this.nextFd = 3;
  }

  resolve(p) {
    const abs = p.startsWith("/") ? p : `${this.cwd}/${p}`;
    const out = [];
    for (const part of split(abs)) {
      if (part === "..") out.pop();
      else out.push(part);
    }
    return `/${out.join("/")}`;
  }

  lookup(p, { parent = false } = {}) {
    const parts = split(this.resolve(p));
    const walk = parent ? parts.slice(0, -1) : parts;
    let node = this.rootNode;
    for (const part of walk) {
      if (!(node instanceof Dir)) return undefined;
      node = node.children.get(part);
      if (!node) return undefined;
    }
    return node;
  }

  mkdirp(p) {
    let node = this.rootNode;
    for (const part of split(this.resolve(p))) {
      let next = node.children.get(part);
      if (!next) {
        next = new Dir();
        node.children.set(part, next);
      }
      node = next;
    }
    return node;
  }

  /** @param {string} p @param {Uint8Array | { size: number, load: () => Uint8Array }} content */
  writeFile(p, content, mtime) {
    const abs = this.resolve(p);
    const dir = this.mkdirp(abs.slice(0, abs.lastIndexOf("/")) || "/");
    dir.children.set(abs.slice(abs.lastIndexOf("/") + 1), new File(content, mtime));
  }

  readFile(p) {
    const node = this.lookup(p);
    if (!(node instanceof File)) throw err("ENOENT", p, "open");
    return node.read();
  }

  statOf(p, syscall) {
    const node = this.lookup(p);
    if (!node) throw err("ENOENT", p, syscall);
    return this.statFrom(node);
  }

  statFrom(node) {
    const dir = node instanceof Dir;
    return {
      dev: 1, ino: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
      mode: node.mode,
      size: dir ? 0 : node.size,
      blksize: 4096,
      blocks: dir ? 0 : Math.ceil(node.size / 512),
      atimeMs: node.mtime, mtimeMs: node.mtime, ctimeMs: node.mtime, birthtimeMs: node.mtime,
      isFile: () => !dir,
      isDirectory: () => dir,
      isSymbolicLink: () => false,
      isBlockDevice: () => false,
      isCharacterDevice: () => false,
      isFIFO: () => false,
      isSocket: () => false,
    };
  }
}

/** A stat for something that is not a file in this filesystem: the pipes GHC
 * makes for its interpreter. `fdType` reads the mode, and `S_IFIFO` is what
 * tells it not to expect seeking. */
const fifoStat = () => ({
  dev: 1, ino: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
  mode: 0o010600,
  size: 0, blksize: 4096, blocks: 0,
  atimeMs: 0, mtimeMs: 0, ctimeMs: 0, birthtimeMs: 0,
  isFile: () => false, isDirectory: () => false, isSymbolicLink: () => false,
  isBlockDevice: () => false, isCharacterDevice: () => false,
  isFIFO: () => true, isSocket: () => false,
});

/**
 * node's `fs`, as much of it as GHC's RTS asks for.
 *
 * `fifos` is anything with `has(fd)`: those fds are pipes handed out by
 * `h$pipe` rather than open files, and stat is the one call that reaches
 * here for them - reads and writes go through the RTS's own fd table.
 */
export function makeFs(vfs, { stdout, stderr, guard = (f) => f, fifos = new Set() } = {}) {
  const write = (fd, chunk) => {
    if (fd === 1) stdout?.(chunk);
    else if (fd === 2) stderr?.(chunk);
    else {
      const open = vfs.fds.get(fd);
      if (!open) throw err("EBADF", String(fd), "write");
      const before = open.node.bytes ?? new Uint8Array(0);
      const at = open.pos;
      const grown = new Uint8Array(Math.max(before.length, at + chunk.length));
      grown.set(before);
      grown.set(chunk, at);
      open.node.bytes = grown;
      open.node.lazy = undefined;
      open.node.mtime = now();
      open.pos = at + chunk.length;
    }
    return chunk.length;
  };

  /**
   * `flags` arrives either as node's string form or, from the RTS, as the
   * numeric `O_*` bitmask. GHC opens its object files the numeric way, so
   * reading only the string form left every write failing with ENOENT.
   */
  const openSync = (p, flags = "r") => {
    const C = fs.constants;
    const numeric = typeof flags === "number";
    const create = numeric ? (flags & C.O_CREAT) !== 0 : /[wa]/.test(flags);
    const truncate = numeric ? (flags & C.O_TRUNC) !== 0 : flags.startsWith("w");
    const append = numeric ? (flags & C.O_APPEND) !== 0 : flags.startsWith("a");

    let node = vfs.lookup(p);
    if (!node && create) {
      vfs.writeFile(p, new Uint8Array(0));
      node = vfs.lookup(p);
    }
    if (!node) throw err("ENOENT", p, "open");
    if (truncate) {
      node.bytes = new Uint8Array(0);
      node.lazy = undefined;
    }
    const fd = vfs.nextFd++;
    vfs.fds.set(fd, { node, pos: append ? node.size : 0, path: vfs.resolve(p) });
    return fd;
  };

  /** Every async call here is answered immediately; nothing actually waits. */
  const async_ = (f) => (...args) => {
    const cb = args.pop();
    try {
      const value = f(...args);
      queueMicrotask(guard(() => cb(null, value)));
    } catch (e) {
      queueMicrotask(guard(() => cb(e)));
    }
  };

  const readSync = (fd, buffer, offset, length, position) => {
    const open = vfs.fds.get(fd);
    if (!open) throw err("EBADF", String(fd), "read");
    const bytes = open.node.read();
    const at = position === null || position === undefined ? open.pos : position;
    const n = Math.max(0, Math.min(length, bytes.length - at));
    buffer.set(bytes.subarray(at, at + n), offset);
    if (position === null || position === undefined) open.pos = at + n;
    return n;
  };

  const fs = {
    // node's own table, captured in constants.mjs. The RTS reads `S_IFMT`
    // and `S_IFREG` out of it to decide what kind of file it is holding.
    constants: processConstants.fs,

    openSync,
    closeSync: (fd) => void vfs.fds.delete(fd),
    readSync,
    writeSync: (fd, buffer, offset = 0, length) => write(fd, buffer.subarray(offset, offset + (length ?? buffer.length - offset))),
    statSync: (p) => vfs.statOf(p, "stat"),
    lstatSync: (p) => vfs.statOf(p, "lstat"),
    mkdirSync: (p) => void vfs.mkdirp(p),
    rmdirSync: (p) => {
      const abs = vfs.resolve(p);
      vfs.lookup(abs, { parent: true })?.children.delete(abs.slice(abs.lastIndexOf("/") + 1));
    },
    unlinkSync: (p) => fs.rmdirSync(p),
    renameSync: (from, to) => {
      const node = vfs.lookup(from);
      if (!node) throw err("ENOENT", from, "rename");
      const abs = vfs.resolve(to);
      vfs.mkdirp(abs.slice(0, abs.lastIndexOf("/")) || "/").children.set(abs.slice(abs.lastIndexOf("/") + 1), node);
      fs.rmdirSync(from);
    },
    realpathSync: (p) => vfs.resolve(p),
    readlinkSync: (p) => {
      throw err("EINVAL", p, "readlink");
    },
    utimesSync: () => {},
    futimesSync: () => {},
    lutimesSync: () => {},
    opendirSync: (p) => {
      const node = vfs.lookup(p);
      if (!(node instanceof Dir)) throw err("ENOTDIR", p, "opendir");
      const entries = [...node.children.entries()].map(([name, child]) => ({
        name,
        isFile: () => child instanceof File,
        isDirectory: () => child instanceof Dir,
        isSymbolicLink: () => false,
      }));
      let i = 0;
      return {
        readSync: () => (i < entries.length ? entries[i++] : null),
        closeSync: () => {},
        close: (cb) => queueMicrotask(guard(() => cb?.(null))),
        read: (cb) => queueMicrotask(guard(() => cb(null, i < entries.length ? entries[i++] : null))),
      };
    },
    readdirSync: (p) => {
      const node = vfs.lookup(p);
      if (!(node instanceof Dir)) throw err("ENOTDIR", p, "readdir");
      return [...node.children.keys()];
    },
    existsSync: (p) => vfs.lookup(p) !== undefined,
    readFileSync: (p) => vfs.readFile(p),
    writeFileSync: (p, data) => vfs.writeFile(p, data instanceof Uint8Array ? data : new TextEncoder().encode(String(data))),
    chmodSync: () => {},
    ftruncateSync: (fd, len = 0) => {
      const open = vfs.fds.get(fd);
      if (open) open.node.bytes = (open.node.bytes ?? new Uint8Array(0)).subarray(0, len);
    },
    fstatSync: (fd) => {
      if (fifos.has(fd)) return fifoStat();
      const open = vfs.fds.get(fd);
      if (!open) throw err("EBADF", String(fd), "fstat");
      return vfs.statFrom(open.node);
    },
    accessSync: (p) => {
      if (!vfs.lookup(p)) throw err("ENOENT", p, "access");
    },
    linkSync: (from, to) => fs.renameSync(from, to),
  };

  for (const name of ["open", "close", "read", "write", "stat", "lstat", "fstat", "access", "chmod", "unlink", "link", "ftruncate", "mkdir", "readdir", "rmdir", "rename", "realpath"]) {
    const sync = fs[`${name}Sync`];
    if (sync) fs[name] = async_(sync);
  }
  // `read` and `write` hand back more than one value, so they do not fit the
  // generic wrapper: node calls back with (err, bytesRead, buffer).
  fs.read = (fd, buffer, offset, length, position, cb) => {
    try {
      const n = readSync(fd, buffer, offset, length, position);
      queueMicrotask(guard(() => cb(null, n, buffer)));
    } catch (e) {
      queueMicrotask(guard(() => cb(e)));
    }
  };
  fs.write = (fd, buffer, offset, length, position, cb) => {
    const done = typeof position === "function" ? position : cb;
    try {
      const n = write(fd, buffer.subarray(offset ?? 0, (offset ?? 0) + (length ?? buffer.length)));
      queueMicrotask(guard(() => done(null, n, buffer)));
    } catch (e) {
      queueMicrotask(guard(() => done(e)));
    }
  };
  return fs;
}

/** node's `path`, enough of it for the RTS. */
export const makePath = () => ({
  sep: "/",
  delimiter: ":",
  join: (...parts) => parts.filter(Boolean).join("/").replace(/\/+/g, "/"),
  resolve: (...parts) => {
    let out = "";
    for (const p of parts) out = p.startsWith("/") ? p : `${out}/${p}`;
    const stack = [];
    for (const part of split(out)) {
      if (part === "..") stack.pop();
      else stack.push(part);
    }
    return `/${stack.join("/")}`;
  },
  dirname: (p) => p.slice(0, p.lastIndexOf("/")) || "/",
  basename: (p) => p.slice(p.lastIndexOf("/") + 1),
  extname: (p) => {
    const b = p.slice(p.lastIndexOf("/") + 1);
    const i = b.lastIndexOf(".");
    return i <= 0 ? "" : b.slice(i);
  },
  isAbsolute: (p) => p.startsWith("/"),
  normalize: (p) => p.replace(/\/+/g, "/"),
});

export const makeOs = () => ({
  tmpdir: () => "/tmp",
  platform: () => "linux",
  arch: () => "javascript",
  EOL: "\n",
  cpus: () => [],
  homedir: () => "/root",
});
