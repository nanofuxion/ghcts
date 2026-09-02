#!/usr/bin/env node
/**
 * Run a linked ghcts bundle under a stubbed Lynx host, in node.
 *
 *   node scripts/lynx-run.mjs                     # the counter, both threads
 *   node scripts/lynx-run.mjs --thread mts        # main thread alone
 *   node scripts/lynx-run.mjs --thread bts        # background thread alone
 *   node scripts/lynx-run.mjs --tree              # print the element tree at exit
 *   node scripts/lynx-run.mjs --trace             # log every cross-thread message
 *   node scripts/lynx-run.mjs --tap 3 --tap 3     # tap element #3 twice (uids from --tree)
 *   node scripts/lynx-run.mjs --tap-key bench --bench 20  # tap by data-key, no --tree lookup needed
 *   node scripts/lynx-run.mjs --tap 3 --bench 20   # time 20 taps, one at a time
 *   node scripts/lynx-run.mjs --settle 100         # ms to let each tap finish
 *   node scripts/lynx-run.mjs --count h$someEntry  # how often that entry ran
 *   node scripts/lynx-run.mjs --ms 4000 path/to/all.js
 *
 * `scripts/hs-run.mjs` evaluates one compiled module against the bare RTS. This
 * evaluates a whole *linked* bundle - miso's `js-sources` included - against the
 * host globals Lynx supplies, which is the part of the device a process can
 * honestly stand in for.
 *
 * THE THREADS ARE REAL, THE HOST IS A STUB
 *
 * Lynx runs the app twice, in two JS engines that share no objects: a main
 * thread that owns the element tree (`__MAIN_THREAD__`) and a background thread
 * that owns the model (`__BACKGROUND__`), wired together by one message channel
 * (`lynx.getJSContext()` on the main side, `lynx.getCoreContext()` on the
 * background side). `--thread both` reproduces exactly that: the same bundle in
 * two `node:vm` contexts - separate realms, no shared objects - with the channel
 * bridged between them and delivery deferred a turn, because a cross-engine
 * message can never arrive re-entrantly. The element PAPI is installed only on
 * the main realm, because on the device the background thread does not have it.
 *
 * What that leaves as stub, and how faithful each part is:
 *
 *   - Element PAPI, modelled on plain objects. Everything miso depends on is
 *     reproduced: handle identity, a stable unique id, real parent/child links,
 *     attribute read-back, `__SetConfig` dropping nested objects, and
 *     `__AddEvent(_,_,_,undefined)` being the *removal* primitive. Layout is
 *     not modelled; `__FlushElementTree` only counts.
 *   - A nil handle crashes natively on the device, so every entry point runs
 *     `handle()`, which throws naming the call and the value it got rather than
 *     quietly doing nothing.
 *   - `__CreateElement` is the one stub that returns what a device might not:
 *     the native creator returns nil for a tag with no registered element, and
 *     this cannot know that registry. Every tag created is listed at exit.
 *   - `lynx.fetch`, `lynx.createSelectorQuery` and `lynx.SystemInfo` are left
 *     absent, as they are on a device main thread; miso `typeof`-guards each.
 *     Any `lynx.*` read that found nothing is listed at exit.
 *   - A dispatch nothing listens for is counted and named at exit, never
 *     swallowed and never faked into a reply.
 */
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { createContext, runInContext } from "node:vm";

const traceStart = Date.now();
const options = { ms: 3000, tree: false, trace: false, thread: "both", bundle: "references/miso-lynx/examples/dist/jsexe/all.js" };
const taps = [];
/** `--swipe <uid>`: a leftward drag across the element, as a finger would. */
const swipes = [];
/** `--peek <h$symbol>`: print the closure at exit - its entry, type and first field - in each realm. */
const peeks = [];
/** `--trace-fn <h$name>`: log every call of that global function, with its result. */
const traceFns = [];
/** `--hs-prof`: sample the Haskell stack once per 1000 closure entries and
 * print, at exit, which bindings the time after the first gesture sat under. */
const hsProf = { on: false, armed: false, samples: 0, inclusive: new Map(), self: new Map(), allocs: new Map(), owner: new Map(), papSites: new Map() };
const tapKeys = [];
for (const argv = process.argv.slice(2); argv.length; ) {
  const arg = argv.shift();
  if (arg === "--tree") options.tree = true;
  else if (arg === "--tap") taps.push(Number(argv.shift()));
  else if (arg === "--swipe") swipes.push(Number(argv.shift()));
  else if (arg === "--peek") peeks.push(argv.shift());
  else if (arg === "--hs-prof") hsProf.on = true;
  else if (arg === "--trace-fn") traceFns.push(argv.shift());
  else if (arg === "--tap-key") tapKeys.push(argv.shift());
  else if (arg === "--ms") options.ms = Number(argv.shift());
  else if (arg === "--thread") options.thread = argv.shift();
  else if (arg === "--trace") options.trace = true;
  else if (arg === "--bench") options.bench = Number(argv.shift());
  else if (arg === "--settle") options.settle = Number(argv.shift());
  else if (arg === "--count") (options.count ??= []).push(argv.shift());
  else options.bundle = arg;
}
if (!["mts", "bts", "both"].includes(options.thread)) throw new Error(`--thread: expected mts, bts or both`);
let source = readFileSync(resolve(options.bundle), "utf8");
if (hsProf.on) {
  const loop = "while(c !== h$reschedule && ++count < 1000) {";
  if (!source.includes(loop)) throw new Error("--hs-prof: scheduler loop not found");
  source = source.replace(loop, `h$$$$hsProf(c); ${loop}`);
}

// ---------------------------------------------------------------- element model

let nextUid = 1;
const tagsCreated = new Set();
const handles = new WeakSet();
const element = (tag) => {
  tagsCreated.add(tag);
  const node = {
    uid: nextUid++,
    tag,
    config: {},
    attrs: {},
    classes: [],
    style: "",
    inline: [],
    children: [],
    parent: null,
    // `type:name` -> the `{ type: 'worklet', value }` the engine would call back.
    events: new Map(),
  };
  handles.add(node);
  return node;
};

const describe = (v) => {
  if (v === null || v === undefined) return String(v);
  if (typeof v === "object") return `${v.constructor?.name ?? "object"} ${JSON.stringify(Object.keys(v))}`.slice(0, 80);
  return `${typeof v} ${JSON.stringify(v)}`.slice(0, 80);
};

/** Every PAPI argument that must be an element handle goes through here.
 *
 * The device does not tolerate a nil handle - `__SetCSSId([nil], 0)` takes the
 * app down inside `NSArray insertObject:atIndex:` - so a stub that shrugged at
 * `undefined` would hide the very class of bug worth finding. */
const handle = (node, call, position) => {
  if (node === null || typeof node !== "object" || typeof node?.uid !== "number")
    throw new TypeError(`${call}: argument ${position} is not a Lynx element handle, got ${describe(node)}`);
  return node;
};

const detach = (node) => {
  const parent = node.parent;
  if (!parent) return;
  const i = parent.children.indexOf(node);
  if (i >= 0) parent.children.splice(i, 1);
  node.parent = null;
};

let flushes = 0;

function installElementApi(target) {
  Object.assign(target, {
    __CreatePage: () => element("page"),
    __CreateView: () => element("view"),
    __CreateScrollView: () => element("scroll-view"),
    __CreateText: () => element("text"),
    __CreateImage: () => element("image"),
    __CreateFrame: () => element("frame"),
    __CreateElement: (tag) => element(tag),
    __CreateRawText: (text) => Object.assign(element("raw-text"), { attrs: { text } }),
    __CreateList: (_pageId, componentAtIndex, enqueueComponent) =>
      Object.assign(element("list"), { list: { componentAtIndex, enqueueComponent } }),

    __GetElementUniqueID: (n) => handle(n, "__GetElementUniqueID", 0).uid,
    __ElementIsEqual: (a, b) => handle(a, "__ElementIsEqual", 0) === handle(b, "__ElementIsEqual", 1),
    __SetCSSId: (nodes, id) => {
      if (!Array.isArray(nodes)) throw new TypeError(`__SetCSSId: argument 0 must be an array, got ${describe(nodes)}`);
      for (const n of nodes) handle(n, "__SetCSSId", 0).cssId = id;
    },

    /* Config round-trips flat scalars and drops nested objects - the engine
     * quirk that forced miso's main-thread event registry out of config and
     * into a Map (ts/miso/native/mts/context.ts:41-52). Reproduced, because a
     * stub that stored objects would make that failure mode invisible. */
    __SetConfig: (n, cfg) => {
      const config = handle(n, "__SetConfig", 0).config;
      for (const [k, v] of Object.entries(cfg ?? {})) if (v === null || typeof v !== "object") config[k] = v;
    },
    __GetConfig: (n) => handle(n, "__GetConfig", 0).config,

    __AppendElement: (p, c) => {
      handle(p, "__AppendElement", 0);
      detach(handle(c, "__AppendElement", 1));
      p.children.push(c);
      c.parent = p;
      return c;
    },
    __RemoveElement: (p, c) => {
      handle(p, "__RemoveElement", 0);
      detach(handle(c, "__RemoveElement", 1));
      return c;
    },
    __InsertElementBefore: (p, c, ref) => {
      handle(p, "__InsertElementBefore", 0);
      detach(handle(c, "__InsertElementBefore", 1));
      const at = ref === null || ref === undefined ? -1 : p.children.indexOf(handle(ref, "__InsertElementBefore", 2));
      if (at < 0) p.children.push(c);
      else p.children.splice(at, 0, c);
      c.parent = p;
      return c;
    },
    __ReplaceElements: (p, inserted, removed) => {
      handle(p, "__ReplaceElements", 0);
      const at = removed.length ? p.children.indexOf(handle(removed[0], "__ReplaceElements", 2)) : -1;
      for (const o of removed) detach(handle(o, "__ReplaceElements", 2));
      const index = at < 0 ? p.children.length : at;
      for (const [k, n] of inserted.entries()) {
        detach(handle(n, "__ReplaceElements", 1));
        p.children.splice(index + k, 0, n);
        n.parent = p;
      }
    },
    __SwapElement: (a, b) => {
      handle(a, "__SwapElement", 0);
      handle(b, "__SwapElement", 1);
      const [pa, pb] = [a.parent, b.parent];
      const [ia, ib] = [pa ? pa.children.indexOf(a) : -1, pb ? pb.children.indexOf(b) : -1];
      if (ia >= 0) pa.children[ia] = b;
      if (ib >= 0) pb.children[ib] = a;
      a.parent = pb;
      b.parent = pa;
    },
    __FirstElement: (n) => handle(n, "__FirstElement", 0).children[0] ?? null,
    __NextElement: (n) => {
      const p = handle(n, "__NextElement", 0).parent;
      return p ? (p.children[p.children.indexOf(n) + 1] ?? null) : null;
    },
    __GetParent: (n) => handle(n, "__GetParent", 0).parent,

    __SetAttribute: (n, key, value) => {
      // Only a lepus-empty value removes; an empty string is a stored value.
      const attrs = handle(n, "__SetAttribute", 0).attrs;
      if (value === null || value === undefined) delete attrs[key];
      else attrs[key] = value;
    },
    __GetAttributeByName: (n, key) => handle(n, "__GetAttributeByName", 0).attrs[key] ?? null,
    __SetID: (n, value) => {
      handle(n, "__SetID", 0).attrs.id = value;
    },
    __SetInlineStyles: (n, css) => {
      handle(n, "__SetInlineStyles", 0).style = css;
    },
    __AddInlineStyle: (n, name, value) => {
      handle(n, "__AddInlineStyle", 0).inline.push([name, value]);
    },
    __AddClass: (n, name) => {
      const classes = handle(n, "__AddClass", 0).classes;
      if (!classes.includes(name)) classes.push(name);
    },
    __GetClasses: (n) => handle(n, "__GetClasses", 0).classes.slice(),
    __SetClasses: (n, names) => {
      handle(n, "__SetClasses", 0).classes = names ? String(names).split(/\s+/).filter(Boolean) : [];
    },

    /* `__AddEvent(node, type, name, undefined)` is Lynx's *removal* path -
     * there is no `__RemoveEvent` - so an undefined worklet must unbind. */
    __AddEvent: (n, type, name, worklet) => {
      const events = handle(n, "__AddEvent", 0).events;
      if (worklet === null || worklet === undefined) events.delete(`${type}:${name}`);
      else events.set(`${type}:${name}`, worklet);
    },

    __FlushElementTree: () => {
      flushes++;
    },
  });
}

// -------------------------------------------------------------- the two engines

/** One message channel, both ends. A listener belongs to the realm that
 * registered it, and a dispatch only ever reaches the *other* realm: MTS and
 * BTS both listen and dispatch `Miso.components`, so self-delivery would invent
 * a conversation the device never has. */
const wires = [];
const unheard = new Map();

/** What survives the crossing.
 *
 * The two engines share no heap: Lynx serializes a `dispatchEvent` payload into
 * lepus values, so functions do not travel and a native element handle - which
 * is a pointer into the main engine - cannot travel either. miso's BTS agrees:
 * its `getTarget` returns `{ nodeId: 0 }` and it routes off the `stack` the MTS
 * shipped, never off the event's target. Passing objects by reference instead
 * would hand the background thread a live element it can never have on a
 * device, which is a false-lead machine. A cycle is a payload the engine's own
 * serializer would reject, so it throws. */
const wire = (value, seen = new Set()) => {
  if (value === null || typeof value === "function") return null;
  if (typeof value !== "object") return value;
  if (handles.has(value)) return null;
  if (seen.has(value)) throw new TypeError("ContextProxy.dispatchEvent: payload is cyclic and cannot be serialized");
  seen.add(value);
  const copy = Array.isArray(value)
    ? value.map((v) => wire(v, seen))
    : Object.fromEntries(Object.entries(value).map(([k, v]) => [k, wire(v, seen)]));
  seen.delete(value);
  return copy;
};

// Lynx serializes event payload data across realms, but the receiving realm
// supplies the native event methods. Functions themselves never cross the
// boundary; restoring only these two known methods models that contract.
const restoreEventMethods = (value) => {
  if (!value || typeof value !== "object") return value;
  if (value.type !== undefined && value.preventDefault === null)
    value.preventDefault = () => {};
  if (value.type !== undefined && value.stopPropagation === null)
    value.stopPropagation = () => {};
  for (const child of Object.values(value)) restoreEventMethods(child);
  return value;
};

const dispatch = (from, message) => {
  // The engine's own check, which the device reported as "ContextProxy's
  // dispatchEvent failed, since arg0 must be object!".
  if (message === null || typeof message !== "object")
    throw new TypeError(`ContextProxy.dispatchEvent: arg0 must be an object, got ${describe(message)}`);
  const bound = wires.filter((w) => w.protocol === message.type && w.realm !== from);
  const data = restoreEventMethods(wire(message.data));
  if (options.trace) console.log(`[+${(Date.now() - traceStart).toString().padStart(5)}ms ${from} -> ${message.type} x${bound.length}] ${JSON.stringify(data).slice(0, 300)}`);
  if (bound.length === 0) {
    unheard.set(message.type, (unheard.get(message.type) ?? 0) + 1);
    return;
  }
  // A cross-engine message goes through the other engine's task queue, so it
  // can never arrive re-entrantly. Deliver a turn later.
  for (const w of bound)
    setImmediate(() => timed(() => w.callback({ type: message.type, data })));
};

/** Wall clock is dominated by the harness's own task turns, so what is timed
 * is the time spent *inside* the guest bundle: the worklet the engine runs on
 * a tap, and every cross-thread callback that tap sets off. That number is the
 * app's own cost, and it is what `--bench` compares between two compilers'
 * output for the same program. */
let guestNs = 0n;
const timed = (fn) => {
  const t0 = process.hrtime.bigint();
  try {
    return fn();
  } finally {
    guestNs += process.hrtime.bigint() - t0;
  }
};

const counters = Object.create(null);

const lynxReads = new Set();

function makeRealm(name) {
  const main = name === "mts";
  const context = {
    console,
    setTimeout,
    clearTimeout,
    setInterval,
    clearInterval,
    setImmediate,
    clearImmediate,
    queueMicrotask,
    process,
    // Miso's JS FFI calls the browser-global APIs directly, rather than
    // routing them through `lynx`.
    requestAnimationFrame: (cb) => setTimeout(() => cb(Date.now()), 16),
    cancelAnimationFrame: (id) => clearTimeout(id),
    __MAIN_THREAD__: main,
    __BACKGROUND__: !main,
    // misogram's asset module supplies this registry in rspeedy. The generic
    // stub has no embedded image pack, so return the requested key as a stable
    // placeholder instead of turning a host omission into an app crash.
    __misoGramAssets: new Proxy({}, { get: (_target, key) => typeof key === "string" ? key : undefined }),
  };
  context.globalThis = context;
  if (main) installElementApi(context);

  const proxy = {
    addEventListener: (protocol, callback) => wires.push({ realm: name, protocol, callback }),
    dispatchEvent: (message) => dispatch(name, message),
  };
  const host = {
    // Both names exist on both engines; miso uses getJSContext from the main
    // thread and getCoreContext from the background thread, and they are the
    // two ends of this one channel.
    getJSContext: () => proxy,
    getCoreContext: () => proxy,
    // `lynx.getJSModule("GlobalEventEmitter")`: misogram subscribes to
    // keyboard status on it at startup. Without it the call threw inside the
    // Haskell thread that goes on to handle every event, so no tap ever
    // reached `update` here and every bench measured nothing.
    getJSModule: (name) => ({ name, addListener() {}, removeListener() {}, emit() {}, toggle() {}, trigger() {} }),
    // What LynxExplorer 3.9 on a Pixel 4 XL reports, minus `osVersion`, which
    // that engine omits. misogram's swiper reads `pixelWidth / pixelRatio` as
    // its page width, so without this every swipe computes a zero offset.
    SystemInfo: { pixelWidth: 1440, pixelHeight: 3040, pixelRatio: 3.5, platform: "Android", lynxSdkVersion: "3.9", engineVersion: "3.9", runtimeType: "quickjs" },
    reportError: (e) => console.log(`[${name} lynx.reportError] ${e && e.message ? e.message : e}`),
    requestAnimationFrame: (cb) => setTimeout(() => cb(Date.now()), 16),
    cancelAnimationFrame: (id) => clearTimeout(id),
    setInterval: (cb, ms) => setInterval(cb, ms),
    clearInterval: (id) => clearInterval(id),
  };
  context.lynx = new Proxy(host, {
    get: (target, key) => {
      if (typeof key === "string" && !(key in target)) lynxReads.add(`${name}.${key}`);
      return target[key];
    },
  });
  createContext(context);
  return context;
}

const realms = options.thread === "both" ? ["mts", "bts"] : [options.thread];
const contexts = new Map(realms.map((name) => [name, makeRealm(name)]));
const mts = contexts.get("mts");
for (const [name, context] of contexts) {
  // A linker-local `h$$Mod_NNN` is a continuation frame pushed by some other
  // closure's code; the first function whose body mentions it is taken as
  // its owner, followed up the chain until a named top-level binding.
  const ownerOf = new Map();
  if (hsProf.on) {
    const parts = source.split(/^function (h\$\$?[\w$]+)\(/m);
    for (let i = 1; i < parts.length; i += 2) {
      const fn = parts[i], body = parts[i + 1] ?? "";
      for (const m of body.matchAll(/h\$\$[\w$]+/g)) if (m[0] !== fn && !ownerOf.has(m[0])) ownerOf.set(m[0], fn);
    }
  }
  const resolveOwner = (n) => {
    for (let i = 0; i < 20 && n.startsWith("h$$"); i++) { const o = ownerOf.get(n); if (!o) break; n = o; }
    return n;
  };
  context.h$$hsProf = (c) => {
    if (!hsProf.armed) return;
    hsProf.samples++;
    const self = c?.name || "?";
    hsProf.self.set(self, (hsProf.self.get(self) ?? 0) + 1);
    const seen = new Set([self]);
    const stack = context.h$stack, sp = context.h$sp;
    // The nearest named top-level binding: a `t_e_u_`/`lam_e_u_` local, an
    // `h$$…_NNN` linker-local or an RTS frame is charged to whoever called it.
    const named = (n) => /Z[CD]/.test(n) && !/^h\$(ap|pap|upd|bh|e|rs|p\d|pp\d|catch|return|restore|run|done|sel|unbox|stackFrame|dumpRes|maskFrame|unmaskFrame|reportStackTrace)/.test(n);
    const resolve = resolveOwner;
    let owner = named(self) ? resolve(self) : "";
    for (let k = sp; k >= 0 && k > sp - 400; k--) {
      const f = stack?.[k];
      if (typeof f === "function" && f.name) { seen.add(f.name); if (!owner && named(f.name)) owner = resolve(f.name); }
    }
    owner ||= "(none)";
    hsProf.owner.set(owner, (hsProf.owner.get(owner) ?? 0) + 1);
    for (const n of seen) hsProf.inclusive.set(n, (hsProf.inclusive.get(n) ?? 0) + 1);
  };
  runInContext(source, context, { filename: `${name}:${options.bundle}` });
  if (hsProf.on)
    for (const k of Object.keys(context).filter((k) => /^h\$c(\d+)?$/.test(k))) {
      const orig = context[k];
      context[k] = function (f, ...rest) {
        if (hsProf.armed) {
          const n = f?.name || "?";
          hsProf.allocs.set(n, (hsProf.allocs.get(n) ?? 0) + 1);
          if (n.startsWith("h$pap")) {
            // A partial application is built by the generic apply on behalf
            // of whatever pushed the frame on top of the stack: charge it there.
            let site = "(none)";
            for (let k = context.h$sp; k >= 0 && k > context.h$sp - 60; k--) { const g = context.h$stack?.[k]; if (typeof g === "function" && g.name && /Z[CD]/.test(g.name)) { site = resolveOwner(g.name); break; } }
            hsProf.papSites.set(site, (hsProf.papSites.get(site) ?? 0) + 1);
          }
        }
        return orig.call(this, f, ...rest);
      };
    }
  for (const fn of traceFns) {
    const orig = context[fn];
    if (typeof orig !== "function") { console.log(`--trace-fn ${fn}: not a function in ${name}`); continue; }
    context[fn] = function (...args) {
      const r = orig.apply(this, args);
      const shape = (x, d = 0) => x && typeof x === "object" ? `<${x.f ? x.f.name + "/t" + x.f.t : "obj"}${d < 3 ? ` d1=${shape(x.d1, d + 1)} d2=${shape(x.d2, d + 1)}` : ""}>` : String(x);
      const frames = process.env.LYNX_RUN_TRACE_STACK && r === process.env.LYNX_RUN_TRACE_STACK
        ? "  stack=" + [0, 1, 2, 3, 4, 5, 6].map((k) => { const f = context.h$stack?.[context.h$sp - k]; return typeof f === "function" ? f.name : ""; }).filter(Boolean).join(" < ")
        : "";
      console.log(`[${name} ${fn}] -> ${JSON.stringify(typeof r === "string" ? r : String(r)).slice(0, 100)}${r === "" ? `  arg0=${shape(args[0])}` : ""}${frames}`);
      return r;
    };
  }
  // Each Lynx JS engine evaluates the bundle's RTS static initializers. The
  // MTS path also reaches this through renderPage, but the BTS has no page
  // callback, so initialize it explicitly before its scheduled main runs.
  context.h$runInitStatic?.();
  // `--count h$someEntry` wraps a compiled entry point so a run reports how
  // many times it was entered. Reading a hot symbol's call count is how a
  // profile's self-time is turned into "which Haskell function, how often".
  for (const nm of options.count ?? []) {
    const f = context[nm];
    if (typeof f !== "function") continue;
    counters[nm] ??= 0;
    context[nm] = function () {
      counters[nm]++;
      return f.apply(this, arguments);
    };
    context[nm].a = f.a;
    for (const k of Object.keys(f)) context[nm][k] = f[k];
  }
  // Lynx calls renderPage when the main-thread template loads, before the app
  // gets a turn of its own; `h$main` only schedules, so this still lands first.
  if (name === "mts") {
    if (typeof context.renderPage !== "function")
      throw new Error(`${options.bundle}: no renderPage - miso's js-sources did not link`);
    context.renderPage();
  }
}

// ------------------------------------------------------------------- the report

const walk = (node, into) => {
  into.push(node);
  for (const c of node.children) walk(c, into);
  return into;
};
const render = (node, depth = 0) => {
  const bits = [`${node.tag}#${node.uid}`];
  for (const [k, v] of Object.entries(node.attrs)) bits.push(`${k}=${JSON.stringify(v)}`);
  if (node.classes?.length) bits.push(`class=${JSON.stringify(node.classes.join(" "))}`);
  if (node.events.size) bits.push(`on:${[...node.events.keys()].join(",")}`);
  return ["  ".repeat(depth) + `<${bits.join(" ")}>`, ...node.children.map((c) => render(c, depth + 1))].join("\n");
};

/** Resolve a uid to the element and the ancestor the engine would deliver its
 * tap to. */
function tapTarget(all, uid) {
  const target = all.find((n) => n.uid === uid);
  if (!target) throw new Error(`--tap ${uid}: no such element (run with --tree for the uids)`);
  let mount = target;
  while (mount && !mount.events.has("catchEvent:tap")) mount = mount.parent;
  if (!mount) throw new Error(`--tap ${uid}: no catchEvent:tap listener between it and the root`);
  return { target, mount };
}

/** Same resolution, but by `data-key` instead of a uid read off `--tree`
 * first. A benchmark app's own element is the one thing that does not move
 * between a ghcts build and a GHC one, so naming it this way is what lets a
 * driver script run the same `--tap-key` against both without a human in the
 * loop reading a tree dump to find the uid each time. */
function tapTargetByKey(all, key) {
  const target = all.find((n) => n.attrs["data-key"] === key);
  if (!target) throw new Error(`--tap-key ${key}: no element with that data-key (run with --tree to check)`);
  return tapTarget(all, target.uid);
}

const fireTap = ({ target, mount }) =>
  timed(() =>
    mts.runWorklet(mount.events.get("catchEvent:tap").value, {
      type: "tap",
      target: { elementRefptr: target },
      detail: {},
      preventDefault() {},
      stopPropagation() {},
    }),
  );

/** A finger dragged left across `target`: touchstart, ten touchmoves, touchend,
 * each delivered to the nearest ancestor holding that `catchEvent:` listener
 * with Lynx's `changedTouches` shape. Coordinates are Lynx px on the stub's
 * `SystemInfo`, so a drag of most of the width crosses a page. */
const fireSwipe = (all, uid) => {
  const target = all.find((n) => n.uid === uid);
  if (!target) throw new Error(`--swipe ${uid}: no such element (run with --tree for the uids)`);
  hsProf.armed = true;
  const listener = (kind) => {
    let mount = target;
    while (mount && !mount.events.has(`catchEvent:${kind}`)) mount = mount.parent;
    if (!mount) throw new Error(`--swipe ${uid}: no catchEvent:${kind} listener between it and the root`);
    return mount.events.get(`catchEvent:${kind}`).value;
  };
  const touch = (kind, x, y) => {
    const t = { identifier: 1, x, y, pageX: x, pageY: y, clientX: x, clientY: y };
    timed(() => mts.runWorklet(listener(kind), {
      type: kind,
      target: { elementRefptr: target },
      detail: {},
      changedTouches: [t],
      touches: kind === "touchend" ? [] : [t],
      preventDefault() {},
      stopPropagation() {},
    }));
  };
  const width = 1440 / 3.5;
  const y = 300;
  const frame = () => new Promise((r) => setTimeout(r, 16));
  return (async () => {
    touch("touchstart", width * 0.85, y);
    for (let i = 1; i <= 10; i++) { await frame(); touch("touchmove", width * 0.85 - (width * 0.7 * i) / 10, y); }
    await frame();
    touch("touchend", width * 0.15, y);
  })();
};

/** Let every queued cross-thread message and timer run before the next tap, so
 * each one is measured on its own rather than batched with its neighbours. */
const settle = () => new Promise((r) => setTimeout(r, options.settle ?? 25));

const hsProfReport = () => {
  if (hsProf.on) {
    const top = (m, n) => [...m].sort((a, b) => b[1] - a[1]).slice(0, n);
    console.log(`\nhs-prof: ${hsProf.samples} samples after the first gesture (one per 1000 closure entries)`);
    console.log("inclusive (samples with the binding on the stack):");
    for (const [k, v] of top(hsProf.inclusive, 45)) console.log(`${String((100 * v / hsProf.samples).toFixed(1)).padStart(6)}%  ${k}`);
    const allocTotal = [...hsProf.allocs.values()].reduce((a, b) => a + b, 0);
  console.log(`allocations after the first gesture: ${allocTotal} (h$cN calls; top entries):`);
  for (const [k, v] of top(hsProf.allocs, 40)) console.log(`${String(v).padStart(8)}  ${k}`);
  console.log("partial applications, by the binding whose frame was on top:");
  for (const [k, v] of top(hsProf.papSites, 25)) console.log(`${String(v).padStart(8)}  ${k}`);
  console.log("owner (nearest named binding on the stack):");
  for (const [k, v] of top(hsProf.owner, 40)) console.log(`${String((100 * v / hsProf.samples).toFixed(1)).padStart(6)}%  ${k}`);
  console.log("self (closure being entered):");
    for (const [k, v] of top(hsProf.self, 25)) console.log(`${String((100 * v / hsProf.samples).toFixed(1)).padStart(6)}%  ${k}`);
  }
};

setTimeout(async () => {
  const root = mts?.page;
  const all = root ? walk(root, []) : [];

  if (options.bench) {
    if (taps.length + tapKeys.length !== 1) throw new Error("--bench needs exactly one --tap <uid> or --tap-key <name>");
    const where = tapKeys.length ? tapTargetByKey(all, tapKeys[0]) : tapTarget(all, taps[0]);
    await settle();
    const from = guestNs;
    for (let i = 0; i < options.bench; i++) {
      hsProf.armed = true;
    fireTap(where);
      await settle();
    }
    const ms = Number(guestNs - from) / 1e6;
    console.log(
      `bench taps=${options.bench} guest=${ms.toFixed(1)}ms per-tap=${(ms / options.bench).toFixed(2)}ms` +
        `  elements ${all.length}  flushes ${flushes}`,
    );
    for (const [k, v] of Object.entries(counters)) console.log(`count ${k} ${v}`);
    if (options.tree && root) console.log(`\n${render(root)}`);
    hsProfReport();
    process.exit(0);
  }

  // The engine delivers a tap to the nearest ancestor holding a `catchEvent:tap`
  // listener, with the tapped element as `target.elementRefptr`, and runs the
  // stored worklet through the app's own `runWorklet`. Nothing else is faked.
  for (const uid of taps) {
    const where = tapTarget(all, uid);
    console.log(`\n-- tap <${where.target.tag}#${where.target.uid}> delivered at <${where.mount.tag}#${where.mount.uid}>`);
    fireTap(where);
  }
  for (const key of tapKeys) {
    const where = tapTargetByKey(all, key);
    console.log(`\n-- tap-key ${key} <${where.target.tag}#${where.target.uid}> delivered at <${where.mount.tag}#${where.mount.uid}>`);
    fireTap(where);
  }
  for (const uid of swipes) {
    console.log(`\n-- swipe left across <#${uid}>`);
    await fireSwipe(all, uid);
    await settle();
  }

  setTimeout(() => {
    for (const sym of peeks)
      for (const [name, realm] of contexts) {
        const v = realm?.[sym];
        const show = (x) => x && typeof x === "object" ? `<${x.f ? x.f.name + "/t" + x.f.t : "obj"} d1=${typeof x.d1 === "object" ? show(x.d1) : String(x.d1)} d2=${typeof x.d2 === "object" ? "obj" : String(x.d2)}>` : String(x);
        console.log(`peek ${name} ${sym} = ${show(v)}`);
      }
    const bound = all.filter((n) => n.events.size > 0);
    console.log(
      `\nthreads ${realms.join("+")}  elements ${all.length}  flushes ${flushes}  ` +
        `bound ${bound.length}  tags ${[...tagsCreated].join(" ")}`,
    );
    if (unheard.size)
      console.log(`dispatches nothing listened for: ${[...unheard].map(([k, v]) => `${k} x${v}`).join(", ")}`);
    if (lynxReads.size) console.log(`lynx.* read but absent: ${[...lynxReads].join(" ")}`);
    if (options.tree && root) console.log(`\n${render(root)}`);
    hsProfReport();
    process.exit(0);
  }, taps.length || tapKeys.length ? 500 : 0);
}, options.ms);
