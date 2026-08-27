/** Generic call-by-need runtime used by all generated Haskell programs. */
export interface Thunk<T = unknown> {
  readonly __ghctsThunk: true;
  force(): T;
}
export type Value<T = unknown> = T | Thunk<T>;
export function lazy<T>(compute: () => T): Thunk<T> {
  let state: "pending" | "running" | "done" = "pending";
  let result!: T;
  return {
    __ghctsThunk: true,
    force() {
      if (state === "done") return result;
      if (state === "running")
        throw new Error("<<loop>>: recursive thunk forced while evaluating");
      state = "running";
      try {
        result = compute();
        state = "done";
        return result;
      } catch (cause) {
        state = "pending";
        throw cause;
      }
    },
  };
}
/** Zero-arity IO actions must re-run on every force.  `lazy` would cache the
 * first `{}` from `create_ffi` and make every vnode the same object. */
export function io<T>(compute: () => T): Thunk<T> {
  let running = false;
  return {
    __ghctsThunk: true,
    force() {
      if (running)
        throw new Error("<<loop>>: recursive IO thunk forced while evaluating");
      running = true;
      try {
        return compute();
      } finally {
        running = false;
      }
    },
  };
}

// Host adapters may initialize `globalThis.runtime` after the generated
// Haskell runtime has loaded.  Keep callbacks installed by Haskell when an
// adapter replaces the bookkeeping object (Lynx uses separate JS contexts).
// This is a generic host-object assignment rule; it contains no Miso/Lynx
// knowledge and preserves the ordinary `runtime.nodes` shape.
const installRuntimeHost = (): void => {
  const host = globalThis as typeof globalThis & { runtime?: Record<string, unknown> };
  const descriptor = Object.getOwnPropertyDescriptor(host, "runtime");
  if (descriptor && descriptor.configurable === false) return;
  let current = host.runtime ?? {};
  Object.defineProperty(host, "runtime", {
    configurable: true,
    enumerable: true,
    get: () => current,
    set: (next: Record<string, unknown> | undefined) => {
      // Keep the identity stable.  A Haskell callback may be registered after
      // a host adapter initializes its bookkeeping fields; replacing the
      // object at that point would silently disconnect the callback.
      if (next && current && typeof current === "object") {
        Object.assign(current, next);
        return;
      }
      current = next ?? {};
    },
  });
};
installRuntimeHost();
function isThunk(value: unknown): value is Thunk {
  if (value == null) return false;
  const kind = typeof value;
  if (kind !== "object" && kind !== "function") return false;
  try {
    const thunk = value as Thunk;
    return thunk.__ghctsThunk === true && typeof thunk.force === "function";
  } catch {
    return false;
  }
}
export function prop(value: unknown, key: string): unknown {
  if (value == null) return undefined;
  const kind = typeof value;
  if (kind !== "object" && kind !== "function") return undefined;
  if (key === "globalThis" && value === globalThis) return globalThis;
  try {
    const found = (value as Record<string, unknown>)[key];
    if (found === undefined && key === "globalThis") return globalThis;
    return found;
  } catch {
    return key === "globalThis" ? globalThis : undefined;
  }
}
function hostKeys(value: unknown): string[] {
  if (value == null || typeof value !== "object") return [];
  try {
    return Object.keys(value);
  } catch {
    return [];
  }
}
function hostHas(value: unknown, key: string): boolean {
  if (value == null || typeof value !== "object") return false;
  try {
    if (Object.prototype.hasOwnProperty.call(value, key)) return true;
  } catch {
    /* PrimJS native hosts throw on hasOwnProperty */
  }
  return prop(value, key) !== undefined;
}
export function force<T>(value: Value<T>): T {
  return isThunk(value) ? value.force() : (value as T);
}
function forceFully<T>(value: Value<T>): T {
  let current: unknown = value;
  for (let depth = 0; depth < 32; depth++) {
    if (!isThunk(current)) return current as T;
    current = current.force();
  }
  return current as T;
}
export function apply(fn: unknown, argument: Thunk): unknown {
  const callable = force(fn as Value<(arg: Thunk) => unknown>);
  if (typeof callable !== "function") {
    const tag = prop(callable, "tag");
    if (callable && typeof callable === "object" && tag === "()")
      return () => callable;
    if (callable && typeof callable === "object" && tag === "[]")
      return force(argument);
    let detail = "host value";
    try {
      detail =
        typeof tag === "string" ? `constructor ${tag}` : String(callable);
    } catch {
      /* some JS engines throw when reading missing properties */
    }
    throw new Error(`Attempted to apply a non-function (${detail})`);
  }
  return callable(argument);
}
class Parked {
  readonly __ghctsPark = true;
  constructor(
    readonly wait: (resume: (value: unknown) => void) => void,
    readonly continuation = false,
  ) {}
}
function isParked(cause: unknown): cause is Parked {
  return (
    typeof cause === "object" &&
    cause !== null &&
    (cause as { __ghctsPark?: boolean }).__ghctsPark === true &&
    typeof (cause as Parked).wait === "function"
  );
}
function scheduleTurn(job: () => void): void {
  if (typeof setTimeout === "function") {
    const timer = setTimeout(job, 0);
    if (typeof timer === "object" && timer && "unref" in timer)
      (timer as { unref: () => void }).unref();
    return;
  }
  if (typeof queueMicrotask === "function") {
    queueMicrotask(job);
    return;
  }
  job();
}
function chainPark(parked: Parked, cont: (value: unknown) => unknown): never {
  throw new Parked((resume) => {
    parked.wait((value) => {
      scheduleTurn(() => {
        try {
          resume(cont(value));
        } catch (cause) {
          if (isParked(cause)) cause.wait(resume);
          else throw cause;
        }
      });
    });
  }, true);
}
function forceBind(
  action: unknown,
  next: (result: unknown) => unknown,
): unknown {
  try {
    return next(force(action as Value));
  } catch (cause) {
    if (isParked(cause)) chainPark(cause, next);
    throw cause;
  }
}
/** GHCJS blocks a Haskell thread; the JS event loop keeps running. */
export function runFiber(action: unknown): void {
  // Keep the fiber entry point re-entrant: parked IO continuations call back
  // here with another action after the host scheduler wakes them.
  const step = () => {
    try {
      const fn = force(action as Value);
      if (typeof fn === "function") force(apply(fn, lazy(() => 0)));
      else force(fn as Value);
    } catch (cause) {
      if (isParked(cause)) {
        cause.wait((value) => {
          scheduleTurn(() => {
            if (cause.continuation) runFiber(value);
            else step();
          });
        });
        return;
      }
      throw cause;
    }
  };
  step();
}
export interface DataValue {
  tag: string;
  fields: Thunk[];
  fieldNames?: string[];
}
/** Node-only host surface for GHCJS-style JS FFI. If a document already
 * exists (browser or other JS engine), leave every host global alone. */
function installHostAdapter(): void {
  const globalObject = globalThis as Record<string, any>;
  try {
    if (typeof globalObject.document !== "undefined") return;
  } catch {
    /* PrimJS throws when reading a missing global */
  }
  const childAt = (nodes: unknown, index: number) => {
    if (!Array.isArray(nodes) || index < 0 || index >= nodes.length) return null;
    return nodes[index];
  };
  const makeElement = (tag: string, text = "") => {
      const element: any = {
        tagName: tag === "#text" ? undefined : tag.toUpperCase(),
        nodeName: tag === "#text" ? "#text" : tag.toUpperCase(),
        localName: tag === "#text" ? undefined : tag,
        nodeType: tag === "#text" ? 3 : 1,
        value: "",
        children: [],
        childNodes: [],
        attributes: {},
        style: {
          setProperty(name: string, value: string) {
            (this as any)[name] = value ?? "";
          },
          getPropertyValue(name: string) {
            return (this as any)[name] ?? "";
          },
          removeProperty(name: string) {
            const previous = (this as any)[name];
            delete (this as any)[name];
            return previous ?? "";
          },
        },
        _text: text,
        parentNode: null,
        className: "",
        classList: {
          add(name: string) {
            const parts = new Set((element.className || "").split(/\s+/).filter(Boolean));
            parts.add(name);
            element.className = [...parts].join(" ");
          },
          remove(name: string) {
            element.className = (element.className || "")
              .split(/\s+/)
              .filter((item: string) => item && item !== name)
              .join(" ");
          },
        },
        get firstChild() {
          return childAt(element.childNodes, 0);
        },
        set firstChild(_value: unknown) {},
        get lastChild() {
          const nodes = element.childNodes;
          return Array.isArray(nodes) ? childAt(nodes, nodes.length - 1) : null;
        },
        set lastChild(_value: unknown) {},
        get nextSibling() {
          const siblings = element.parentNode?.childNodes ?? [];
          const index = Array.isArray(siblings) ? siblings.indexOf(element) : -1;
          return childAt(siblings, index + 1);
        },
        set nextSibling(_value: unknown) {},
        get previousSibling() {
          const siblings = element.parentNode?.childNodes ?? [];
          const index = Array.isArray(siblings) ? siblings.indexOf(element) : -1;
          return childAt(siblings, index - 1);
        },
        set previousSibling(_value: unknown) {},
        get textContent() {
          if (element.nodeType === 3 || element.childNodes.length === 0)
            return element._text ?? "";
          return element.childNodes
            .map((child: any) => child.textContent ?? "")
            .join("");
        },
        set textContent(value: string) {
          element._text = String(value);
          element.children = [];
          element.childNodes = [];
        },
        appendChild(child: any) {
          child.parentNode = element;
          element.childNodes.push(child);
          if (child.nodeType !== 3) element.children.push(child);
          return child;
        },
        removeChild(child: any) {
          element.children = element.children.filter(
            (item: any) => item !== child,
          );
          element.childNodes = element.childNodes.filter(
            (item: any) => item !== child,
          );
          child.parentNode = null;
          return child;
        },
        insertBefore(child: any, before: any) {
          child.parentNode = element;
          const index = before ? element.childNodes.indexOf(before) : -1;
          if (index < 0) return element.appendChild(child);
          element.childNodes.splice(index, 0, child);
          if (child.nodeType !== 3) {
            const childIndex = before
              ? element.children.indexOf(before)
              : element.children.length;
            element.children.splice(childIndex < 0 ? element.children.length : childIndex, 0, child);
          }
          return child;
        },
        replaceChild(next: any, previous: any) {
          element.insertBefore(next, previous);
          return element.removeChild(previous);
        },
        replaceChildren(...children: any[]) {
          element.children = [];
          element.childNodes = [];
          children.forEach((child) => element.appendChild(child));
        },
        setAttribute(name: string, value: any) {
          element.attributes[name] = String(value);
          (element as any)[name] = value;
        },
        getAttribute(name: string) {
          return element.attributes[name] ?? null;
        },
        removeAttribute(name: string) {
          delete element.attributes[name];
        },
        setAttributeNS(_ns: string, name: string, value: any) {
          element.setAttribute(name, value);
        },
        addEventListener(name: string, handler: any) {
          (element as any)[`on${name}`] = handler;
        },
        removeEventListener() {},
        dispatchEvent(event: any) {
          const dispatched = event && typeof event === "object" ? event : { type: event };
          if (dispatched.target == null) dispatched.target = element;
          let current: any = element;
          while (current) {
            const handler = current[`on${dispatched.type}`];
            if (typeof handler === "function") {
              dispatched.currentTarget = current;
              handler(dispatched);
            }
            current = current.parentNode;
          }
          return true;
        },
        click() {
          element.dispatchEvent({ type: "click", target: element, currentTarget: element });
        },
        querySelector() {
          return null;
        },
        focus() {},
        scrollIntoView() {},
        scrollTo() {},
      };
      if (tag === "video" || tag === "audio") {
        element.paused = true;
        element.currentTime = 0;
        element.playbackRate = 1;
        element.volume = 1;
        element.muted = false;
        element.play = () => {
          element.paused = false;
          return Promise.resolve();
        };
        element.pause = () => {
          element.paused = true;
        };
      }
      return element;
    };
    const body = makeElement("body");
    const head = makeElement("head");
    const html = makeElement("html");
    html.appendChild(head);
    html.appendChild(body);
    const findById = (node: any, id: string): any => {
      if (node?.id === id || node?.attributes?.id === id) return node;
      for (const child of node?.childNodes ?? []) {
        const found = findById(child, id);
        if (found) return found;
      }
      return null;
    };
    globalObject.document = {
      body,
      head,
      createElement: (tag: string) => makeElement(tag),
      createElementNS: (_ns: string, tag: string) => makeElement(tag),
        createTextNode: (text: string) => makeElement("#text", String(text ?? "")),
      // Browser applications conventionally mount into #root.  The
      // deterministic Node adapter represents that mount point with body so
      // the same generated entry can be exercised headlessly.
      getElementById: (id: string) =>
        id === "root" ? body : findById(html, id),
      querySelector: () => null,
      documentElement: html,
    };
    globalObject.window = globalObject;
  const globalListeners = new Map<string, Set<(...args: any[]) => void>>();
  if (typeof globalObject.addEventListener !== "function") {
    globalObject.addEventListener = (name: string, listener: (...args: any[]) => void) => {
      const listeners = globalListeners.get(name) ?? new Set();
      listeners.add(listener);
      globalListeners.set(name, listeners);
    };
  }
  if (typeof globalObject.removeEventListener !== "function") {
    globalObject.removeEventListener = (name: string, listener: (...args: any[]) => void) => {
      globalListeners.get(name)?.delete(listener);
    };
  }
  if (typeof globalObject.dispatchEvent !== "function") {
    globalObject.dispatchEvent = (event: any) => {
      const dispatched = event && typeof event === "object" ? event : { type: String(event) };
      dispatched.target ??= globalObject;
      dispatched.currentTarget = globalObject;
      for (const listener of globalListeners.get(dispatched.type) ?? []) {
        listener(dispatched);
      }
      return true;
    };
  }
  if (typeof globalObject.scrollTo !== "function") globalObject.scrollTo = () => {};
  if (typeof globalObject.scroll !== "function") globalObject.scroll = () => {};
  if (typeof globalObject.performance === "undefined") {
    globalObject.performance = { now: () => Date.now() };
  }
  if (typeof globalObject.location === "undefined") {
    globalObject.location = {
      pathname: "",
      search: "",
      hash: "",
      reload() {},
    };
  }
  if (typeof globalObject.history === "undefined") {
    globalObject.history = {
      back() {},
      forward() {},
      go() {},
      pushState() {},
      replaceState() {},
    };
  }
  if (typeof globalObject.navigator === "undefined") {
    globalObject.navigator = {};
  }
  if (typeof globalObject.navigator.onLine === "undefined") {
    globalObject.navigator.onLine = true;
  }
  if (typeof globalObject.navigator.clipboard === "undefined") {
    globalObject.navigator.clipboard = {
      writeText: async (_text: string) => undefined,
    };
  }
  if (typeof globalObject.navigator.mediaDevices === "undefined") {
    globalObject.navigator.mediaDevices = {
      getUserMedia: async () => ({}),
    };
  }
  if (typeof globalObject.navigator.geolocation === "undefined") {
    globalObject.navigator.geolocation = {
      getCurrentPosition(success?: (value: unknown) => void) {
        success?.({});
      },
    };
  }
  if (typeof globalObject.cookieStore === "undefined") {
    globalObject.cookieStore = {
      addEventListener() {},
      removeEventListener() {},
    };
  }
}
installHostAdapter();
try {
  (globalThis as Record<string, unknown>).globalThis = globalThis;
} catch {
  /* PrimJS may already expose globalThis as a non-writable host binding */
}
const rws: { reader: unknown; state: unknown; writer: unknown } = {
  reader: null,
  state: null,
  writer: { tag: "[]", fields: [] },
};
export function constructor(
  tag: string,
  arity: number,
  fieldNames?: string[],
): unknown {
  const collect = (fields: Thunk[]): unknown =>
    fields.length === arity
      ? ((fieldNames
          ? { tag, fields, fieldNames }
          : { tag, fields }) satisfies DataValue)
      : (value: Thunk) => collect([...fields, value]);
  return collect([]);
}
export function tuple(fields: Thunk[]): DataValue {
  return { tag: `(${",".repeat(Math.max(0, fields.length - 1))})`, fields };
}
export function field(value: unknown, name: string): unknown {
  const record = force(value as Value) as DataValue | undefined;
  if (!record) return prelude.unit;
  const names = prop(record, "fieldNames");
  const index = Array.isArray(names) ? names.indexOf(name) : -1;
  if (index < 0) {
    if (name === "unParser") {
      if (isData(record) && (record.tag === "Left" || record.tag === "Right"))
        return record;
      return { tag: "Right", fields: [lazy(() => record)] } satisfies DataValue;
    }
    return prelude.unit;
  }
  const fields = prop(record, "fields");
  if (!Array.isArray(fields) || fields[index] === undefined) return prelude.unit;
  // GHCJS's primitive fields are unboxed when they cross a representation
  // boundary.  A field can contain more than one lazy indirection after
  // record updates; expose its fully forced value to selectors/FFI callers.
  return forceFully(fields[index]);
}
export function fieldAt(value: unknown, index: number): unknown {
  const record = force(value as Value) as DataValue | undefined;
  const fields = prop(record, "fields");
  if (!record || !Array.isArray(fields) || fields[index] === undefined)
    return prelude.unit;
  return forceFully(fields[index]);
}
export function updateRecord(
  value: unknown,
  replacements: Record<string, Thunk>,
): DataValue {
  const record = force(value as Value) as DataValue;
  const names = record.fieldNames ?? [];
  const fields = record.fields.map(
    (current, index) => replacements[names[index]] ?? current,
  );
  for (const name of Object.keys(replacements))
    if (!names.includes(name))
      throw new Error(`No field ${name} on ${record.tag}`);
  return { ...record, fields };
}
/** Evaluates the explicitly supplied JavaScript body of a foreign import. */
function listToArray(value: unknown): unknown[] {
  const items: unknown[] = [];
  let current = force(value as Value);
  while (prop(current, "tag") === ":") {
    const fields = prop(current, "fields");
    if (!Array.isArray(fields)) break;
    items.push(force(fields[0]));
    current = force(fields[1] as Value);
  }
  if (prop(current, "tag") !== "[]")
    throw new Error("Expected a Haskell list at JavaScript FFI boundary");
  return items;
}
function listFromArray(values: unknown[]): DataValue {
  return values.reduceRight<DataValue>((tail, item) => ({ tag: ":", fields: [lazy(() => item), lazy(() => tail)] }), prelude.nil as DataValue);
}
function escapeHaskellString(text: string): string {
  let out = "";
  for (const ch of text) {
    if (ch === "\\") out += "\\\\";
    else if (ch === '"') out += '\\"';
    else if (ch === "\n") out += "\\n";
    else if (ch === "\t") out += "\\t";
    else if (ch === "\r") out += "\\r";
    else out += ch;
  }
  return out;
}
/** Haskell's derived `show`: unlike the naive tag-only fallback this
 * replaces, a compound value (list, tuple, or applied constructor) must
 * recurse into its fields, not just print its own tag. `precedence`
 * mirrors `showsPrec`'s convention - 0 at the top call, 11 for a
 * constructor's own arguments - so a negative number or another applied
 * constructor gets wrapped in parens only when nested (`show (Just (-5))`
 * is "Just (-5)", but `show (-5)` alone is "-5", no parens). */
function showValue(value: unknown, precedence: number): string {
  const forced = force(value as Value);
  if (typeof forced === "boolean") return forced ? "True" : "False";
  if (typeof forced === "string") return `"${escapeHaskellString(forced)}"`;
  if (typeof forced === "bigint" || typeof forced === "number") {
    const text = String(forced);
    return forced < 0 && precedence > 6 ? `(${text})` : text;
  }
  if (isData(forced)) {
    if (forced.tag === "Fingerprint") return jsString(forced);
    if (forced.tag === ":" || forced.tag === "[]") {
      const items = listToArray(forced);
      if (items.length > 0 && items.every((item) => typeof item === "string" && item.length === 1))
        return `"${escapeHaskellString(items.join(""))}"`;
      return `[${items.map((item) => showValue(item, 0)).join(",")}]`;
    }
    if (/^\(,+\)$/.test(forced.tag))
      return `(${forced.fields.map((field) => showValue(field, 0)).join(",")})`;
    if (forced.fields.length === 0) return forced.tag;
    const rendered = `${forced.tag} ${forced.fields.map((field) => showValue(field, 11)).join(" ")}`;
    return precedence > 10 ? `(${rendered})` : rendered;
  }
  return String(forced);
}
function mapMList(mapper: Thunk, values: Thunk): DataValue {
  const results: unknown[] = [];
  for (const value of foldableToArray(values))
    results.push(
      force(
        apply(
          mapper,
          lazy(() => value),
        ),
      ),
    );
  return listFromArray(results);
}
function foldableToArray(value: unknown): unknown[] {
  const current = force(value as Value);
  if (!current || typeof current !== "object") return [];
  const tag = prop(current, "tag");
  const fields = prop(current, "fields");
  if (
    tag === "Nothing" ||
    tag === "[]" ||
    tag === "Empty" ||
    tag === "Left"
  )
    return [];
  if (tag === "Just" || tag === "Right") {
    const inner = forceFully(Array.isArray(fields) ? (fields[0] as Value) : undefined);
    return inner == null ? [] : [inner];
  }
  if (tag === ":" || tag === "Cons") {
    const items: unknown[] = [];
    let node: unknown = current;
    while (prop(node, "tag") === ":" || prop(node, "tag") === "Cons") {
      const nodeFields = prop(node, "fields");
      if (!Array.isArray(nodeFields)) break;
      items.push(force(nodeFields[0]));
      node = force(nodeFields[1] as Value);
    }
    return items;
  }
  return [];
}
const enumIndexes = new Map<string, number>();
const enumConstructorTypes = new Map<string, string>();
export function registerEnum(tag: string, index: number, typeName?: string): void {
  enumIndexes.set(tag, index);
  if (typeName) enumConstructorTypes.set(tag, typeName);
}
const enumTypes = new Set<string>();
export function registerEnumType(typeName: string): void {
  enumTypes.add(typeName);
}
const constructorTypes = new Map<string, string>();
const constructorFieldNames = new Map<string, string[]>();
export function registerConstructorType(
  tag: string,
  typeName: string,
  fieldNames?: string[],
): void {
  constructorTypes.set(tag, typeName);
  if (fieldNames?.length) constructorFieldNames.set(tag, fieldNames);
}
interface RegisteredInstance {
  className: string;
  target: string;
  method: string;
  impl: Thunk;
  // Computed once here instead of on every dispatch attempt in
  // tryMarshalInstances/tryBinaryInstance - a real Miso app can register
  // dozens of instances for one class/method pair (FromMisoString alone
  // has ~14), and both lookups used to re-parse `target` with a regex (or
  // two, plus a string split) per candidate on every single call,
  // including calls on hot paths like `==`/`compare` (diffing, `elem`,
  // sorting) and every FFI-adjacent pattern match.
  targetName: string | undefined;
  headName: string | undefined;
}
const instanceTable: RegisteredInstance[] = [];
export function registerInstance(
  className: string,
  target: string,
  method: string,
  impl: Thunk,
): void {
  instanceTable.push({
    className,
    target,
    method,
    impl,
    targetName: marshalTargetName(target, className),
    headName: target.match(/[A-Z][A-Za-z0-9_']*/)?.[0],
  });
}
const primitiveMarshalTargets = new Set([
  "JSVal",
  "Int",
  "Integer",
  "Word",
  "Word8",
  "Word16",
  "Word32",
  "Word64",
  "Char",
  "Float",
  "Double",
  "Bool",
  "Text",
  "String",
  "JSString",
  "Value",
  "Object",
  "Maybe",
  "Either",
  "IO",
]);
function marshalTargetName(target: string, className: string): string | undefined {
  const trimmed = target.trim();
  if (!trimmed || /\s/.test(trimmed) || trimmed.startsWith("(") || trimmed.startsWith("["))
    return undefined;
  const parts = trimmed.split(".");
  const name = parts[parts.length - 1] ?? trimmed;
  if (!/^[A-Z][A-Za-z0-9_']*$/.test(name) || name === "()")
    return undefined;
  if (
    (className === "FromJSVal" || className === "ToJSVal") &&
    primitiveMarshalTargets.has(name)
  )
    return undefined;
  return name;
}
const marshalStack: Thunk[] = [];
function tryMarshalInstances(
  className: string,
  method: string,
  value: unknown,
  expected?: string,
): unknown {
  const forced = force(value as Thunk);
  // ghcts has no static type inference, so a return-type-polymorphic method
  // (fromMisoString and friends: FromJSVal/ToJSVal narrow by shape/tag below,
  // but plenty of other classes - FromMisoString chief among them - don't)
  // can't know which registered instance the call site actually wants; it
  // can only try instances against the runtime value and see which one
  // claims the result. Trying registration order (source/import order)
  // first means a generic, always-succeeding instance (e.g. `instance
  // FromMisoString MisoString where fromMisoStringEither = Right`, true for
  // *any* string) permanently shadows every more specific instance declared
  // after it (Int/Double/Fingerprint/...), which never gets a chance to run.
  // Trying the most-recently-registered instance first at least prefers
  // more specific/derived instances over foundational catch-all ones.
  // Iterate in reverse registration order without allocating a copy - this
  // runs on every FromJSVal/ToJSVal-adjacent pattern match that misses the
  // fast already-tagged path in fromJSValAs, so a fresh reversed array per
  // call is wasted allocation on a genuine hot path.
  for (let i = instanceTable.length - 1; i >= 0; i--) {
    const inst = instanceTable[i]!;
    if (inst.className !== className || inst.method !== method) continue;
    const name = inst.targetName;
    if (!name) continue;
    if (expected && className === "FromJSVal" && name !== expected) continue;
    if (!expected && className === "FromJSVal") {
      if (typeof forced !== "string" || !enumTypes.has(name)) continue;
    }
    if (className === "ToJSVal") {
      const tag = isData(forced) ? forced.tag : undefined;
      if (!tag || (name !== tag && enumConstructorTypes.get(tag) !== name)) continue;
    }
    if (marshalStack.includes(inst.impl)) continue;
    marshalStack.push(inst.impl);
    try {
      let result = force(apply(inst.impl, lazy(() => forced)));
      if (className === "FromJSVal" && typeof result === "function")
        result = force(result());
      if (className === "FromJSVal") {
        if (isData(result) && result.tag === "Just") return result;
        if (expected && isData(result) && result.tag === expected) {
          return { tag: "Just", fields: [lazy(() => result)] } satisfies DataValue;
        }
        continue;
      }
      // An Either-returning method (fromMisoStringEither and its ilk) has
      // its own "this instance doesn't apply" signal that isn't a thrown
      // exception: a plain `Left` value. Treat it the same as a throw -
      // keep trying instances - instead of returning the wrong type's
      // rejection as if it were the answer.
      if (isData(result) && result.tag === "Left") continue;
      return result;
    } catch {
      continue;
    } finally {
      marshalStack.pop();
    }
  }
  return undefined;
}
export function classMethod(
  className: string,
  method: string,
  value: unknown,
): unknown {
  const result = tryMarshalInstances(className, method, value);
  if (result !== undefined) return result;
  throw new Error(`${className}.${method} has no matching instance`);
}
function asBool(value: unknown): DataValue | undefined {
  if (value === true) return prelude.true;
  if (value === false) return prelude.false;
  if (isData(value) && value.tag === "True") return prelude.true;
  if (isData(value) && value.tag === "False") return prelude.false;
  if (isData(value) && value.tag === "Bool" && value.fields[0])
    return asBool(force(value.fields[0] as Value));
  return undefined;
}
export function fromJSValAs(tag: string, value: Thunk): unknown {
  const forced = force(value);
  if (isData(forced) && forced.tag === tag) return forced;
  if (tag === "True" || tag === "False") {
    const bool = asBool(forced);
    if (bool) return bool;
  }
  if (tag === "Nothing") {
    if (
      forced == null ||
      (isData(forced) && (forced.tag === "()" || forced.tag === "Nothing" || forced.tag === "Null"))
    )
      return { tag: "Nothing", fields: [] } satisfies DataValue;
  }
  if (tag === "()") {
    if (forced == null) return prelude.unit;
    if (isData(forced) && (forced.tag === "Null" || forced.tag === "()"))
      return prelude.unit;
    if (!isData(forced) && typeof forced !== "function") return prelude.unit;
  }
  if (isData(forced)) return forced;
  if (tag === "Just" && forced != null)
    return { tag: "Just", fields: [lazy(() => forced)] } satisfies DataValue;
  if (typeof forced === "string" && enumIndexes.has(tag))
    return { tag, fields: [] } satisfies DataValue;
  if (typeof forced === "number" && enumIndexes.get(tag) === forced)
    return { tag, fields: [] } satisfies DataValue;
  const typeName = constructorTypes.get(tag) ?? enumConstructorTypes.get(tag) ?? tag;
  // A user-written FromJSVal instance owns the wire shape for its type - it
  // may use arbitrary key names (e.g. Miso.Runtime's `ToJSVal COMPONENT`
  // writes "compId"/"compParentId", not the Haskell selector spellings
  // "componentComponentId"/"componentComponentParentId"). It must run
  // before the generic selector-name guess below: that guess can partially
  // match by coincidence (one field's guessed name happens to collide with
  // a real key, e.g. componentType) and would otherwise short-circuit with
  // every other field silently undefined instead of ever reaching the
  // instance that actually knows the real wire keys.
  const instanceDecoded = tryMarshalInstances("FromJSVal", "fromJSVal", forced, typeName);
  if (isData(instanceDecoded) && instanceDecoded.tag === "Just") return force(instanceDecoded.fields[0]);
  // GHCJS foreign records arrive as ordinary JavaScript objects.  Preserve
  // the generic constructor-pattern contract by reifying a registered
  // constructor from its field metadata for types with no FromJSVal
  // instance of their own.  This is deliberately type metadata driven; no
  // Miso shape is recognized here.
  const fields = constructorFieldNames.get(tag);
  if (fields && forced && typeof forced === "object") {
    try {
      const object = forced as Record<string, unknown>;
      const wireName = (name: string): string => {
        if (hostHas(object, name)) return name;
        const match = name.match(/^[a-z][a-z0-9_']*([A-Z].*)$/);
        // A single selector such as recN is not enough evidence for a
        // structural wire spelling: its FromJSVal instance may deliberately
        // use unrelated names.  GHCJS-qualified record selectors have an
        // additional capitalized component (e.g. componentComponentType).
        if (!match || !/[A-Z].*[A-Z]/.test(match[1])) return name;
        let candidate = match[1][0].toLowerCase() + match[1].slice(1);
        if (hostHas(object, candidate)) return candidate;
        // GHCJS record selectors may carry the declaring type prefix more
        // than once (e.g. TypeTypeField); the wire object contains the
        // progressively unqualified spelling (TypeField or Field).  Search
        // only those type-prefix removals, never arbitrary suffix matches.
        const prefix = tag[0]?.toLowerCase() + tag.slice(1);
        while (candidate.startsWith(prefix)) {
          candidate = candidate.slice(prefix.length);
          if (!candidate) break;
          candidate = candidate[0].toLowerCase() + candidate.slice(1);
          if (hostHas(object, candidate)) return candidate;
        }
        return name;
      };
      const names = fields.map((name) => {
        const direct = wireName(name);
        if (hostHas(object, direct)) return direct;
        // Do not guess from arbitrary suffixes: a user FromJSVal instance
        // must retain control when its wire names (e.g. n/ty) do not follow
        // the Haskell selector spelling.  Only the GHCJS-compatible camel
        // case spelling above is structural.
        return direct;
      });
      // JavaScript records crossing the GHCJS FFI may be partial.  In
      // particular, a record constructor can be used as a small protocol
      // message whose omitted fields decode through Maybe as undefined.
      // Reify the record when at least one declared property is present and
      // leave the other selectors backed by the missing host property.
      // Requiring every property would reject valid FromJSVal records before
      // their field-level decoders get a chance to handle absence.
      if (names.some((name) => hostHas(object, name))) {
        return {
          tag,
          fields: names.map((name) => lazy(() => prop(object, name))),
          fieldNames: fields,
        } satisfies DataValue;
      }
    } catch {
      /* native host objects reject enumeration */
    }
  }
  return forced;
}
interface DerivedJsonConstructor {
  name: string;
  arity: number;
  fields?: string[];
}
interface DerivedJsonSpec {
  typeName: string;
  allNullary: boolean;
  constructors: DerivedJsonConstructor[];
}
const derivedJsonByConstructor = new Map<string, DerivedJsonSpec>();
const derivedJsonByType = new Map<string, DerivedJsonSpec>();
export function registerDerivedJSON(spec: DerivedJsonSpec): void {
  derivedJsonByType.set(spec.typeName, spec);
  for (const constructor of spec.constructors)
    derivedJsonByConstructor.set(constructor.name, spec);
}
type StaticPointerTable = Array<StaticPointerTable | DataValue | undefined>;
const rtsGlobal = globalThis as typeof globalThis & {
  h$static_pointer_table?: StaticPointerTable;
  h$static_pointer_table_keys?: string[];
};
const staticPtrTable = rtsGlobal.h$static_pointer_table ??= [];
const staticPtrKeys = rtsGlobal.h$static_pointer_table_keys ??= [];
let staticPtrSeq = 0;
function staticPtr(value: Thunk, stableKey?: string): DataValue {
  // GHCJS static keys are link-time identities, not allocation counters. A
  // Lynx bundle evaluates the same linked program in separate JS contexts;
  // an incrementing key would therefore disagree between BTS and MTS.
  const key = stableKey ?? (++staticPtrSeq).toString(16).padStart(32, "0");
  const ptr = Object.assign({ tag: "StaticPtr", fields: [value] } satisfies DataValue, { key });
  const words = [0, 1, 2, 3].map((index) => Number.parseInt(key.slice(index * 8, index * 8 + 8), 16) >>> 0);
  let level: StaticPointerTable = staticPtrTable;
  for (const word of words.slice(0, 3)) {
    level[word] ??= [];
    level = level[word] as StaticPointerTable;
  }
  level[words[3]!] = ptr;
  if (!staticPtrKeys.includes(key)) staticPtrKeys.push(key);
  return ptr;
}
/** Register link-time static pointers before either Lynx JS context runs the
 * application entry point. This mirrors GHCJS's static-pointer table. */
/** GHCJS RTS spelling for inserting a static pointer.  GHCTS keeps the
 * fingerprint as its canonical serialized key at this boundary; the lookup
 * semantics remain the RTS table semantics. */
export function h$hs_spt_insert(key1: number, key2: number, key3: number, key4: number, value: Thunk): void {
  const key = [key1, key2, key3, key4]
    .map((word) => (word >>> 0).toString(16).padStart(8, "0"))
    .join("");
  staticPtr(value, key);
}
export const registerStaticPtr = h$hs_spt_insert;
function deRefStaticPtr(value: Thunk): unknown {
  const forced = force(value) as DataValue | undefined;
  if (isData(forced) && forced.fields[0]) return force(forced.fields[0] as Value);
  return forced;
}
function staticKeyValue(value: Thunk): DataValue {
  const forced = force(value) as (DataValue & { key?: string }) | undefined;
  const key = forced?.key ?? "0".repeat(32);
  return { tag: "Fingerprint", fields: [lazy(() => key)] } satisfies DataValue;
}
function unsafeLookupStaticPtrValue(value: Thunk): unknown {
  const key = jsString(value);
  const words = [0, 1, 2, 3].map((index) => Number.parseInt(key.slice(index * 8, index * 8 + 8), 16) >>> 0);
  let level: StaticPointerTable | DataValue | undefined = staticPtrTable;
  for (const word of words) {
    if (!Array.isArray(level)) { level = undefined; break; }
    level = level[word];
  }
  const found = level && !Array.isArray(level) ? level : undefined;
  return found ? prelude.just(lazy(() => found)) : prelude.nothing;
}
function jsonString(text: string): DataValue {
  return { tag: "String", fields: [lazy(() => text)] } satisfies DataValue;
}
function jsonNumber(n: number): DataValue {
  return { tag: "Number", fields: [lazy(() => n)] } satisfies DataValue;
}
function jsonBool(value: boolean): DataValue {
  return { tag: "Bool", fields: [lazy(() => (value ? prelude.true : prelude.false))] } satisfies DataValue;
}
function encodeDerived(value: unknown): unknown {
  const forced = force(value);
  if (typeof forced === "number") return jsonNumber(forced);
  if (typeof forced === "boolean") return jsonBool(forced);
  if (typeof forced === "string") return jsonString(forced);
  if (!isData(forced)) return jsonFromJavaScript(jsValue(value));
  const spec = derivedJsonByConstructor.get(forced.tag);
  if (spec?.allNullary && forced.fields.length === 0) return jsonString(forced.tag);
  const ctor = spec?.constructors.find((item) => item.name === forced.tag);
  if (ctor?.fields?.length) {
    const map = new Map<string, unknown>();
    ctor.fields.forEach((name, index) => map.set(name, encodeDerived(forced.fields[index])));
    return { tag: "Object", fields: [lazy(() => map)] } satisfies DataValue;
  }
  if (ctor && ctor.arity === 1 && forced.fields[0]) return encodeDerived(forced.fields[0]);
  if (ctor && ctor.arity === 0) return jsonString(forced.tag);
  if (forced.fieldNames?.length) {
    const map = new Map<string, unknown>();
    forced.fieldNames.forEach((name, index) => map.set(name, encodeDerived(forced.fields[index])));
    return { tag: "Object", fields: [lazy(() => map)] } satisfies DataValue;
  }
  if (forced.tag === ":" || forced.tag === "[]") {
    return {
      tag: "Array",
      fields: [lazy(() => listFromArray(listToArray(forced).map(encodeDerived)))],
    } satisfies DataValue;
  }
  if (forced.tag === "Nothing") return { tag: "Null", fields: [] } satisfies DataValue;
  if (forced.tag === "Just") return encodeDerived(forced.fields[0]);
  if (forced.tag === "True") return jsonBool(true);
  if (forced.tag === "False") return jsonBool(false);
  return jsonFromJavaScript(jsValue(value));
}
function objectMap(value: DataValue): Map<string, unknown> | undefined {
  const map = force(value.fields[0] as Value);
  return map instanceof Map ? map : undefined;
}
function decodeDerived(value: unknown): unknown {
  const forced = force(value);
  if (!isData(forced)) return forced;
  if (forced.tag === "String" && forced.fields[0]) {
    const text = jsString(forced.fields[0]);
    const spec = derivedJsonByConstructor.get(text);
    if (spec?.allNullary) return { tag: text, fields: [] } satisfies DataValue;
    return text;
  }
  if (forced.tag === "Number" && forced.fields[0]) return force(forced.fields[0] as Value);
  if (forced.tag === "Bool" && forced.fields[0]) return force(forced.fields[0] as Value);
  if (forced.tag === "True" || forced.tag === "False") return forced.tag === "True";
  if (forced.tag === "Null") return prelude.nothing;
  if (forced.tag === "Array") return forced.fields[0] ? force(forced.fields[0] as Value) : prelude.nil;
  if (forced.tag === "Object") {
    const map = objectMap(forced);
    if (!map) return forced;
    if (map.has("tag")) {
      const tagValue = map.get("tag");
      const tag = isData(tagValue) && tagValue.tag === "String" ? jsString(tagValue.fields[0]) : jsString(tagValue);
      const spec = derivedJsonByConstructor.get(tag);
      const ctor = spec?.constructors.find((item) => item.name === tag);
      if (ctor) {
        const contents = map.get("contents");
        if (ctor.arity === 0) return { tag, fields: [] } satisfies DataValue;
        if (ctor.fields?.length && isData(contents) && contents.tag === "Object") {
          const inner = objectMap(contents) ?? new Map();
          return {
            tag,
            fieldNames: ctor.fields,
            fields: ctor.fields.map((name) => lazy(() => decodeDerived(inner.get(name)))),
          } satisfies DataValue;
        }
        if (ctor.arity === 1) return { tag, fields: [lazy(() => decodeDerived(contents))] } satisfies DataValue;
      }
    }
    for (const spec of derivedJsonByType.values()) {
      const ctor = spec.constructors.find(
        (item) => item.fields && item.fields.every((name) => map.has(name)),
      );
      if (ctor?.fields) {
        return {
          tag: ctor.name,
          fieldNames: ctor.fields,
          fields: ctor.fields.map((name) => lazy(() => decodeDerived(map.get(name)))),
        } satisfies DataValue;
      }
    }
  }
  return forced;
}
function fromMisoStringEitherValue(value: Thunk): unknown {
  const text = jsString(value);
  if (/^[+-]?(?:\d+\.\d*|\.\d+)(?:[eE][+-]?\d+)?$/.test(text.trim())) {
    const parsed = Number.parseFloat(text);
    if (!Number.isNaN(parsed)) return prelude.right(lazy(() => parsed));
  }
  return prelude.right(lazy(() => force(value)));
}
function isData(value: unknown): value is DataValue {
  if (value == null || typeof value !== "object") return false;
  return typeof prop(value, "tag") === "string" && Array.isArray(prop(value, "fields"));
}
/** Marshal a Haskell value across the JavaScript FFI.  Class dictionaries
 * (ToJSVal) are applied first for enum-like constructors; remaining
 * algebraic data uses the same generic representation every boot library
 * already shares. */
function isHostFunction(fn: Function): boolean {
  if (prop(fn, "__ghctsCallback")) return false;
  const source = Function.prototype.toString.call(fn);
  if (source.includes("[native code]")) return true;
  if (/^\s*(async\s+)?function\b/.test(source)) return true;
  // Lynx/TS emit `getVTree((vtree) => …)`. Wrapping those as Haskell
  // callbacks passes a thunk into `delegateEvent` and drops the event.
  if (
    source.includes("=>") &&
    !source.includes("apply(") &&
    !source.includes("lazy(")
  )
    return true;
  return false;
}
function jsCallback(fn: Function): Function {
  if ((fn as { __ghctsCallback?: boolean }).__ghctsCallback) return fn;
  const wrapped = (fn as { __ghctsJs?: Function }).__ghctsJs;
  if (wrapped) return wrapped;
  if (isHostFunction(fn)) return fn;
  const callback = (...args: unknown[]) => {
    // Mirror runFiber's park handling. A Haskell callback invoked from JS is
    // an ordinary fiber: when it parks, the resumed value is either the
    // continuation to run (`continuation`) or a signal to retry the step.
    // Discarding it - as this used to - silently drops the rest of the
    // callback body with no exception, so an event listener appears to do
    // nothing at all. The JS caller has already been returned to by then,
    // so only the effects continue; there is no value left to hand back.
    const step = (): unknown => {
      try {
        let current: unknown = fn;
        for (const arg of args) current = apply(current, lazy(() => arg));
        return forceFully(current as Value);
      } catch (cause) {
        if (isParked(cause)) {
          cause.wait((value) => {
            scheduleTurn(() => {
              if (cause.continuation) runFiber(value);
              else step();
            });
          });
          return;
        }
        throw cause;
      }
    };
    return step();
  };
  (callback as { __ghctsCallback?: boolean }).__ghctsCallback = true;
  (fn as { __ghctsJs?: Function }).__ghctsJs = callback;
  (callback as { __ghctsJs?: Function }).__ghctsJs = callback;
  return callback;
}
function jsString(value: unknown): string {
  let current: unknown = value;
  for (let depth = 0; depth < 8; depth++) {
    const next = force(current as Value);
    if (next === current) break;
    current = next;
  }
  if (typeof current === "string") return current;
  if (typeof current === "number" || typeof current === "boolean") return String(current);
  if (isData(current) && (current.tag === ":" || current.tag === "[]"))
    return listToArray(current).map(jsString).join("");
  if (isData(current) && current.tag === "Just") return jsString(current.fields[0]);
  if (isData(current) && current.tag === "Fingerprint") {
    const words = current.fields ?? [];
    if (words.length >= 2)
      return `${jsString(words[0]).padStart(16, "0")}${jsString(words[1]).padStart(16, "0")}`;
    if (words[0]) return jsString(words[0]);
  }
  if (isData(current) && current.tag === "StaticPtr") {
    const key = (current as DataValue & { key?: unknown }).key;
    if (typeof key === "string") return key;
  }
  return String(current ?? "");
}
function isHostNode(value: unknown): boolean {
  return (
    !!value &&
    typeof value === "object" &&
    typeof (value as { nodeType?: unknown }).nodeType === "number" &&
    typeof (value as { appendChild?: unknown }).appendChild === "function"
  );
}
function jsonFromJavaScript(value: unknown): unknown {
  if (value == null) return { tag: "Null", fields: [] } satisfies DataValue;
  if (typeof value === "boolean")
    return { tag: "Bool", fields: [lazy(() => (value ? prelude.true : prelude.false))] } satisfies DataValue;
  if (typeof value === "number")
    return { tag: "Number", fields: [lazy(() => value)] } satisfies DataValue;
  if (typeof value === "string")
    return { tag: "String", fields: [lazy(() => value)] } satisfies DataValue;
  if (typeof value !== "object") return value;
  if (isData(value) || value instanceof Map || isHostNode(value)) return value;
  if (Array.isArray(value))
    return {
      tag: "Array",
      fields: [lazy(() => listFromArray(value.map(jsonFromJavaScript)))],
    } satisfies DataValue;
  const map = new Map<string, unknown>();
  for (const [key, item] of Object.entries(value as Record<string, unknown>))
    map.set(key, jsonFromJavaScript(item));
  return { tag: "Object", fields: [lazy(() => map)] } satisfies DataValue;
}
export function jsValue(value: unknown): unknown {
  const forced = forceFully(value as Value);
  if (typeof forced === "function") {
    const existing = (forced as { __ghctsJs?: Function }).__ghctsJs;
    if (existing) return existing;
    if ((forced as { __ghctsCallback?: boolean }).__ghctsCallback) return forced;
    if (isHostFunction(forced)) return forced;
    return jsCallback(forced);
  }
  // GHCJS's plain `Int`/`Word` cross the JS FFI boundary as ordinary
  // numbers (see GHC.StgToJS.Prim/Literal - only the explicitly-sized
  // Int64/Word64 get a two-value hi/lo split, via their own ToJSVal
  // instance, never reaching this generic fallback as a bare BigInt).
  // ghcts represents Int as BigInt internally (`jInt` in compiler.ts), so
  // a value that never went through an explicit ToJSVal instance would
  // otherwise cross this boundary as a raw BigInt - which most native
  // bridges (JSON.stringify, structured clone, JSI-style bridges) either
  // throw on or silently drop, corrupting the message.
  if (typeof forced === "bigint") return Number(forced);
  if (forced == null || typeof forced !== "object") return forced;
  if (forced instanceof Map) {
    if (forced.size === 0) return [];
    const object: Record<string, unknown> = {};
    for (const [key, item] of forced) object[jsString(key)] = jsValue(item);
    return object;
  }
  if (Array.isArray(forced)) return forced.map(jsValue);
  if (!isData(forced)) return forced;
  if (forced.tag === "[]" || forced.tag === ":") {
    const items = listToArray(forced).map(jsValue);
    if (
      items.length > 0 &&
      items.every((item) => typeof item === "string" && item.length === 1)
    )
      return items.join("");
    return items;
  }
  if (forced.tag === "Nothing") return null;
  if (forced.tag === "Just") return jsValue(forced.fields[0]);
  if (forced.tag === "True") return true;
  if (forced.tag === "False") return false;
  if (forced.tag === "()") return null;
  if (/^\(,+\)$/.test(forced.tag)) return forced.fields.map(jsValue);
  if ((forced.tag === "Object" || forced.tag === "Function" || forced.tag === "VTree" || forced.tag === "JSVal") && forced.fields.length)
    return jsValue(forced.fields[0]);
  if (forced.tag === "CAPTURE" && forced.fields.length === 0) return true;
  if (forced.tag === "BUBBLE" && forced.fields.length === 0) return false;
  if (forced.fields.length === 0 && enumIndexes.has(forced.tag))
    return enumIndexes.get(forced.tag);
  if (forced.fieldNames?.length) {
    const object: Record<string, unknown> = {};
    forced.fieldNames.forEach((name, index) => {
      object[name] = jsValue(forced.fields[index]);
    });
    return object;
  }
  if (forced.fields.length === 1 && forced.tag !== "Left" && forced.tag !== "Right") {
    const inner = forceFully(forced.fields[0] as Value);
    if (inner instanceof Map && inner.size === 0) return [];
    return jsValue(forced.fields[0]);
  }
  return forced;
}
function toJavaScript(value: unknown): unknown {
  const forced = forceFully(value as Value);
  if (forced instanceof Map)
    return [...forced.entries()].map(([name, phase]) => ({
      name: jsString(name),
      capture: Boolean(jsValue(phase)),
    }));
  return jsValue(forced);
}
function asMVar(value: unknown): { queue: unknown[]; waiters: Array<() => void> } {
  const m = unwrapJsHost(forceFully(value as Value)) as {
    queue?: unknown[];
    waiters?: Array<() => void>;
  };
  if (m == null || typeof m !== "object")
    throw new Error("takeMVar/putMVar expected an MVar");
  if (!Array.isArray(m.queue)) m.queue = [];
  if (!Array.isArray(m.waiters)) m.waiters = [];
  return m as { queue: unknown[]; waiters: Array<() => void> };
}
function wakeMVar(m: { waiters: Array<() => void> }): void {
  const waiters = m.waiters.splice(0);
  for (const waiter of waiters) waiter();
}
function unwrapCallable(value: unknown): unknown {
  const forced = forceFully(value as Value);
  if (typeof forced === "function") return forced;
  if (
    isData(forced) &&
    (forced.tag === "Function" || forced.tag === "JSVal") &&
    forced.fields[0]
  )
    return unwrapCallable(forced.fields[0]);
  return forced;
}
function jsApplyArgList(value: unknown): unknown[] {
  if (Array.isArray(value)) return value;
  if (isData(value) && (value.tag === ":" || value.tag === "[]"))
    return listToArray(value).map(jsValue);
  if (value == null) return [];
  return [value];
}
const SIMPLE_FOREIGN = Symbol("simple-foreign");
function argAt(values: unknown[], index: number): unknown {
  if (index < 0 || index >= values.length) return undefined;
  try {
    return values[index];
  } catch {
    return undefined;
  }
}
function unwrapJsHost(value: unknown): unknown {
  let current: unknown = forceFully(value as Value);
  for (let depth = 0; depth < 8; depth++) {
    if (!isData(current)) return current;
    if (
      (current.tag === "Object" ||
        current.tag === "JSVal" ||
        current.tag === "Function") &&
      current.fields[0]
    ) {
      current = forceFully(current.fields[0] as Value);
      continue;
    }
    return current;
  }
  return current;
}
function hostStore(value: unknown): unknown {
  const forced = forceFully(value as Value);
  if (isData(forced) && (forced.tag === "True" || forced.tag === "False"))
    return forced.tag === "True";
  // GHCJS ToJSVal erases the representation of Maybe and Fingerprint at the
  // JavaScript boundary.  This matters for StaticKey: retaining Just
  // Fingerprint here makes Lynx see a dynamic component instead of the static
  // key carried by the COMPONENT protocol.
  if (isData(forced) && forced.tag === "Nothing") return null;
  if (isData(forced) && forced.tag === "Just" && forced.fields[0]) {
    const inner = forceFully(forced.fields[0] as Value);
    if (isData(inner) && inner.tag === "Fingerprint") return jsString(inner);
    if (isData(inner) && inner.tag === "String") return jsString(inner);
    if (typeof inner === "string" || typeof inner === "number" || typeof inner === "boolean")
      return inner;
  }
  if (isData(forced) && forced.tag === "Fingerprint") return jsString(forced);
  return unwrapJsHost(forced);
}
function hostSet(object: unknown, key: unknown, value: unknown): unknown {
  const target = unwrapJsHost(object);
  const stored = hostStore(value);
  if (target == null || (typeof target !== "object" && typeof target !== "function"))
    return stored;
  try {
    Reflect.set(target as object, jsKey(key), stored);
  } catch {
    try {
      (target as Record<PropertyKey, unknown>)[jsKey(key)] = stored;
    } catch {
      /* PrimJS native hosts reject missing or new properties */
    }
  }
  return stored;
}
function jsKey(value: unknown): string {
  try {
    return jsString(value);
  } catch {
    return "";
  }
}
function simpleForeign(javascript: string, values: unknown[]): unknown {
  const src = javascript.trim();
  if (
    /^\(\(\)\s*=>\s*\{\s*return\s+globalThis\s*;\s*\}\s*\)$/.test(src) ||
    /^\$r\s*=\s*globalThis;?$/.test(src)
  )
    return globalThis;
  if (
    /^\(\(\)\s*=>\s*\{\s*return\s+\{\}\s*;\s*\}\s*\)$/.test(src) ||
    /^\$r\s*=\s*\{\}\s*;?$/.test(src)
  )
    return {};
  if (/return\s+\$2\[\$1\]/.test(src) || /\$r\s*=\s*\$2\[\$1\]/.test(src)) {
    const object = unwrapJsHost(argAt(values, 1));
    if (object == null) return undefined;
    return prop(object, jsKey(argAt(values, 0)));
  }
  if (/\$3\[\$1\]\s*=\s*\$2/.test(src)) {
    return hostSet(argAt(values, 2), argAt(values, 0), argAt(values, 1));
  }
  if (/return\s+new\s+\$1\(\.\.\.\$2\)/.test(src))
    return Reflect.construct(argAt(values, 0) as Function, jsApplyArgList(argAt(values, 1)));
  if (/return\s+Object\.keys\(\$1\)/.test(src))
    return hostKeys(argAt(values, 0));
  if (/return\s+\$1\s*===\s*\$2/.test(src)) return argAt(values, 0) === argAt(values, 1);
  return SIMPLE_FOREIGN;
}
function ghcjsNewBody(javascript: string): string | null {
  const trimmed = javascript.trim();
  const block = trimmed.match(/^\(\s*\(([^)]*)\)\s*=>\s*\{([\s\S]*)\}\s*\)$/);
  if (block) return block[2].replace(/\$(\d+)/g, (_, index: string) => `a${index}`);
  const expr = trimmed.match(/^\(\s*\(([^)]*)\)\s*=>\s*(.+)\s*\)$/);
  if (expr && !expr[2].trim().startsWith("{"))
    return `return ${expr[2].replace(/\$(\d+)/g, (_, index: string) => `a${index}`)};`;
  return null;
}
export function foreignFunction(javascript: string, arity: number): unknown {
  const invoke = (args: Thunk[]): unknown => {
    const expression = javascript.replace(
      /\$(\d+)/g,
      (_, index: string) => `a${index}`,
    );
    if (javascript.includes("ghcjs-newEmptyMVar"))
      return { queue: [], waiters: [] };
    if (javascript.includes("ghcjs-takeMVar")) {
      const m = asMVar(args[0]);
      if (m.queue.length) return m.queue.shift();
      throw new Parked((resume) => {
        m.waiters.push(() => resume(m.queue.shift()));
      });
    }
    if (javascript.includes("ghcjs-readMVar")) {
      const m = asMVar(args[0]);
      if (m.queue.length) return m.queue[0];
      throw new Parked((resume) => {
        m.waiters.push(() => resume(m.queue[0]));
      });
    }
    if (javascript.includes("ghcjs-putMVar")) {
      const m = asMVar(args[0]);
      m.queue.push(forceFully(args[1]));
      wakeMVar(m);
      return prelude.unit;
    }
    if (javascript.includes("ghcjs-tryPutMVar")) {
      const m = asMVar(args[0]);
      if (m.queue.length) return prelude.false;
      m.queue.push(forceFully(args[1]));
      wakeMVar(m);
      return prelude.true;
    }
    if (javascript.includes("ghcjs-threadDelay")) {
      const ms = Math.max(0, Number(forceFully(args[0])) / 1000);
      if (!(ms > 0)) return prelude.unit;
      // GHC's JS backend delays a thread with setTimeout for the requested
      // number of microseconds (h$delayThread). There is no host-specific
      // branch: a Lynx special case that parks on requestAnimationFrame
      // ignores the requested delay entirely, so a 50ms retry loop fires
      // every frame instead.
      if (typeof setTimeout !== "function")
        throw new Parked((resume) => resume(prelude.unit));
      throw new Parked((resume) => setTimeout(() => resume(prelude.unit), ms));
    }
    // GHCJS `requestAnimationFrame` is a JS host call: the argument is a
    // JavaScript function that receives a numeric timestamp.  Haskell
    // `Function`/`JSVal` wrappers must be unwrapped; calling via `apply`
    // would pass a thunk and skip `putMVar` in Miso's rAF callback.
    if (/requestAnimationFrame/.test(expression)) {
      const callback = unwrapCallable(args[0]);
      if (typeof callback !== "function")
        throw new Error("requestAnimationFrame expects a callback");
      callback(0);
      return 0;
    }
    // Timers are scheduled after the current pure/effect step.  Avoid
    // treating the callback as a raw JavaScript function: generated Haskell
    // callbacks are curried and receive lazy arguments.
    if (/setTimeout\(\s*a1\s*,\s*0\s*\)/.test(expression)) {
      // GHCJS `forkIO` schedules the thread and yields.  Force the IO thunk
      // (it is not a raw JS function) on a later turn so the other Lynx
      // thread can register listeners before handshake retries run.
      const callback = force(args[0]);
      scheduleTurn(() => runFiber(callback));
      return 0;
    }
    // `new Map` is how boot Map/IntMap copy-on-write is implemented. Treating
    // that as a JavaScript boundary would marshal keys and values (including
    // record constructors) into plain objects, so later pattern matches fail.
    const convert =
      !/listToArray/.test(expression) &&
      /\.join|\.slice|\.startsWith|\.length|\.repeat|setTimeout|requestAnimationFrame/.test(expression);
    const invokesApply = /\.apply\(/.test(expression);
    const assignsJsProperty = /\$\d+\s*\[/.test(javascript);
    const jsPropertyKeys = new Set(
      [...javascript.matchAll(/\$(\d+)\s*\[\s*\$(\d+)/g)].map(
        (match) => Number(match[2]) - 1,
      ),
    );
    const lazyArgs = new Set<number>();
    if (javascript.includes("rws-run")) lazyArgs.add(0);
    if (javascript.includes("rws-censor")) lazyArgs.add(1);
    if (javascript.includes("io-catch")) lazyArgs.add(0);
    const values = args.map((arg, index) => {
      if (lazyArgs.has(index)) return arg;
      if (
        index === 0 &&
        /\$2\.has\(\$1\)|copy\.set\(\$1|copy\.delete\(\$1/.test(javascript)
      ) {
        let key: unknown = forceFully(arg);
        for (let depth = 0; depth < 4; depth++) {
          if (typeof key === "number" || typeof key === "string") return key;
          if (!isData(key) || key.fields?.length !== 1) break;
          key = forceFully(key.fields[0] as Value);
        }
      }
      if (jsPropertyKeys.has(index)) {
        const forced = forceFully(arg);
        return typeof forced === "number" ? forced : jsString(arg);
      }
      const converted =
        convert || (invokesApply && index === 2)
          ? toJavaScript(arg)
          : invokesApply && index === 0
            ? unwrapCallable(arg)
            : forceFully(arg);
      if (invokesApply && index === 0 && typeof converted === "function")
        return converted;
      return typeof converted === "function" && (convert || assignsJsProperty)
        ? jsCallback(converted)
        : converted;
    });
    if (invokesApply) {
      const fn = values[0];
      const argv = jsApplyArgList(values[2]);
      if (typeof fn !== "function") return undefined;
      return Function.prototype.apply.call(
        fn as Function,
        unwrapJsHost(values[1]),
        argv,
      );
    }
    const simple = simpleForeign(javascript, values);
    if (simple !== SIMPLE_FOREIGN) return simple;
    const parameterNames = values.map((_, index) => `a${index + 1}`);
    const unwrapped = ghcjsNewBody(javascript);
    const callbackStyle = unwrapped == null && /^\(\s*\(/.test(javascript.trim());
    const functionBody = javascript.includes("$r")
      ? `let __r; ${javascript
          .replace(/\$r\b/g, "__r")
          .replace(/\$(\d+)/g, (_, index: string) => `a${index}`)
          .replace(/\r/g, "\\r")
          .replace(/\n/g, "\\n")}; return __r;`
      : unwrapped != null
        ? unwrapped.replace(/\r/g, "\\r").replace(/\n/g, "\\n")
        : callbackStyle
          ? `return (${expression.replace(/\r/g, "\\r").replace(/\n/g, "\\n")})(${parameterNames.join(", ")});`
          : `return (${expression.replace(/\r/g, "\\r").replace(/\n/g, "\\n")});`;
    let result: unknown;
    try {
      result = Function(
        ...parameterNames,
        "force",
        "lazy",
        "apply",
        "listToArray",
        "listFromArray",
        "jsString",
        "rws",
        functionBody,
      )(...values, force, lazy, apply, listToArray, listFromArray, jsString, rws);
    } catch (cause) {
      console.error("[ghcts foreign]", javascript, cause);
      throw cause;
    }
    return !callbackStyle && unwrapped == null && typeof result === "function"
      ? result(...values)
      : result;
  };
  const collect = (args: Thunk[]): unknown =>
    args.length === arity
      ? invoke(args)
      : (argument: Thunk) => collect([...args, argument]);
  return collect([]);
}
export function isTrue(value: unknown): boolean {
  const forced = force(value as Value);
  const tag = prop(forced, "tag");
  if (typeof tag === "string") return tag === "True";
  return Boolean(forced);
}
function equalValue(left: unknown, right: unknown): boolean {
  const a = force(left as Value);
  const b = force(right as Value);
  if (Object.is(a, b)) return true;
  const boolA = asBool(a);
  const boolB = asBool(b);
  if (boolA && boolB) return boolA.tag === boolB.tag;
  if (
    typeof a !== "object" ||
    a === null ||
    typeof b !== "object" ||
    b === null
  )
    return false;
  const tagA = prop(a, "tag");
  const tagB = prop(b, "tag");
  const fieldsA = prop(a, "fields");
  const fieldsB = prop(b, "fields");
  if (
    typeof tagA !== "string" ||
    tagA !== tagB ||
    !Array.isArray(fieldsA) ||
    !Array.isArray(fieldsB) ||
    fieldsA.length !== fieldsB.length
  )
    return false;
  return fieldsA.every((fieldValue, index) =>
    equalValue(fieldValue, fieldsB[index]),
  );
}
function appendList(left: unknown, right: unknown): unknown {
  const value = force(left as Value) as DataValue;
  // A Haskell `String` (`[Char]`) is represented as a plain JS string here
  // (see `jStr` in compiler.ts), not as a cons-list, for performance - but
  // `++`/`appendList` only ever expected the cons-list shape, so ordinary
  // string concatenation like `"a" ++ "b"` threw "expected matching
  // Semigroup values" instead of just joining the two strings. `<>`
  // (`appendValue`) already handles this case; mirror it here so `++`
  // (by far the more common way Haskell code joins strings) does too.
  if (typeof value === "string") {
    const other = force(right as Value);
    if (typeof other === "string") return value + other;
  }
  const tag = prop(value, "tag");
  const fields = prop(value, "fields");
  if (tag === "[]") return force(right as Value);
  if (tag !== ":" || !Array.isArray(fields))
    throw new Error("(<>) expected matching Semigroup values");
  return {
    tag: ":",
    fields: [fields[0], lazy(() => appendList(fields[1], right))],
  } satisfies DataValue;
}
function appendSeq(left: unknown, right: unknown): unknown {
  const value = force(left as Value) as DataValue;
  const tag = prop(value, "tag");
  const fields = prop(value, "fields");
  if (tag === "Empty") return force(right as Value);
  if (tag !== "Cons" || !Array.isArray(fields))
    throw new Error("(<>) expected matching Semigroup values");
  return {
    tag: "Cons",
    fields: [fields[0], lazy(() => appendSeq(fields[1], right))],
  } satisfies DataValue;
}
function tryBinaryInstance(
  className: string,
  method: string,
  left: unknown,
  right: unknown,
): unknown | undefined {
  const tag = prop(left, "tag");
  if (typeof tag !== "string") return undefined;
  const typeName = constructorTypes.get(tag) ?? tag;
  for (const inst of instanceTable) {
    if (inst.className !== className || inst.method !== method) continue;
    const head = inst.headName;
    if (head !== typeName && head !== tag && inst.target !== typeName) continue;
    try {
      return force(
        apply(
          apply(force(inst.impl as Value), lazy(() => left)),
          lazy(() => right),
        ) as Value,
      );
    } catch {
      continue;
    }
  }
  return undefined;
}
function appendValue(left: unknown, right: unknown): unknown {
  // Monoid values frequently arrive through a polymorphic `concat` call.
  // GHCJS's representation may leave an additional indirection at that
  // boundary (notably for Map-valued foreign imports), so normalize the
  // value completely before selecting the representation-specific append.
  const a = forceFully(left as Value);
  const b = forceFully(right as Value);
  // Some boot-library collection values use the historical empty-string
  // sentinel for `mempty` while the populated value is a JS object.
  if (a === "") return b;
  if (b === "") return a;
  // A few GHCJS boot representations expose a singleton map as its key/value
  // pair at the JS boundary. Preserve that pair as a host object so a later
  // map append can combine it normally.
  if (typeof a === "string" && typeof b === "object" && b !== null)
    return { [a]: b };
  if (typeof a === "string" && typeof b === "string") return a + b;
  if (
    (typeof a === "string" || typeof a === "number" || typeof a === "boolean") &&
    (typeof b === "string" || typeof b === "number" || typeof b === "boolean")
  )
    return String(a) + String(b);
  if (a instanceof Map && b instanceof Map) return new Map([...a, ...b]);
  // Cross-realm JS hosts (including embedded runtimes) may not satisfy this
  // realm's `instanceof Map`, but retain the standard Map protocol.
  if (
    typeof a === "object" && a !== null && typeof b === "object" && b !== null &&
    typeof (a as { entries?: unknown }).entries === "function" &&
    typeof (b as { entries?: unknown }).entries === "function"
  ) return new Map([...(a as Map<unknown, unknown>).entries(), ...(b as Map<unknown, unknown>).entries()]);
  if (
    typeof a === "object" && a !== null &&
    typeof b === "object" && b !== null &&
    !Array.isArray(a) && !Array.isArray(b) &&
    prop(a, "tag") === undefined && prop(b, "tag") === undefined
  ) return { ...(a as object), ...(b as object) };
  if (Array.isArray(a) && Array.isArray(b)) return [...a, ...b];
  const tag = prop(a, "tag");
  if (tag === "[]" || tag === ":") return appendList(a, b);
  if (tag === "Empty" || tag === "Cons") return appendSeq(a, b);
  const dispatched = tryBinaryInstance("Semigroup", "<>", a, b);
  if (dispatched !== undefined) return dispatched;
  throw new Error(
    `(<>) has no runtime Semigroup implementation for these values (${typeof a}, ${String(prop(a, "tag") ?? "no-tag")}; ${typeof b}, ${String(prop(b, "tag") ?? "no-tag")})`,
  );
}
function firstAlternative(left: unknown, right: unknown): unknown {
  const value = force(left as Value);
  const tag = prop(value, "tag");
  if (tag === "Nothing" || tag === "[]") return force(right as Value);
  return value;
}
export const prelude = {
  nil: { tag: "[]", fields: [] } satisfies DataValue,
  cons: (head: Thunk) => (tail: Thunk) =>
    ({ tag: ":", fields: [head, tail] }) satisfies DataValue,
  true: { tag: "True", fields: [] } satisfies DataValue,
  false: { tag: "False", fields: [] } satisfies DataValue,
  nothing: { tag: "Nothing", fields: [] } satisfies DataValue,
  just: (value: Thunk) =>
    ({ tag: "Just", fields: [value] }) satisfies DataValue,
  left: (value: Thunk) =>
    ({ tag: "Left", fields: [value] }) satisfies DataValue,
  right: (value: Thunk) =>
    ({ tag: "Right", fields: [value] }) satisfies DataValue,
  unit: { tag: "()", fields: [] } satisfies DataValue,
  pair: (left: Thunk) => (right: Thunk) => tuple([left, right]),
  otherwise: true,
  and: (a: Thunk) => (b: Thunk) =>
    isTrue(a) && isTrue(b) ? prelude.true : prelude.false,
  or: (a: Thunk) => (b: Thunk) =>
    isTrue(a) || isTrue(b) ? prelude.true : prelude.false,
  not: (value: Thunk) => (isTrue(value) ? prelude.false : prelude.true),
  add: (a: Thunk) => (b: Thunk) => Number(force(a)) + Number(force(b)),
  subtract: (a: Thunk) => (b: Thunk) => Number(force(a)) - Number(force(b)),
  subtractFunction: (a: Thunk) => (b: Thunk) =>
    Number(force(a)) - Number(force(b)),
  multiply: (a: Thunk) => (b: Thunk) => Number(force(a)) * Number(force(b)),
  divide: (a: Thunk) => (b: Thunk) => Number(force(a)) / Number(force(b)),
  equal: (a: Thunk) => (b: Thunk) => equalValue(a, b),
  notEqual: (a: Thunk) => (b: Thunk) => !equalValue(a, b),
  append: (a: Thunk) => (b: Thunk) => appendValue(a, b),
  // The polymorphic identity for the initial runtime representation is the
  // empty lazy list. Typed-Core dictionary selection replaces this with a
  // class-specific identity (for example Text or Map) when evidence exists.
  // Polymorphic 'mempty' is an empty Map: Miso (and the boot Map/IntMap
  // libraries) construct containers with mempty, while empty lists are
  // written `[]` and use prelude.nil.
  empty: new Map(),
  emptyQueue: { tag: "Queue", fields: [lazy(() => new Map()), lazy(() => ({ tag: "Empty", fields: [] } as DataValue))], fieldNames: ["_queue", "_queueSchedule"] } satisfies DataValue,
  wait: (_mvar: Thunk) => prelude.unit,
  forever: (action: Thunk) => {
    const step = () => {
      try {
        force(action);
      } catch (cause) {
        if (isParked(cause)) {
          cause.wait((value) => {
            scheduleTurn(() => {
              void value;
              scheduleTurn(step);
            });
          });
          return;
        }
        scheduleTurn(() => {
          throw cause;
        });
        return;
      }
      scheduleTurn(step);
    };
    scheduleTurn(step);
    return prelude.unit;
  },
  concat: (values: Thunk) => {
    // The boot Monoid fallback represents an empty collection as `""`.
    // Treat that sentinel as identity when concatenating a heterogeneous
    // list of host-backed values (for example cross-realm Maps).
    const items = listToArray(values).filter((item) => force(item as Value) !== "");
    if (!items.length) return "";
    return items.slice(1).reduce(
      (result, value) => appendValue(result, value),
      items[0],
    );
  },
  alternative: (a: Thunk) => (b: Thunk) => firstAlternative(a, b),
  replace: (value: Thunk) => (_context: Thunk) => force(value),
  keepLeft: (left: Thunk) => (right: Thunk) => {
    const result = force(left);
    force(right);
    return result;
  },
  keepRight: (left: Thunk) => (right: Thunk) => {
    try {
      force(left);
    } catch (cause) {
      if (isParked(cause)) chainPark(cause, () => force(right));
      throw cause;
    }
    return force(right);
  },
  applyF: (fn: Thunk) => (value: Thunk) => {
    const f = force(fn);
    const x = force(value);
    if (isData(f) && f.tag === "Nothing") return f;
    if (typeof f === "function") return apply(lazy(() => f), lazy(() => x));
    if (isData(f) && f.tag === "Just") {
      if (isData(x) && x.tag === "Nothing") return x;
      const inner = force(f.fields[0]);
      if (typeof inner === "function") {
        const argument =
          isData(x) && x.tag === "Just" ? x.fields[0] : lazy(() => x);
        return {
          tag: "Just",
          fields: [lazy(() => apply(lazy(() => inner), argument as Thunk))],
        } satisfies DataValue;
      }
    }
    if (isData(f) && f.tag === "[]") return x;
    return x;
  },
  appendList: (left: Thunk) => (right: Thunk) => appendList(left, right),
  flatten: (values: Thunk) =>
    listToArray(values).reduce(
      (result, value) => appendList(result, value),
      prelude.nil,
    ),
  less: (a: Thunk) => (b: Thunk) => Number(force(a)) < Number(force(b)),
  greater: (a: Thunk) => (b: Thunk) => Number(force(a)) > Number(force(b)),
  lessEqual: (a: Thunk) => (b: Thunk) => Number(force(a)) <= Number(force(b)),
  greaterEqual: (a: Thunk) => (b: Thunk) =>
    Number(force(a)) >= Number(force(b)),
  putStrLn: (text: Thunk) => console.log(String(force(text))),
  error: (message: Thunk): never => {
    throw new Error(String(force(message)));
  },
  round: (value: Thunk) => Math.round(Number(force(value))),
  negate: (value: Thunk) => -Number(force(value)),
  // The first backend keeps IO actions direct.  These combinators provide
  // the same sequencing contract while the browser scheduler supplies the
  // asynchronous execution layer.
  pure: (value: Thunk) => force(value),
  bind: (action: Thunk) => (next: Thunk) =>
    forceBind(action, (result) =>
      force(apply(force(next), lazy(() => result)) as Value),
    ),
  then: (first: Thunk) => (second: Thunk) => {
    try {
      force(first);
    } catch (cause) {
      if (isParked(cause)) chainPark(cause, () => force(second));
      throw cause;
    }
    return force(second);
  },
  map: (fn: Thunk) => (list: Thunk) => {
    const value = force(list);
    const tag = prop(value, "tag");
    const fields = prop(value, "fields");
    if (tag === "[]") return prelude.nil;
    if (tag !== ":" || !Array.isArray(fields)) throw new Error("map expected a list");
    return {
      tag: ":",
      fields: [
        lazy(() => apply(fn, fields[0])),
        lazy(() =>
          (prelude.map as (f: Thunk) => (xs: Thunk) => unknown)(fn)(
            fields[1],
          ),
        ),
      ],
    } satisfies DataValue;
  },
  fmap: (fn: Thunk) => (value: Thunk) => {
    const forced = force(value) as any;
    const tag = prop(forced, "tag");
    const fields = prop(forced, "fields");
    // A bare JS string is a MisoString/JSString - an opaque scalar at the
    // FFI boundary, not a [Char]. Haskell's own String is a cons list here
    // (see listFromArray/showValue), so a JS string reaching fmap can only
    // be the FFI representation, and mapping over its characters is never
    // what the Functor dictionary would have chosen. Real GHC picks that
    // dictionary from the type at compile time; ghcts has to fall through
    // to the scalar case below and apply fn to the whole value.
    //
    // Concretely: Miso's `instance FromJSVal COMPONENT` does
    // `fmap fromMisoString <$> msk` on a 32-char hex StaticKey. Splitting
    // it produced a 32-element char list where digits parsed back to
    // numbers, so componentListener's `case ... of Nothing/Just` saw a
    // cons cell and died with "Non-exhaustive patterns in case: :".
    if (tag === "[]") {
      const mappedWhole = apply(fn, value);
      const result = force(mappedWhole);
      if (typeof result === "function") return result;
      return prelude.nil;
    }
    if (tag === ":")
      return (prelude.map as any)(fn)(value);
    if (tag === "Nothing") return forced;
    if (tag === "Just" && Array.isArray(fields))
      return {
        tag: "Just",
        fields: [lazy(() => apply(fn, fields[0]))],
      } satisfies DataValue;
    return apply(fn, lazy(() => forced));
  },
  mapM_: (fn: Thunk) => (list: Thunk) => {
    for (const value of foldableToArray(list))
      force(
        apply(
          fn,
          lazy(() => value),
        ),
      );
    return prelude.unit;
  },
  forM_: (list: Thunk) => (fn: Thunk) => {
    for (const item of foldableToArray(list)) force(apply(fn, lazy(() => item)));
    return prelude.unit;
  },
  reverse: (list: Thunk) => {
    const value: any = force(list);
    const tag = prop(value, "tag");
    if (!value || (tag !== "[]" && tag !== ":")) return prelude.nil;
    return listFromArray(listToArray(value).reverse());
  },
  drop: (count: Thunk) => (list: Thunk) => {
    const n = Math.max(0, Number(force(count)) || 0);
    const value: any = force(list);
    const tag = prop(value, "tag");
    if (!value || (tag !== "[]" && tag !== ":")) return prelude.nil;
    return listFromArray(listToArray(value).slice(n));
  },
  dropWhile: (predicate: Thunk) => (list: Thunk) => {
    const forced = force(list);
    if (typeof forced === "string") {
      let index = 0;
      while (
        index < forced.length &&
        isTrue(apply(predicate, lazy(() => forced[index])))
      )
        index += 1;
      return forced.slice(index);
    }
    let current = forced as DataValue;
    while (current && current.tag === ":") {
      if (!isTrue(apply(predicate, current.fields[0]))) return current;
      current = force(current.fields[1]) as DataValue;
    }
    return current ?? prelude.nil;
  },
  sequence_: (list: Thunk) => {
    for (const action of foldableToArray(list)) force(action);
    return prelude.unit;
  },
  maybe: (fallback: Thunk) => (onJust: Thunk) => (value: Thunk) => {
    const option = force(value) as DataValue;
    return option.tag === "Nothing"
      ? force(fallback)
      : option.tag === "Just"
        ? apply(onJust, option.fields[0])
        : (() => {
            throw new Error("maybe expected Maybe");
          })();
  },
  either: (onLeft: Thunk) => (onRight: Thunk) => (value: Thunk) => {
    const choice = force(value) as DataValue;
    return choice.tag === "Left"
      ? apply(onLeft, choice.fields[0])
      : choice.tag === "Right"
        ? apply(onRight, choice.fields[0])
        : (() => {
            throw new Error("either expected Either");
          })();
  },
  foldr: (fn: Thunk) => (initial: Thunk) => (list: Thunk) => {
    const value = force(list) as DataValue;
    if (value.tag === "[]") return force(initial);
    if (value.tag !== ":") throw new Error("foldr expected a list");
    return apply(
      apply(fn, value.fields[0]),
      lazy(() =>
        (prelude.foldr as (f: Thunk) => (z: Thunk) => (xs: Thunk) => unknown)(
          fn,
        )(initial)(value.fields[1]),
      ),
    );
  },
  fromIntegral: (value: Thunk) => Number(force(value)),
  realToFrac: (value: Thunk) => Number(force(value)),
  isNaN: (value: Thunk) => Number.isNaN(Number(force(value))),
  fst: (value: Thunk) => force((force(value) as DataValue).fields[0]),
  snd: (value: Thunk) => force((force(value) as DataValue).fields[1]),
  index: (list: Thunk) => (n: Thunk) => {
    const i = Number(force(n));
    if (!Number.isInteger(i) || i < 0)
      throw new Error("Prelude.!!: negative index");
    const forced = force(list) as any;
    if (typeof forced === "string") {
      if (i >= forced.length) throw new Error("Prelude.!!: index too large");
      return forced[i];
    }
    let current = forced as DataValue;
    let k = 0;
    while (current && (current.tag === ":" || current.tag === "Cons")) {
      if (k === i) return force(current.fields[0]);
      k += 1;
      current = force(current.fields[1]) as DataValue;
    }
    throw new Error("Prelude.!!: index too large");
  },
  last: (value: Thunk) => {
    const forced = force(value) as any;
    if (typeof forced === "string") {
      if (forced.length === 0) throw new Error("last: empty list");
      return forced[forced.length - 1];
    }
    let current = forced as DataValue;
    if (!current || current.tag === "[]" || current.tag === "Empty")
      throw new Error("last: empty list");
    while (current.tag === ":" || current.tag === "Cons") {
      const next = force(current.fields[1]) as DataValue;
      if (next.tag === "[]" || next.tag === "Empty") return force(current.fields[0]);
      current = next;
    }
    throw new Error("last: malformed list");
  },
  init: (value: Thunk) => {
    const forced = force(value) as any;
    if (typeof forced === "string") {
      if (forced.length === 0) throw new Error("init: empty list");
      return forced.slice(0, -1);
    }
    const walk = (node: DataValue): unknown => {
      if (!node || (node.tag !== ":" && node.tag !== "Cons"))
        throw new Error("init: malformed list");
      const next = force(node.fields[1]) as DataValue;
      if (next.tag === "[]" || next.tag === "Empty") return next;
      return {
        tag: node.tag,
        fields: [node.fields[0], lazy(() => walk(next))],
      } satisfies DataValue;
    };
    let current = forced as DataValue;
    if (!current || current.tag === "[]" || current.tag === "Empty")
      throw new Error("init: empty list");
    return walk(current);
  },
  isNull: (value: Thunk) => {
    const forced = force(value) as any;
    if (forced == null) return true;
    if (typeof forced === "string" || Array.isArray(forced)) return forced.length === 0;
    if (forced instanceof Map) return forced.size === 0;
    if (isData(forced) && (forced.tag === "[]" || forced.tag === "Empty")) return true;
    if (isData(forced) && (forced.tag === ":" || forced.tag === "Cons")) return false;
    return false;
  },
  length: (value: Thunk) => {
    const forced = force(value) as any;
    if (typeof forced === "string" || Array.isArray(forced)) return forced.length;
    if (forced instanceof Map) return forced.size;
    if (isData(forced) && (forced.tag === "[]" || forced.tag === "Empty")) return 0;
    if (isData(forced) && (forced.tag === ":" || forced.tag === "Cons")) {
      let count = 0;
      let current = forced as DataValue;
      while (current.tag === ":" || current.tag === "Cons") {
        count += 1;
        current = force(current.fields[1]) as DataValue;
      }
      return count;
    }
    return Number(forced?.length ?? 0);
  },
  foldlPrime: (fn: Thunk) => (initial: Thunk) => (values: Thunk) => {
    let acc: unknown = force(initial);
    const step = (item: unknown) => {
      acc = apply(
        apply(fn, lazy(() => acc)),
        lazy(() => item),
      );
    };
    const walk = (xs: unknown) => {
      const value: any = force(xs as Value);
      if (value == null) return;
      if (Array.isArray(value)) {
        value.forEach(step);
        return;
      }
      if (isData(value) && (value.tag === "[]" || value.tag === "Empty")) return;
      if (isData(value) && (value.tag === ":" || value.tag === "Cons")) {
        step(force(value.fields[0]));
        walk(value.fields[1]);
      }
    };
    walk(values);
    return acc;
  },
  toList: (value: Thunk) => force(value),
  isSpace: (value: Thunk) => /^\s$/.test(String(force(value))),
  traverse: (fn: Thunk) => (value: Thunk) => mapMList(fn, value),
  show: (value: Thunk) => showValue(value, 0),
  toJSON: (value: Thunk) => {
    const forced = force(value);
    if (isData(forced) && derivedJsonByConstructor.has(forced.tag))
      return encodeDerived(forced);
    return jsValue(value);
  },
  ord: (value: Thunk) => String(force(value)).charCodeAt(0),
  fromEnum: (value: Thunk) => String(force(value)).charCodeAt(0),
  sum: (values: Thunk) =>
    listToArray(values).reduce(
      (total: number, value) => total + Number(force(value as Thunk)),
      0,
    ),
  elem: (needle: Thunk) => (values: Thunk) =>
    listToArray(values).some((value) => equalValue(needle, value)),
  filter: (predicate: Thunk) => (values: Thunk) => {
    const go = (list: Thunk): DataValue => {
      const value = force(list) as DataValue;
      if (!value || value.tag !== ":") return prelude.nil as DataValue;
      const rest = lazy(() => go(value.fields[1]));
      return isTrue(apply(predicate, value.fields[0]))
        ? { tag: ":", fields: [value.fields[0], rest] }
        : force(rest);
    };
    return go(values);
  },
  // Haskell's `div`/`mod` round toward negative infinity (floor division),
  // unlike `quot`/`rem`, which truncate toward zero like JS's `/`/`%` and
  // most other languages' integer division. `Math.trunc` here would give
  // `quot`/`rem` semantics instead - e.g. `(-7) \`div\` 2` must be -4, not
  // -3 (`Math.trunc(-7/2)`).
  div: (left: Thunk) => (right: Thunk) =>
    Math.floor(Number(force(left)) / Number(force(right))),
  mod: (left: Thunk) => (right: Thunk) => {
    const n = Number(force(left));
    const d = Number(force(right));
    return n - d * Math.floor(n / d);
  },
  // `quot`/`rem` truncate toward zero (JS's native `/`/`%`), unlike
  // `div`/`mod` above - the pair Haskell code reaches for when it wants
  // rounding to match most other languages' integer division.
  quot: (left: Thunk) => (right: Thunk) =>
    Math.trunc(Number(force(left)) / Number(force(right))),
  rem: (left: Thunk) => (right: Thunk) =>
    Number(force(left)) % Number(force(right)),
  quotRem: (left: Thunk) => (right: Thunk) => {
    const n = Number(force(left));
    const d = Number(force(right));
    const q = Math.trunc(n / d);
    return { tag: "(,)", fields: [lazy(() => q), lazy(() => n - d * q)] };
  },
  even: (value: Thunk) => Number(force(value)) % 2 === 0,
  odd: (value: Thunk) => Number(force(value)) % 2 !== 0,
  min: (left: Thunk) => (right: Thunk) => {
    const a = force(left);
    const b = force(right);
    return Number(a) <= Number(b) ? a : b;
  },
  max: (left: Thunk) => (right: Thunk) => {
    const a = force(left);
    const b = force(right);
    return Number(a) >= Number(b) ? a : b;
  },
  // ghcts has no per-type Bounded dispatch (this constant answers every
  // minBound/maxBound call regardless of type), so it must match Int - by
  // far the most common Bounded use in real Haskell source (e.g. Miso's
  // `Nothing -> ... minBound minBound ...` sentinel component ids).
  // GHC's *JS backend* (GHC.StgToJS.Prim) represents Int/Word as ordinary
  // 32-bit-truncated JS numbers, not 64-bit machine words: IntAddOp/etc.
  // wrap results with `toI32`/`.>>>. 0`, and GHC.StgToJS.Literal's genLit
  // gives a plain LitNumInt a single untouched JS number - only the
  // explicitly-sized Int64/Word64 literals get the two-JS-value hi/lo
  // split. So Int's real range under GHCJS (the target ghcts matches) is
  // the 32-bit range, matching JS's native bitwise-op width.
  minBound: -2147483648,
  maxBound: 2147483647,
  succ: (value: Thunk) => Number(force(value)) + 1,
  pred: (value: Thunk) => Number(force(value)) - 1,
  divMod: (left: Thunk) => (right: Thunk) => {
    const n = Number(force(left));
    const d = Number(force(right));
    const q = Math.floor(n / d);
    return { tag: "(,)", fields: [lazy(() => q), lazy(() => n - d * q)] };
  },
  any: (predicate: Thunk) => (values: Thunk) =>
    listToArray(values).some((value) =>
      isTrue(
        apply(
          predicate,
          lazy(() => value),
        ),
      ),
    ),
  concatMap: (mapper: Thunk) => (values: Thunk) =>
    listToArray(values).reduce(
      (out, value) =>
        appendList(
          out,
          apply(
            mapper,
            lazy(() => value),
          ),
        ),
      prelude.nil,
    ),
  zip: (left: Thunk) => (right: Thunk) => {
    const pair = (as: Thunk, bs: Thunk): DataValue => {
      const a = force(as) as DataValue;
      const b = force(bs) as DataValue;
      if (!a || a.tag !== ":" || !b || b.tag !== ":")
        return prelude.nil as DataValue;
      return {
        tag: ":",
        fields: [
          lazy(() => ({
            tag: "(,)",
            fields: [a.fields[0], b.fields[0]],
          })),
          lazy(() => pair(a.fields[1], b.fields[1])),
        ],
      };
    };
    return pair(left, right);
  },
  enumFrom: (start: Thunk) => {
    const from = (n: number): DataValue => ({
      tag: ":",
      fields: [lazy(() => n), lazy(() => from(n + 1))],
    });
    return from(Number(force(start)));
  },
  enumFromTo: (start: Thunk) => (end: Thunk) => {
    const from = (n: number, last: number): DataValue =>
      n > last
        ? (prelude.nil as DataValue)
        : {
            tag: ":",
            fields: [lazy(() => n), lazy(() => from(n + 1, last))],
          };
    return from(Number(force(start)), Number(force(end)));
  },
  enumFromThen: (start: Thunk) => (next: Thunk) => {
    const first = Number(force(start));
    const step = Number(force(next)) - first;
    const from = (n: number): DataValue => ({
      tag: ":",
      fields: [lazy(() => n), lazy(() => from(n + step))],
    });
    return from(first);
  },
  enumFromThenTo: (start: Thunk) => (next: Thunk) => (end: Thunk) => {
    const first = Number(force(start));
    const second = Number(force(next));
    const last = Number(force(end));
    const step = second - first;
    const done = (n: number) => (step >= 0 ? n > last : n < last);
    const from = (n: number): DataValue =>
      done(n)
        ? (prelude.nil as DataValue)
        : {
            tag: ":",
            fields: [lazy(() => n), lazy(() => from(n + step))],
          };
    return from(first);
  },
  mapM: (mapper: Thunk) => (values: Thunk) => mapMList(mapper, values),
  forM: (values: Thunk) => (mapper: Thunk) => mapMList(mapper, values),
  sequence: (values: Thunk) => {
    const results: unknown[] = [];
    for (const action of foldableToArray(values)) results.push(force(action as Thunk));
    return listFromArray(results);
  },
  traverse_: (mapper: Thunk) => (values: Thunk) => {
    for (const value of foldableToArray(values))
      force(
        apply(
          mapper,
          lazy(() => value),
        ),
      );
    return prelude.unit;
  },
  uncurry: (fn: Thunk) => (pair: Thunk) =>
    apply(
      apply(
        fn,
        lazy(() => (force(pair) as DataValue).fields[0]),
      ),
      lazy(() => (force(pair) as DataValue).fields[1]),
    ),
  seq: (first: Thunk) => (second: Thunk) => {
    force(first);
    return force(second);
  },
  pipe: (value: Thunk) => (fn: Thunk) => apply(fn, value),
  dollar: (fn: Thunk) => (value: Thunk) => apply(fn, value),
  bindFlip: (next: Thunk) => (action: Thunk) =>
    apply(apply(prelude.bind as unknown as Thunk, action), next),
  id: (value: Thunk) => force(value),
  toMisoString: (value: Thunk) => jsString(value),
  staticPtr: (value: Thunk) => staticPtr(value),
  staticPtrStable: (key: Thunk) => (value: Thunk) => staticPtr(value, jsString(key)),
  deRefStaticPtr: (value: Thunk) => deRefStaticPtr(value),
  staticKey: (value: Thunk) => staticKeyValue(value),
  unsafeLookupStaticPtr: (value: Thunk) => unsafeLookupStaticPtrValue(value),
  readMaybe: (value: Thunk) => {
    const text = jsString(value).trim();
    if (!text) return prelude.nothing;
    const parsed = Number(text);
    if (Number.isNaN(parsed)) return prelude.nothing;
    return prelude.just(lazy(() => parsed));
  },
  fromMisoStringEither: (value: Thunk) => fromMisoStringEitherValue(value),
  parseJSON: (value: Thunk) => {
    const forced = force(value) as DataValue | undefined;
    const ok = (payload: unknown) =>
      ({
        tag: "Parser",
        fieldNames: ["unParser"],
        fields: [lazy(() => prelude.right(lazy(() => payload)))],
      }) satisfies DataValue;
    if (isData(forced) && forced.tag === "String" && forced.fields[0]) {
      const text = jsString(forced.fields[0]);
      const spec = derivedJsonByConstructor.get(text);
      if (spec?.allNullary) return ok({ tag: text, fields: [] } satisfies DataValue);
      return ok(text);
    }
    if (isData(forced) && forced.tag === "Number" && forced.fields[0])
      return ok(force(forced.fields[0] as Value));
    if (isData(forced) && forced.tag === "Bool" && forced.fields[0])
      return ok(force(forced.fields[0] as Value));
    if (isData(forced) && forced.tag === "True") return ok(true);
    if (isData(forced) && forced.tag === "False") return ok(false);
    if (isData(forced) && (forced.tag === "Object" || forced.tag === "Array")) {
      const decoded = decodeDerived(forced);
      if (decoded !== forced) return ok(decoded);
    }
    return ok(forced);
  },
  compose: (g: Thunk) => (f: Thunk) => {
    const left = forceFully(g);
    const right = forceFully(f);
    if (isData(left) && left.tag === "Lens" && isData(right) && right.tag === "Lens")
      return {
        tag: "Lens",
        fieldNames: ["_get", "_set"],
        fields: [
          lazy(
            () => (record: Thunk) =>
              apply(
                field(right, "_get"),
                lazy(() => apply(field(left, "_get"), record)),
              ),
          ),
          lazy(
            () => (value: Thunk) => (record: Thunk) =>
              apply(
                apply(
                  field(left, "_set"),
                  lazy(() =>
                    apply(
                      apply(field(right, "_set"), value),
                      lazy(() => apply(field(left, "_get"), record)),
                    ),
                  ),
                ),
                record,
              ),
          ),
        ],
      } satisfies DataValue;
    return (value: Thunk) =>
      apply(
        left,
        lazy(() => apply(right, value)),
      );
  },
  at: (key: Thunk) => {
    const k = forceFully(key);
    return {
      tag: "Lens",
      fieldNames: ["_get", "_set"],
      fields: [
        lazy(() => (container: Thunk) => {
          const map = forceFully(container) as Map<unknown, unknown>;
          if (map && typeof map.has === "function")
            return map.has(k)
              ? ({ tag: "Just", fields: [lazy(() => map.get(k))] } satisfies DataValue)
              : prelude.nothing;
          return prelude.nothing;
        }),
        lazy(() => (value: Thunk) => (container: Thunk) => {
          const map = forceFully(container) as Map<unknown, unknown>;
          const next = new Map(map);
          const replacement = forceFully(value) as DataValue;
          if (!replacement || replacement.tag === "Nothing") next.delete(k);
          else next.set(k, forceFully(replacement.fields[0] as Value));
          return next;
        }),
      ],
    } satisfies DataValue;
  },
  undefined: undefined,
  toJSVal: (value: Thunk): unknown => {
    const forced = force(value);
    // GHCJS represents GHC.Fingerprint (and therefore StaticKey) at the JS
    // boundary as its 32-hex-digit string, not as the internal constructor
    // object. This is required by unsafeLookupStaticPtr and cross-thread
    // protocols that carry staticKey values.
    if (isData(forced) && forced.tag === "Fingerprint") return jsString(forced);
    // Match the ordinary GHCJS/Miso ToJSVal instance for Maybe: the
    // constructor is a Haskell representation detail and does not cross the
    // JavaScript boundary.  Recursing through the field also preserves the
    // element's own ToJSVal instance (for example Fingerprint -> hex text).
    if (isData(forced) && forced.tag === "Nothing") return null;
    if (isData(forced) && forced.tag === "Just")
      return forced.fields.length ? prelude.toJSVal(forced.fields[0]) : null;
    const encoded = tryMarshalInstances("ToJSVal", "toJSVal", forced);
    return encoded === undefined ? jsValue(value) : encoded;
  },
  fromJSVal: (value: Thunk) => {
    const forced = force(value);
    if (forced == null)
      return marshalStack.length
        ? prelude.just(lazy(() => prelude.nothing))
        : prelude.nothing;
    if (typeof forced === "boolean")
      return prelude.just(lazy(() => (forced ? prelude.true : prelude.false)));
    const decoded = tryMarshalInstances("FromJSVal", "fromJSVal", forced);
    if (decoded !== undefined) return decoded;
    if (
      typeof forced === "object" &&
      !isData(forced) &&
      !(forced instanceof Map) &&
      !isHostNode(forced)
    )
      return {
        tag: "Just",
        fields: [lazy(() => jsonFromJavaScript(forced))],
      } satisfies DataValue;
    return { tag: "Just", fields: [value] } satisfies DataValue;
  },
  fromJSValUnchecked: (value: Thunk) => force(value),
  toObject: (value: Thunk) => {
    const forced = force(value) as DataValue | undefined;
    if (isData(forced) && forced.tag === "Object") return forced;
    return {
      tag: "Object",
      fields: [lazy(() => jsValue(value))],
    } satisfies DataValue;
  },
  toArgs: (value: Thunk) => {
    const forced = force(value) as DataValue | undefined;
    if (!forced || typeof forced !== "object") return [jsValue(forced)];
    if (isData(forced) && forced.tag === "()") return [];
    if (isData(forced) && (forced.tag === ":" || forced.tag === "[]"))
      return listToArray(forced).map(jsValue);
    if (isData(forced) && /^\(,+\)$/.test(forced.tag))
      return forced.fields.map(jsValue);
    return [jsValue(forced)];
  },
  liftIO: (value: Thunk) => force(value),
  flip: (fn: Thunk) => (b: Thunk) => (a: Thunk) => apply(apply(fn, a), b),
  constValue: (value: Thunk) => (_ignored: Thunk) => force(value),
};
