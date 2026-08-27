#!/usr/bin/env node
/**
 * Serve packed Lynx bundles on the LAN for Lynx Explorer.
 *
 *   node scripts/host-lynx.mjs
 *   node scripts/host-lynx.mjs --port 8080
 *
 * Explorer URLs (phone and this machine must be on the same network):
 *   http://<lan-ip>:8080/counter/main.lynx.bundle
 *   http://<lan-ip>:8080/misogram/main.lynx.bundle
 */
import { createServer } from "node:http";
import { networkInterfaces } from "node:os";
import { stat } from "node:fs/promises";
import { createReadStream } from "node:fs";
import { readFile } from "node:fs/promises";
import { gzipSync } from "node:zlib";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const port = Number(process.argv.includes("--port")
  ? process.argv[process.argv.indexOf("--port") + 1]
  : 8080);

const apps = {
  "/counter/main.lynx.bundle": join(
    root,
    "references/miso-lynx/examples/dist/lynx/main.lynx.bundle",
  ),
  "/misogram/main.lynx.bundle": join(
    root,
    "references/misogram/dist/lynx/main.lynx.bundle",
  ),
  "/reference/main.lynx.bundle": join(
    root,
    "references/miso-lynx/examples/main.lynx.bundle",
  ),
  // The oracle's own lib.js/out.js driven by ghcts's generated rts.js - see
  // scripts/rts-swap.mjs. Real compiled Haskell on our RTS.
  "/rts-swap/main.lynx.bundle": join(root, "dist/rts-swap/lynx/main.lynx.bundle"),
};

const lanAddresses = () => {
  const found = [];
  for (const adapters of Object.values(networkInterfaces())) {
    for (const adapter of adapters ?? []) {
      if (adapter.family !== "IPv4" || adapter.internal) continue;
      found.push(adapter.address);
    }
  }
  return found.length ? found : ["127.0.0.1"];
};

const cors = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Methods": "GET, HEAD, OPTIONS",
  "Access-Control-Allow-Headers": "*",
};

const indexPage = (hosts) => {
  const links = Object.keys(apps)
    .flatMap((path) =>
      hosts.map(
        (host) =>
          `<li><a href="http://${host}:${port}${path}">http://${host}:${port}${path}</a></li>`,
      ),
    )
    .join("");
  return `<!doctype html>
<meta charset="utf-8">
<title>ghcts Lynx bundles</title>
<body style="font:16px/1.4 system-ui;margin:2rem;max-width:40rem">
<h1>Lynx Explorer</h1>
<p>Paste one of these into Explorer. Phone and this machine must share a network.</p>
<ul>${links}</ul>
</body>
`;
};

for (const [path, file] of Object.entries(apps)) {
  try {
    await stat(file);
  } catch {
    console.error(`Missing ${path}\n  expected ${file}\n  pack it first with scripts/pack-lynx.mjs`);
    process.exit(1);
  }
}

const server = createServer(async (request, response) => {
  const url = new URL(request.url ?? "/", `http://${request.headers.host}`);
  const path = url.pathname.replace(/\/+$/, "") || "/";
  if (request.method === "OPTIONS") {
    response.writeHead(204, cors);
    response.end();
    return;
  }
  if (path === "/" || path === "/index.html") {
    response.writeHead(200, {
      ...cors,
      "Content-Type": "text/html; charset=utf-8",
      "Cache-Control": "no-store",
    });
    if (request.method !== "HEAD")
      response.end(indexPage(["localhost", ...lanAddresses()]));
    else response.end();
    return;
  }
  const file = apps[path];
  if (!file) {
    response.writeHead(404, { ...cors, "Content-Type": "text/plain" });
    response.end("not found\n");
    return;
  }
  const info = await stat(file);
  // Lynx Explorer versions in the field omit Accept-Encoding but still
  // transparently decode Content-Encoding: gzip. Always compress bundles so
  // the phone does not hit its short template-fetch timeout on multi-MB JS.
  const compressed = gzipSync(await readFile(file));
  response.writeHead(200, {
    ...cors,
    "Content-Type": "application/octet-stream",
    "Content-Length": compressed ? compressed.length : info.size,
    ...(compressed ? { "Content-Encoding": "gzip", Vary: "Accept-Encoding" } : {}),
    "Cache-Control": "no-store",
  });
  if (request.method === "HEAD") {
    response.end();
    return;
  }
  if (compressed) response.end(compressed);
  else createReadStream(file).pipe(response);
});

server.listen(port, "0.0.0.0", () => {
  console.log(`Lynx Explorer — http://<lan-ip>:${port}/…/main.lynx.bundle\n`);
  for (const host of ["127.0.0.1", ...lanAddresses()]) {
    console.log(`  counter   http://${host}:${port}/counter/main.lynx.bundle`);
    console.log(`  misogram  http://${host}:${port}/misogram/main.lynx.bundle`);
    console.log("");
  }
});
