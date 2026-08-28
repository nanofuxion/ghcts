import { createReadStream } from 'node:fs';
import { stat } from 'node:fs/promises';
import { createServer, type Server } from 'node:http';
import { extname, resolve, sep } from 'node:path';
import { build } from './build.js';
import { readFile } from 'node:fs/promises';
import { formatDiagnostic } from './diagnostics.js';

const mimeTypes: Record<string, string> = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.ts': 'text/plain; charset=utf-8', '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8',
};

export interface ServeOptions { project: string; port?: number; host?: string; }
export interface RunningServer { server: Server; url: string; close(): Promise<void>; }

/** Build a project, then serve its browser output using only Node's standard library. */
export async function serveProject(options: ServeOptions): Promise<RunningServer> {
  const config = JSON.parse(await readFile(`${options.project}/ghcts.json`, 'utf8'));
  const result = await build({ project: options.project, config });
  if (result.diagnostics.some(d => d.severity === 'error')) throw new Error(result.diagnostics.map(formatDiagnostic).join('\n'));
  // The new pipeline emits a GHC-shaped .jsexe rather than per-target trees,
  // so `serve` hands out that directory directly.
  const root = resolve(options.project, config.outDir, 'jsexe');
  const server = createServer(async (request, response) => {
    const rawPath = new URL(request.url ?? '/', 'http://localhost').pathname;
    const relativePath = decodeURIComponent(rawPath === '/' ? '/index.html' : rawPath).replace(/^\/+/, '');
    const candidates = [
      resolve(root, relativePath),
      relativePath.startsWith(`assets${sep}`) ? resolve(root, relativePath.replace(/^assets\//, 'js/')) : null,
      relativePath.startsWith(`assets${sep}`) ? resolve(root, relativePath.replace(/^assets\//, 'assets/')) : null,
    ].filter((candidate): candidate is string => candidate !== null);
    const file = candidates.find(candidate => candidate === root || candidate.startsWith(`${root}${sep}`)) ?? candidates[0];
    if (!file) { response.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' }).end('Not found'); return; }
    if (file !== root && !file.startsWith(`${root}${sep}`)) { response.writeHead(403).end('Forbidden'); return; }
    try {
      if (!(await stat(file)).isFile()) throw new Error('not a file');
      response.writeHead(200, {
        'content-type': mimeTypes[extname(file)] ?? 'application/octet-stream',
        'cache-control': 'no-store, max-age=0',
      });
      createReadStream(file).pipe(response);
    } catch { response.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' }).end('Not found'); }
  });
  await new Promise<void>((resolveListen, rejectListen) => {
    server.once('error', rejectListen);
    server.listen(options.port ?? 3000, options.host ?? '127.0.0.1', () => { server.off('error', rejectListen); resolveListen(); });
  });
  const address = server.address();
  if (!address || typeof address === 'string') throw new Error('Could not determine listening address');
  const host = options.host === '0.0.0.0' ? 'localhost' : (options.host ?? '127.0.0.1');
  return { server, url: `http://${host}:${address.port}`, close: () => new Promise((resolveClose, rejectClose) => server.close(error => error ? rejectClose(error) : resolveClose())) };
}
