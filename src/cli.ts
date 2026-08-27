#!/usr/bin/env node
import { resolve } from 'node:path';
import { compileProject, formatDiagnostic } from './index.js';
import { serveProject } from './server.js';

const [command, ...args] = process.argv.slice(2);
const projectFlag = args.indexOf('--project');
const project = projectFlag >= 0 ? args[projectFlag + 1] : process.cwd();
const portFlag = args.indexOf('--port');
const port = portFlag >= 0 ? Number(args[portFlag + 1]) : undefined;
if (!['build', 'check', 'serve'].includes(command ?? '') || !project || (port !== undefined && (!Number.isInteger(port) || port < 1 || port > 65535))) {
  console.error('Usage: ghcts <build|check|serve> --project <directory> [--port <1-65535>]');
  process.exitCode = 2;
} else if (command === 'serve') {
  try {
    const running = await serveProject({ project: resolve(project), port });
    console.log(`Serving ${resolve(project)} at ${running.url}`);
    console.log('Press Ctrl+C to stop.');
  } catch (cause) {
    console.error(cause instanceof Error ? cause.message : String(cause));
    process.exitCode = 1;
  }
} else {
  const result = await compileProject({ project: resolve(project), emit: command === 'build' });
  for (const diagnostic of result.diagnostics) console.error(formatDiagnostic(diagnostic));
  if (!result.diagnostics.some(d => d.severity === 'error') && command === 'build') for (const output of result.outputPaths) console.log(output);
  process.exitCode = result.diagnostics.some(d => d.severity === 'error') ? 1 : 0;
}
