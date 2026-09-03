#!/usr/bin/env node
/**
 * Pack a ghcts JS program into a Lynx `main.lynx.bundle`.
 *
 * This is not a compiler backend.  It takes the GHCJS-shaped `all.js` ghcts
 * already emits (js-sources linked, same as a `.jsexe/all.js`) and runs the
 * same rspeedy recipe as miso's `mkLynxBundle`.
 *
 * `all.js` is linked program code like GHCJS `.jsexe/all.js`.  This helper
 * matches miso's `mkLynxBundle`: minify `all.js`, write `entry.js` that only
 * `import`s it, and run rspeedy with `pluginReactLynx()`.  Thread split and
 * `renderPage` live in the app js-sources (miso-native), not here.
 *
 *   node scripts/pack-lynx.mjs --js references/miso-lynx/examples/dist/node/all.js --out references/miso-lynx/examples/dist/lynx
 */
import { spawnSync } from "node:child_process";
import { cp, mkdir, readdir, writeFile } from "node:fs/promises";
import { join, resolve } from "node:path";

const args = process.argv.slice(2);
const flag = (name) => {
  const index = args.indexOf(name);
  return index >= 0 ? args[index + 1] : undefined;
};
const js = flag("--js");
const out = flag("--out");
const styles = flag("--styles");
const assets = flag("--assets");
const registry = flag("--registry") ?? "__misoGramAssets";
if (!js || !out) {
  console.error(
    "Usage: pack-lynx.mjs --js <all.js> --out <dir> [--styles styles.css] [--assets dir] [--registry name]",
  );
  process.exit(2);
}

const build = resolve(out, ".pack");
await mkdir(build, { recursive: true });
await cp(resolve(js), join(build, "all.js"));
const bun = spawnSync("bun", ["--version"], { encoding: "utf8" });
if (bun.status === 0) {
  const minified = spawnSync(
    "bun",
    ["build", "--minify-whitespace", "--target=bun", "--outfile=all.min.js", "all.js"],
    { cwd: build, encoding: "utf8" },
  );
  if (minified.status === 0)
    await cp(join(build, "all.min.js"), join(build, "all.js"));
}
const imports = [];
if (assets) {
  const root = resolve(assets);
  await cp(root, join(build, "assets"), { recursive: true });
  const files = [];
  const walk = async (dir, prefix) => {
    for (const entry of await readdir(dir, { withFileTypes: true })) {
      const relative = prefix ? `${prefix}/${entry.name}` : entry.name;
      if (entry.isDirectory()) await walk(join(dir, entry.name), relative);
      else if (/\.(png|jpe?g)$/i.test(entry.name)) files.push(relative);
    }
  };
  await walk(root, "");
  files.sort();
  const lines = ["const reg = {};"];
  files.forEach((file, index) => {
    lines.push(`import a${index} from './assets/${file}?inline';`);
    lines.push(`reg[${JSON.stringify(file)}] = a${index};`);
  });
  lines.push(`globalThis.${registry} = reg;`);
  await writeFile(join(build, "__assets.js"), `${lines.join("\n")}\n`);
  imports.push("import './__assets.js';");
}
if (styles) {
  await cp(resolve(styles), join(build, "styles.css"));
  imports.push("import './styles.css';");
}
imports.push("import './all.js';");
await writeFile(join(build, "entry.js"), `${imports.join("\n")}\n`);
await writeFile(
  join(build, "lynx.config.ts"),
  `import { defineConfig } from '@lynx-js/rspeedy';
import { pluginReactLynx } from '@lynx-js/react-rsbuild-plugin';
export default defineConfig({
  source: { entry: './entry.js' },
  plugins: [ pluginReactLynx() ],
});
`,
);
await writeFile(
  join(build, "package.json"),
  `${JSON.stringify(
    {
      type: "module",
      private: true,
      devDependencies: {
        "@lynx-js/react": "latest",
        "@lynx-js/react-rsbuild-plugin": "latest",
        "@lynx-js/rspeedy": "latest",
        // rspeedy 0.16.5 imports typescript from its own register hook and
        // does not depend on it, so a fresh install has no `typescript`.
        typescript: "latest",
      },
    },
    null,
    2,
  )}\n`,
);

const npm = spawnSync("npm", ["install", "--no-fund", "--no-audit"], {
  cwd: build,
  stdio: "inherit",
  env: { ...process.env, HOME: process.env.HOME },
});
if (npm.status !== 0) process.exit(npm.status ?? 1);

const rspeedyBin = join(build, "node_modules", ".bin", "rspeedy");
const packed = spawnSync(rspeedyBin, ["build"], {
  cwd: build,
  stdio: ["ignore", "pipe", "pipe"],
  env: { ...process.env, HOME: process.env.HOME },
});
if (packed.status !== 0) {
  process.stderr.write(packed.stdout ?? "");
  process.stderr.write(packed.stderr ?? "");
  process.exit(packed.status ?? 1);
}

const dist = join(build, "dist");
await mkdir(resolve(out), { recursive: true });
await cp(dist, resolve(out), { recursive: true });
console.log(`Wrote Lynx bundle: ${join(resolve(out), "main.lynx.bundle")}`);
