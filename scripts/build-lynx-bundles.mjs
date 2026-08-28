import { spawnSync } from "node:child_process";

const run = (cmd, args) => {
  const result = spawnSync(cmd, args, { stdio: "inherit" });
  if (result.status !== 0) process.exit(result.status ?? 1);
};

// `ghcts build` writes the linked bundle to `<outDir>/jsexe/all.js` and nowhere
// else; `dist/node/all.js` is a leftover of a backend that no longer exists, and
// packing it shipped a dead artifact. The link also overflows node's default
// stack inside `dist/js/optimizer.js`, hence --stack-size.
const build = (project) => run("node", ["--stack-size=60000", "dist/cli.js", "build", "--project", project]);

build("references/miso-lynx/examples");
run("node", ["scripts/pack-lynx.mjs", "--js", "references/miso-lynx/examples/dist/jsexe/all.js", "--out", "references/miso-lynx/examples/dist/lynx"]);
build("references/misogram");
run("node", [
  "scripts/pack-lynx.mjs",
  "--js", "references/misogram/dist/jsexe/all.js",
  "--out", "references/misogram/dist/lynx",
  "--styles", "references/misogram/styles.css",
  "--assets", "references/misogram/assets",
  "--registry", "__misoGramAssets",
]);
