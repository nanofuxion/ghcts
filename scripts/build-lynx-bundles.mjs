import { spawnSync } from "node:child_process";

const run = (cmd, args) => {
  const result = spawnSync(cmd, args, { stdio: "inherit" });
  if (result.status !== 0) process.exit(result.status ?? 1);
};

run("node", ["dist/cli.js", "build", "--project", "references/miso-lynx/examples"]);
run("node", ["scripts/pack-lynx.mjs", "--js", "references/miso-lynx/examples/dist/node/all.js", "--out", "references/miso-lynx/examples/dist/lynx"]);
run("node", ["dist/cli.js", "build", "--project", "references/misogram"]);
run("node", [
  "scripts/pack-lynx.mjs",
  "--js", "references/misogram/dist/node/all.js",
  "--out", "references/misogram/dist/lynx",
  "--styles", "references/misogram/styles.css",
  "--assets", "references/misogram/assets",
  "--registry", "__misoGramAssets",
]);
