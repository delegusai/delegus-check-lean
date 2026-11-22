// Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.
//
// Runs the scripts against a source checkout of the reference engine instead
// of the npm packages, for an engine release not yet on npm:
//
//   DELEGUS_ENGINE_DIR=/path/to/delegus node --import ./scripts/engine-hook.mjs scripts/compare.mjs
//
// `@delegus/core` and `@delegus/conformance` then resolve to
// $DELEGUS_ENGINE_DIR/packages/{core,conformance}/src/index.ts (Node strips
// the TypeScript types; Node 22.6+ needs --experimental-strip-types).

import { register } from "node:module";
import { pathToFileURL } from "node:url";
import { join } from "node:path";

const dir = process.env.DELEGUS_ENGINE_DIR;
if (!dir) throw new Error("set DELEGUS_ENGINE_DIR to a checkout containing packages/core and packages/conformance");
const map = {
  "@delegus/core": pathToFileURL(join(dir, "packages", "core", "src", "index.ts")).href,
  "@delegus/conformance": pathToFileURL(join(dir, "packages", "conformance", "src", "index.ts")).href,
};
const hooks = `
const map = ${JSON.stringify(map)};
export async function resolve(specifier, context, next) {
  if (Object.hasOwn(map, specifier)) return { url: map[specifier], shortCircuit: true };
  return next(specifier, context);
}`;
register(`data:text/javascript,${encodeURIComponent(hooks)}`);
