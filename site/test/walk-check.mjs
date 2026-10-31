// Differential check: the WASM build must reproduce `rsolver walk` byte for
// byte. For each seed, with and without bias, it compares three outputs:
//   native   rsolver walk SEED STEPS [bias]
//   wasm     the walk generated inside WASM (engine.walk)
//   js       the walk driven from JavaScript through the site's own API
//            (load / play / view / walkBlock), with the same seeded choices
//
// usage: node test/walk-check.mjs ENGINE_WASM RSOLVER_BIN STEPS SEED...

import { readFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { loadEngine } from "../web/engine.js";

const [wasmPath, rsolver, stepsArg, ...seeds] = process.argv.slice(2);
if (!wasmPath || !rsolver || !stepsArg || seeds.length === 0) {
  console.error("usage: node test/walk-check.mjs ENGINE_WASM RSOLVER_BIN STEPS SEED...");
  process.exit(2);
}
const steps = Number(stepsArg);
const engine = await loadEngine(readFileSync(wasmPath));

const MASK = (1n << 64n) - 1n;
const next = (x) => (x * 6364136223846793005n + 1442695040888963407n) & MASK;
const pick = (x, n) => Number((x >> 33n) % BigInt(n));

function jsWalk(seed, steps, bias) {
  let x = BigInt(seed);
  const rec = [(BigInt(seed) & 1n) === 0n ? 0 : 1, 20, 20];
  engine.load(rec);
  let out = "";
  for (let n = 0; n < steps; n++) {
    out += engine.walkBlock();
    const v = engine.view();
    const ms = v.moves;
    const big = [...v.A.bf, ...v.B.bf].some((w) => w.c > 40);
    if (v.winner !== null || ms.length === 0 || big) {
      engine.load(rec);
      continue;
    }
    x = next(x);
    let cand = ms.map((_, i) => i);
    const others = cand.filter((i) => ms[i].k !== "pass" && ms[i].k !== "pump");
    if (bias && others.length > 0 && pick(x, 3) !== 0) {
      x = next(x);
      cand = others;
    }
    if (!engine.play(cand[pick(x, cand.length)])) throw new Error("play rejected a listed move");
  }
  return out;
}

function firstDiff(a, b) {
  const la = a.split("\n");
  const lb = b.split("\n");
  for (let i = 0; i < Math.max(la.length, lb.length); i++) {
    if (la[i] !== lb[i]) return `line ${i + 1}:\n  expected ${la[i]}\n  got      ${lb[i]}`;
  }
  return "lengths differ";
}

let failed = 0;
for (const seed of seeds) {
  for (const bias of [false, true]) {
    const args = ["walk", seed, String(steps)];
    if (bias) args.push("bias");
    const native = execFileSync(rsolver, args, { maxBuffer: 1 << 30 }).toString();
    const wasm = engine.walk(seed, steps, bias);
    const js = jsWalk(seed, steps, bias);
    const lines = native.split("\n").length - 1;
    const overs = (native.match(/pend=O/g) || []).length;
    for (const [name, got] of [["wasm", wasm], ["js", js]]) {
      const ok = got === native;
      if (!ok) failed++;
      console.log(
        `seed ${seed}${bias ? " bias" : ""}: ${name} ${ok ? "identical" : "DIFFERENT"} ` +
          `(${lines} lines, ${native.length} bytes, ${overs} finished games)` +
          (ok ? "" : "\n" + firstDiff(native, got))
      );
    }
  }
}
console.log(failed === 0 ? "all walks identical" : `${failed} walk(s) differ`);
process.exit(failed === 0 ? 0 : 1);
