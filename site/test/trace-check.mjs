// Targeted check for paths the random walk rarely reaches (multi-blocks,
// damage assignment orders, B's Walker shuffled back). A seeded walk that
// prefers blocking with as many creatures as possible is played through the
// WASM API; the native build of the same library then replays the record
// (`engine-bench trace`) and both must print identical walk blocks.
//
// usage: node test/trace-check.mjs ENGINE_WASM ENGINE_BENCH [GAMES]

import { readFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { loadEngine } from "../web/engine.js";

const [wasmPath, bench, gamesArg] = process.argv.slice(2);
const games = Number(gamesArg || 40);
const engine = await loadEngine(readFileSync(wasmPath));

let x = 0x2545f4914f6cdd1dn;
const MASK = (1n << 64n) - 1n;
const rand = (n) => {
  x = (x * 6364136223846793005n + 1442695040888963407n) & MASK;
  return Number((x >> 33n) % BigInt(n));
};
const blockers = (m) => m.wb.filter((w) => w !== null).length + m.tb.reduce((a, b) => a + b, 0);

let failed = 0;
const seen = { order: 0, damageChoice: 0, shuffle: 0, over: 0 };
for (let g = 0; g < games; g++) {
  const rec = [g & 1, 20, 20];
  engine.load(rec);
  let wasm = engine.walkBlock();
  for (let n = 0; n < 1500; n++) {
    const v = engine.view();
    if (v.winner) { seen.over++; break; }
    if ([...v.A.bf, ...v.B.bf].some((w) => w.c > 30)) break;
    const ms = v.moves;
    let i;
    if (v.pend.kind === "block") {
      // the moves with the most blockers, then any
      const best = Math.max(...ms.map(blockers));
      const top = ms.map((m, k) => k).filter((k) => blockers(ms[k]) === best);
      i = rand(3) ? top[rand(top.length)] : rand(ms.length);
    } else if (v.pend.kind === "window") {
      // casts when possible, otherwise mostly pass (pumps tap Walkers,
      // which then can't attack or block)
      const casts = ms.map((m, k) => k).filter((k) => ms[k].k === "cast" && ms[k].x === 1 || ms[k].k === "castElixir" || ms[k].k === "elixir");
      const others = ms.map((m, k) => k).filter((k) => ms[k].k !== "pass");
      i = casts.length && rand(2) ? casts[rand(casts.length)] : others.length && rand(6) === 0 ? others[rand(others.length)] : 0;
    } else if (v.pend.kind === "attack") {
      // usually attack with every Walker
      const most = Math.max(...ms.map((m) => m.ws.length));
      const top = ms.map((m, k) => k).filter((k) => ms[k].ws.length === most);
      i = rand(4) ? top[rand(top.length)] : rand(ms.length);
    } else {
      i = rand(ms.length);
    }
    if (v.pend.kind === "order") seen.order++;
    if (v.pend.kind === "damage" && ms.length > 1) seen.damageChoice++;
    if (v.pend.kind === "shuffle") seen.shuffle++;
    rec.push(i);
    engine.play(i);
    wasm += engine.walkBlock();
  }
  const native = execFileSync(bench, ["trace"], { input: rec.join(" "), maxBuffer: 1 << 30 }).toString();
  if (native !== wasm) {
    failed++;
    console.log(`game ${g}: DIFFERENT (${rec.length - 3} moves)`);
  }
}
console.log(`${games} games: ${seen.order} damage-order decisions, ${seen.damageChoice} damage choices, ${seen.shuffle} shuffles, ${seen.over} finished`);
console.log(failed === 0 ? "all traces identical" : `${failed} trace(s) differ`);
process.exit(failed === 0 ? 0 : 1);
