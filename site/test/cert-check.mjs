// Certified B in WASM: load the site's certificate table the way the
// worker does, then play games of certified B against several A players.
// B must win every game, and the certificate must never fail.
//
// usage: node test/cert-check.mjs ENGINE_WASM CERT_GZ [GAMES [SEARCH_GAMES]]
//   GAMES games each against random, biased-random, rank- and value-
//   maximising A inside WASM (certtest.rs), SEARCH_GAMES against the
//   heuristic search, and GAMES/10 driven from JavaScript through the
//   page's own API (load / certPlan / play), with random A.

import { readFileSync } from "node:fs";
import { loadEngine, fetchCertTable } from "../web/engine.js";

const [wasmPath, gzPath, gamesArg, searchArg] = process.argv.slice(2);
const games = Number(gamesArg || 200);
const searchGames = Number(searchArg ?? Math.max(1, Math.floor(games / 10)));
const engine = await loadEngine(readFileSync(wasmPath));
let failed = 0;
const fail = (msg) => { failed++; console.log(`FAIL ${msg}`); };

// ---- loading ----
const t0 = performance.now();
const f = await fetchCertTable(readFileSync(gzPath));
const t1 = performance.now();
const r = engine.loadCert(f.bytes);
const t2 = performance.now();
if (!r.ok) { console.log(`FAIL loading: ${r.error}`); process.exit(1); }
console.log(`table: ${f.gzBytes} bytes gzipped, ${f.bytes.length} raw, ${r.records} records, checksum ${r.checksum}; ` +
  `inflate ${(t1 - t0).toFixed(0)} ms, decode ${(t2 - t1).toFixed(0)} ms`);

// ---- coverage of openings ----
const planAt = (rec) => { engine.load(rec); return engine.certPlan(); };
const p0 = planAt([1, 20, 20]);
if (!(p0.ok && p0.certified && p0.rank === 587 && p0.val === 17)) fail(`opening: ${JSON.stringify(p0)}`);
for (const [la, lb, want] of [[20, 17, true], [20, 40, true], [20, 16, false], [19, 20, null], [21, 20, null]]) {
  const p = planAt([1, la, lb]);
  if (!p.ok) fail(`opening ${la}/${lb}: ${p.error}`);
  else {
    console.log(`opening A ${la} / B ${lb}: ${p.certified ? `certified (rank ${p.rank}, needs ${p.val})` : `not certified (${p.reason}, lostAfter ${p.lostAfter})`}`);
    if (want !== null && p.certified !== want) fail(`opening ${la}/${lb}: expected certified=${want}`);
    if (!p.certified && p.lostAfter !== null) fail(`opening ${la}/${lb}: lostAfter should be null`);
  }
}
// A's first turn start is not covered when B started: an uncovered record
// from the start must not count as a lost certificate.
const pa = planAt([0, 20, 20]);
console.log(`A-first opening: ${pa.ok ? (pa.certified ? "certified" : `not certified (lostAfter ${pa.lostAfter})`) : pa.error}`);

// ---- self-play inside WASM ----
const advs = [["random", 0, games], ["bias", 1, games], ["rank", 2, games], ["val", 3, games], ["search30ms", 1030, searchGames]];
for (const [name, code, n] of advs) {
  if (n <= 0) continue;
  const s0 = performance.now();
  const sum = engine.certSelfplay(n, code, 0x5eed + code);
  const ms = performance.now() - s0;
  console.log(`wasm selfplay vs ${name}: ${sum.games} games, B won ${sum.bWins}, turns mean ${(sum.turnsTotal / sum.games).toFixed(1)} max ${sum.turnsMax}, ` +
    `A decisions ${sum.decisionsA}, B decisions ${sum.decisionsB}, ${sum.plans} plans, ${sum.nodes} checker nodes, ${sum.recordLife} on the record's life; ${(ms / 1000).toFixed(1)} s`);
  if (sum.games !== n || sum.bWins !== n || sum.failures.length) {
    fail(`selfplay vs ${name}: ${sum.failures.slice(0, 5).join(" | ")}`);
  }
}

// ---- games through the page's API ----
let x = 0x2545f4914f6cdd1dn;
const MASK = (1n << 64n) - 1n;
const rand = (n) => {
  x = (x * 6364136223846793005n + 1442695040888963407n) & MASK;
  return Number((x >> 33n) % BigInt(n));
};
const jsGames = Math.max(1, Math.floor(games / 10));
let jsWins = 0, plans = 0, maxMs = 0;
for (let g = 0; g < jsGames; g++) {
  const rec = [1, 20, 20];
  engine.load(rec);
  let v = engine.view();
  let ok = true;
  for (let n = 0; n < 100000 && !v.winner; n++) {
    if (v.toMove === "B") {
      engine.load(rec); // the worker replays the record for every request
      const p = engine.certPlan();
      plans++;
      maxMs = Math.max(maxMs, p.ms || 0);
      if (!p.ok || !p.certified || !p.moves.length) { fail(`js game ${g}: ${JSON.stringify(p)}`); ok = false; break; }
      for (const i of p.moves) { if (!engine.play(i)) { fail(`js game ${g}: illegal certified move`); ok = false; break; } rec.push(i); }
      if (!ok) break;
    } else {
      const i = rand(v.moves.length);
      engine.play(i);
      rec.push(i);
    }
    v = engine.view();
  }
  if (!ok) continue;
  if (v.winner === "B") jsWins++;
  else fail(`js game ${g}: winner ${v.winner}`);
}
console.log(`js games vs random: ${jsGames}, B won ${jsWins}; ${plans} certified requests, slowest ${maxMs.toFixed(1)} ms`);

if (failed) { console.log(`${failed} failures`); process.exit(1); }
console.log("cert-check: all good");
