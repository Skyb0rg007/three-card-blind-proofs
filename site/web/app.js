// The play page. Rules come from engine.wasm (rsolver/src/model.rs); this
// file only renders states, offers the legal moves and keeps the record.
import { loadEngine } from "./engine.js";

const STEPS = [
  ["Upkeep", "Upkeep"],
  ["DrawStep", "Draw"],
  ["Main1", "Main 1"],
  ["BeginCombat", "Begin combat"],
  ["DeclAtk", "Attackers"],
  ["DeclBlk", "Blockers"],
  ["DamageStep", "Damage"],
  ["EndCombat", "End combat"],
  ["Main2", "Main 2"],
  ["EndStep", "End"],
];
const STEP_LABEL = Object.fromEntries(STEPS);
const DRAW_TURNS = 60; // offer a draw after this many turns
// All of a user's github.io project pages share one origin (and one
// localStorage), so the key is namespaced by repository.
const STORE_KEY = "three-card-blind-proofs/hangarback-game/v1";

const $ = (id) => document.getElementById(id);
const el = (tag, attrs = {}, ...kids) => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") e.className = v;
    else if (k === "onclick") e.addEventListener("click", v);
    else if (k === "text") e.textContent = v;
    else if (v === true) e.setAttribute(k, "");
    else if (v !== false && v != null) e.setAttribute(k, v);
  }
  for (const k of kids.flat()) if (k != null && k !== false) e.append(k.nodeType ? k : String(k));
  return e;
};
const opp = (p) => (p === "A" ? "B" : "A");
const plural = (n, one, many = one + "s") => `${n} ${n === 1 ? one : many}`;

// ---- state ----

let engine; // main-thread engine: legal moves, steps, views
let worker = null;
let workerBusy = false;
let reqId = 0;

let settings = { human: "A", starter: "A", budget: 1000, autopass: "smart", lifeA: 20, lifeB: 20 };
let game; // { rec, who, views, log, result }
let cur; // view of the current state
let passUntilTurn = null; // turn number the "pass until next turn" shortcut runs to
let lastEngineInfo = "";
let drawOfferFrom = DRAW_TURNS;
let drawDismissedKey = null;
let flashStatus = ""; // the engine's latest action, shown under the status

function newGame() {
  game = {
    rec: [settings.starter === "A" ? 0 : 1, settings.lifeA, settings.lifeB],
    who: [], // per move: "user", "auto" (passed for the user) or "engine"
    views: [], // the view before each move
    turns: [], // the turn number before each move
    log: [], // per move: [{kind, text, actor}]
    result: null, // "A", "B", "draw" or null
  };
  passUntilTurn = null;
  lastEngineInfo = "";
  drawOfferFrom = DRAW_TURNS;
  drawDismissedKey = null;
  engine.load(game.rec);
  cur = engine.view();
  cancelSearch();
}

function turnNow() {
  const n = game.views.length;
  if (n === 0) return 1;
  return game.turns[n - 1] + (cur.active !== game.views[n - 1].active ? 1 : 0);
}

function save() {
  try {
    localStorage.setItem(STORE_KEY, JSON.stringify({ settings, rec: game.rec, who: game.who, result: game.result }));
  } catch (_) {
    /* storage unavailable: the game just won't survive a reload */
  }
}

function restore() {
  try {
    const raw = localStorage.getItem(STORE_KEY);
    if (!raw) return false;
    const saved = JSON.parse(raw);
    if (!saved || !Array.isArray(saved.rec) || saved.rec.length < 3) return false;
    settings = { ...settings, ...saved.settings };
    newGame();
    const moves = saved.rec.slice(3);
    for (let k = 0; k < moves.length; k++) {
      if (!applyMove(moves[k], saved.who[k] || "user", true)) break;
    }
    game.result = saved.result && !cur.winner ? saved.result : game.result;
    return true;
  } catch (_) {
    return false;
  }
}

// ---- names and descriptions ----

const walkerName = (side, i) => {
  const w = side.bf[i];
  return w ? `Walker ${i + 1} (${w.c}/${w.c})` : `Walker ${i + 1}`;
};
const cardName = (c) => (c === "W" ? "Hangarback Walker" : "Elixir of Immortality");
const shortCard = (c) => (c === "W" ? "Walker" : "Elixir");
const youOr = (p) => (p === settings.human ? "You" : "Engine");

function blockerName(def, b) {
  return b === "T" ? "Thopter" : walkerName(def, b);
}

/// Human-readable text for move `m` in view `v`.
function moveText(v, m) {
  const p = v.toMove;
  const me = v[p];
  const att = v[v.active];
  const def = v[opp(v.active)];
  switch (m.k) {
    case "pass":
      return v.pend.passed ? `passes; ${STEP_LABEL[v.pend.step]} ends` : "passes priority";
    case "pump": {
      const w = me.bf[m.w];
      return `pumps ${walkerName(me, m.w)} to ${w.c + 1}/${w.c + 1}`;
    }
    case "elixir":
      return `activates Elixir: gains 5 life (${me.life} → ${me.life + 5}); Elixir and the graveyard are shuffled into the library`;
    case "cast":
      return m.x === 1
        ? "casts Hangarback Walker with X = 1 (a 1/1)"
        : "casts Hangarback Walker with X = 0; it dies at once, with no Thopters";
    case "castElixir":
      return "casts Elixir of Immortality";
    case "attack": {
      const parts = m.ws.map((i) => walkerName(att, i));
      if (m.t > 0) parts.push(plural(m.t, "Thopter"));
      return parts.length ? `attacks with ${parts.join(", ")}` : "declares no attackers";
    }
    case "block": {
      const parts = [];
      m.wb.forEach((a, j) => {
        if (a !== null) parts.push(`${walkerName(def, j)} blocks ${walkerName(att, v.cmb.atk[a])}`);
      });
      m.tb.forEach((k, a) => {
        if (k > 0) parts.push(`${plural(k, "Thopter")} ${k === 1 ? "blocks" : "block"} ${walkerName(att, v.cmb.atk[a])}`);
      });
      if (m.tr > 0) parts.push(`${plural(m.tr, "Thopter")} ${m.tr === 1 ? "blocks an attacking Thopter" : "block attacking Thopters"}`);
      return parts.length ? `blocks: ${parts.join("; ")}` : "declares no blockers";
    }
    case "order": {
      const parts = [];
      m.os.forEach((bs, a) => {
        if (bs.length >= 2) parts.push(`${walkerName(att, v.cmb.atk[a])} deals damage to ${bs.map((b) => blockerName(def, b)).join(", then ")}`);
      });
      return `orders damage: ${parts.join("; ")}`;
    }
    case "assign": {
      const parts = [];
      m.js.forEach((j, a) => {
        const bs = v.cmb.blk[a];
        if (bs.length >= 2) parts.push(`${walkerName(att, v.cmb.atk[a])} kills ${j === 0 ? "none" : bs.slice(0, j).map((b) => blockerName(def, b)).join(" and ")}`);
      });
      return parts.length ? `assigns combat damage: ${parts.join("; ")}` : "deals combat damage";
    }
    case "arrange":
      return `orders B's library, top first: ${m.lib.map(shortCard).join(", ")}`;
  }
  return JSON.stringify(m);
}

function counterBag(side) {
  const bag = new Map();
  for (const w of side.bf) bag.set(w.c, (bag.get(w.c) || 0) + 1);
  return bag;
}

/// Things that happened as a result of a move (draws, combat results).
function events(pre, m, post) {
  const out = [];
  if (m.k === "pass" && pre.pend.kind === "window" && pre.pend.step === "Upkeep" && pre.pend.passed) {
    const a = pre[pre.active];
    const b = post[pre.active];
    if (b.library.length < a.library.length) out.push(`${pre.active} draws ${cardName(a.library[0])}`);
  }
  if (m.k === "assign") {
    for (const p of ["A", "B"]) {
      const a = pre[p];
      const b = post[p];
      if (b.life < a.life) out.push(`${p} takes ${a.life - b.life} damage (${a.life} → ${b.life})`);
      const before = counterBag(a);
      for (const w of b.bf) before.set(w.c, before.get(w.c) - 1);
      let made = 0;
      const dead = [];
      for (const [c, n] of before) for (let k = 0; k < n; k++) { dead.push(c); made += c; }
      for (const c of dead) out.push(`${p}'s ${c}/${c} Walker dies and makes ${plural(c, "Thopter")}`);
      const lost = a.thopU + a.thopT + made - (b.thopU + b.thopT);
      if (lost > 0) out.push(`${p} loses ${plural(lost, "Thopter")}`);
    }
    if (post.winner) out.push(`${opp(post.winner)} takes lethal damage: ${post.winner} wins`);
  }
  return out;
}

// ---- playing moves ----

/// Moves that leave the board as it was (for "stops if the engine acts").
function isNoop(m) {
  switch (m.k) {
    case "pass": case "order": case "assign": return true;
    case "attack": return m.ws.length === 0 && m.t === 0;
    case "block": return m.wb.every((x) => x === null) && m.tb.every((x) => x === 0) && m.tr === 0;
    default: return false;
  }
}

/// Apply move index `i` for the side to move. `quiet` skips rendering.
function applyMove(i, who, quiet = false) {
  const pre = cur;
  const m = pre.moves[i];
  if (!m || !engine.play(i)) return false;
  const turn = turnNow();
  game.rec.push(i);
  game.who.push(who);
  game.views.push(pre);
  game.turns.push(turn);
  cur = engine.view();
  const entries = [{ kind: m.k === "pass" ? "pass" : "action", actor: pre.toMove, text: moveText(pre, m), who }];
  for (const t of events(pre, m, cur)) entries.push({ kind: "event", text: t });
  game.log.push(entries);
  if (cur.winner) game.result = cur.winner;
  if (who === "engine" && !isNoop(m)) {
    passUntilTurn = null;
    flashStatus = `Engine (${pre.toMove}) ${moveText(pre, m)}.`;
  }
  if (!quiet) save();
  return true;
}

function undo() {
  let k = game.who.lastIndexOf("user");
  if (k < 0) return;
  cancelSearch();
  game.rec.length = 3 + k;
  game.who.length = k;
  game.views.length = k;
  game.turns.length = k;
  game.log.length = k;
  game.result = null;
  passUntilTurn = null;
  engine.load(game.rec);
  cur = engine.view();
  drawDismissedKey = null;
  save();
  advance();
}

// ---- automatic moves ----

const isMine = (v) => v.toMove === settings.human;

function shouldAutoPass(v) {
  if (v.pend.kind !== "window") return false;
  const nonPass = v.moves.filter((m) => m.k !== "pass");
  if (nonPass.length === 0) return true;
  if (passUntilTurn !== null) return true;
  if (settings.autopass !== "smart") return false;
  // Moves the solver's exploration filter keeps (REDUCTION.md R6): anything
  // else is matched by the same action at a later window.
  if (v.filtered.some((i) => v.moves[i].k !== "pass")) return false;
  // Still stop in your own main phases when you could cast something.
  const main = v.pend.step === "Main1" || v.pend.step === "Main2";
  if (main && v.active === settings.human && nonPass.some((m) => m.k === "cast" || m.k === "castElixir")) return false;
  return true;
}

let advancing = false;
function advance() {
  if (advancing) return;
  advancing = true;
  try {
    let n = 0;
    while (!game.result && !cur.winner && n < 400) {
      if (passUntilTurn !== null && (turnNow() >= passUntilTurn || (isMine(cur) && cur.pend.kind !== "window"))) passUntilTurn = null;
      if (isMine(cur)) {
        if (cur.moves.length === 1) { applyMove(0, "auto", true); n++; continue; }
        if (shouldAutoPass(cur)) { applyMove(cur.moves.findIndex((m) => m.k === "pass"), "auto", true); n++; continue; }
        break;
      }
      // the engine's decision: trivial ones are played here
      const cands = cur.filtered.length ? cur.filtered : cur.moves.map((_, i) => i);
      if (cands.length <= 1) { applyMove(cands[0] ?? 0, "engine", true); n++; continue; }
      break;
    }
    save();
    render();
    if (!game.result && !cur.winner && !isMine(cur)) {
      if (n >= 400) setTimeout(advance, 0);
      else requestEngineMove();
    } else if (n >= 400) {
      setTimeout(advance, 0);
    }
  } finally {
    advancing = false;
  }
}

// ---- the engine worker ----

function startWorker() {
  worker = new Worker(new URL("worker.js", import.meta.url), { type: "module" });
  worker.onmessage = onEngineReply;
  worker.onerror = (e) => {
    workerBusy = false;
    lastEngineInfo = `Engine error: ${e.message || "worker failed"}`;
    render();
  };
}

function cancelSearch() {
  reqId++;
  if (workerBusy && worker) {
    worker.terminate();
    worker = null;
    workerBusy = false;
  }
}

function requestEngineMove() {
  if (workerBusy) return;
  if (!worker) startWorker();
  workerBusy = true;
  const id = ++reqId;
  worker.postMessage({ id, rec: game.rec.slice(), budget: settings.budget });
  render();
}

function describeValue(r) {
  const forA = r.value;
  if (Math.abs(forA) >= r.win) {
    const who = forA > 0 ? "A" : "B";
    return `it sees a forced win for ${who} within its search (assuming the reduced move sets it searches)`;
  }
  const lead = forA === 0 ? "level" : `${forA > 0 ? "A" : "B"} ahead by ${Math.abs(forA)}`;
  return `heuristic score ${lead}`;
}

function onEngineReply(e) {
  const r = e.data;
  if (r.id !== reqId) return; // stale (undo or restart happened)
  workerBusy = false;
  if (!r.ok) {
    lastEngineInfo = `Engine error: ${r.error}`;
    render();
    return;
  }
  const reach = r.depth === 0 ? "to the end of this turn" : `this turn and ${plural(r.depth, "more turn")}`;
  lastEngineInfo =
    `Engine searched ${reach} (${r.nodes.toLocaleString()} new positions, ` +
    `${(r.ms / 1000).toFixed(1)} s); ${describeValue(r)}.`;
  if (!applyMove(r.move, "engine")) {
    lastEngineInfo = "Engine error: it chose an illegal move.";
    render();
    return;
  }
  advance();
}

// ---- draws ----

function drawPrompt() {
  if (game.result || cur.winner) return null;
  const t = turnNow();
  // count repeated turn-start positions
  const counts = new Map();
  for (let k = 0; k < game.views.length; k++) {
    const v = game.views[k];
    if (k === 0 || v.active !== game.views[k - 1].active) counts.set(v.key, (counts.get(v.key) || 0) + 1);
  }
  if (game.views.length && cur.active !== game.views[game.views.length - 1].active) counts.set(cur.key, (counts.get(cur.key) || 0) + 1);
  let rep = 0;
  let repKey = null;
  for (const [key, n] of counts) if (n > rep) { rep = n; repKey = key; }
  if (rep >= 3 && drawDismissedKey !== repKey) {
    return { text: "The same turn-start position has now occurred three times. Declare a draw?", dismiss: () => (drawDismissedKey = repKey) };
  }
  if (t >= drawOfferFrom) {
    return { text: `This game has reached turn ${t}. Walkers grow forever and Elixir can loop, so it may never end. Declare a draw?`, dismiss: () => (drawOfferFrom = t + 30) };
  }
  return null;
}

function declareDraw() {
  if (game.result || cur.winner) return;
  cancelSearch();
  game.result = "draw";
  save();
  render();
}

// ---- rendering ----

function render() {
  renderSide($("side-top"), opp(settings.human));
  renderSide($("side-bottom"), settings.human);
  renderTurnbar();
  renderCombat();
  renderStatus();
  renderBanner();
  renderControls();
  renderLog();
  $("engine-info").textContent = lastEngineInfo;
  $("btn-undo").disabled = !game.who.includes("user");
  $("btn-draw").disabled = !!(game.result || cur.winner);
}

function renderSide(box, p) {
  const s = cur[p];
  const mine = p === settings.human;
  const att = cur.cmb.atk.length || cur.cmb.atkThop ? cur.active : null;
  box.className = "side" + (!game.result && cur.toMove === p && !cur.winner ? " decide" : "");
  box.replaceChildren();
  const head = el("div", { class: "side-head" },
    el("div", { class: "who" }, `Player ${p}`,
      el("span", { class: `tag ${mine ? "you" : "them"}` }, mine ? "you" : "engine"),
      cur.active === p ? el("span", { class: "tag active" }, "active") : null),
    cur.winner === opp(p)
      ? el("div", { class: "life", title: "reduced to 0 or less life" }, "≤0", el("small", {}, "life"))
      : el("div", { class: "life", "aria-label": `life ${s.life}` }, String(s.life), el("small", {}, "life")));
  const res = el("div", { class: "res" },
    el("span", {}, "City of Traitors: ", el("b", {}, s.city ? "untapped" : "tapped")),
    el("span", {}, "Mana pool: ", el("b", {}, s.pool ? "◇".repeat(s.pool) + ` (${s.pool})` : "empty")),
    el("span", {}, "Graveyard: ", el("b", {}, s.gyW ? plural(s.gyW, "Walker") : "empty")));
  if (p === "B") res.append(el("span", {}, "Library: ", el("b", {}, s.library.length ? "top → " + s.library.map(shortCard).join(", ") : "empty")));
  box.append(head, res);

  // battlefield
  box.append(el("div", { class: "zone-label" }, "Battlefield"));
  const bf = el("div", { class: "cards" });
  s.bf.forEach((w, i) => {
    const chips = [];
    if (w.tapped) chips.push(el("span", { class: "chip" }, "tapped"));
    if (w.sick) chips.push(el("span", { class: "chip" }, "summoning sick"));
    if (att === p && cur.cmb.atk.includes(i)) chips.push(el("span", { class: "chip atk" }, "attacking"));
    if (att && att !== p && cur.cmb.blk.some((bs) => bs.includes(i))) chips.push(el("span", { class: "chip blk" }, "blocking"));
    bf.append(el("div", { class: "card" + (w.tapped ? " tapped" : ""), title: `Hangarback Walker with ${plural(w.c, "counter")}` },
      el("div", { class: "name" }, `Walker ${i + 1}`),
      el("div", { class: "chips" }, chips),
      el("div", { class: "pt" }, `${w.c}/${w.c}`)));
  });
  if (s.thopU) bf.append(thopterCard(s.thopU, false, 0));
  if (s.thopT) bf.append(thopterCard(s.thopT, true, att === p ? cur.cmb.atkThop : 0));
  if (s.elixir) bf.append(el("div", { class: "card" }, el("div", { class: "name" }, "Elixir of Immortality"), el("div", { class: "chips" }, el("span", { class: "chip" }, "{2},{T}: gain 5"))));
  if (!bf.childNodes.length) bf.append(el("span", { class: "empty" }, "no permanents besides City"));
  box.append(bf);

  // hand
  box.append(el("div", { class: "zone-label" }, "Hand"));
  const hand = el("div", { class: "cards" });
  for (let k = 0; k < s.handW; k++) hand.append(el("div", { class: "card hidden-card" }, el("div", { class: "name" }, "Hangarback Walker"), el("div", { class: "chips" }, el("span", { class: "chip" }, "{X}{X}"))));
  if (s.handE) hand.append(el("div", { class: "card hidden-card" }, el("div", { class: "name" }, "Elixir of Immortality"), el("div", { class: "chips" }, el("span", { class: "chip" }, "{1}"))));
  if (!hand.childNodes.length) hand.append(el("span", { class: "empty" }, "empty"));
  box.append(hand);
}

function thopterCard(n, tapped, attacking) {
  return el("div", { class: "card thopter" + (tapped ? " tapped" : ""), title: "1/1 colorless Thopter tokens with flying" },
    el("div", { class: "name" }, `Thopter ×${n}`),
    el("div", { class: "chips" }, el("span", { class: "chip" }, tapped ? "tapped" : "untapped"), el("span", { class: "chip" }, "flying"),
      attacking ? el("span", { class: "chip atk" }, `${attacking} attacking`) : null),
    el("div", { class: "pt" }, "1/1"));
}

function currentStep(v) {
  return v.pend.step || null;
}

function renderTurnbar() {
  const box = $("turnbar");
  const st = currentStep(cur);
  const idx = STEPS.findIndex(([k]) => k === st);
  const steps = el("ol", { class: "steps", "aria-label": "turn steps" },
    STEPS.map(([k, label], i) => el("li", { class: i === idx ? "now" : i < idx ? "done" : "" }, label)));
  const t = turnNow();
  box.replaceChildren(
    el("div", { class: "turnline" },
      el("span", {}, el("b", {}, `Turn ${t}`), ` · ${cur.active === settings.human ? "your" : "the engine's"} turn (${cur.active})`),
      el("span", { class: "dim" }, cur.firstTurn ? "starting player's first turn: no draw" : "")),
    steps);
}

function renderCombat() {
  const box = $("combat");
  const c = cur.cmb;
  if (!c.atk.length && !c.atkThop) { box.hidden = true; return; }
  box.hidden = false;
  const att = cur[cur.active];
  const def = cur[opp(cur.active)];
  const blocksDeclared = cur.pend.kind !== "block" && ["DeclBlk", "DamageStep"].includes(cur.pend.step);
  const items = c.atk.map((i, a) => {
    const bs = c.blk[a] || [];
    const tail = !blocksDeclared ? "" : bs.length ? ` ← blocked by ${bs.map((b) => blockerName(def, b)).join(", ")}${bs.length > 1 ? " (in damage order)" : ""}` : " (unblocked)";
    return el("li", {}, `${walkerName(att, i)}${tail}`);
  });
  if (c.atkThop) {
    const tail = blocksDeclared ? ` (${c.trades} blocked by Thopters, ${c.atkThop - c.trades} unblocked)` : "";
    items.push(el("li", {}, `${plural(c.atkThop, "Thopter")}${tail}`));
  }
  box.replaceChildren(el("b", {}, `Combat: ${cur.active} attacks`), el("ul", {}, items));
}

function pendText(v) {
  switch (v.pend.kind) {
    case "window": return `priority in ${STEP_LABEL[v.pend.step]}`;
    case "attack": return "declare attackers";
    case "block": return "declare blockers";
    case "order": return "order blockers for damage";
    case "damage": return "assign combat damage";
    case "shuffle": return "choose the order of B's library";
    default: return "";
  }
}

function renderStatus() {
  const box = $("status");
  box.className = "status";
  let main;
  let sub = flashStatus;
  if (game.result === "draw") { main = "The game is declared a draw."; box.classList.add("over"); }
  else if (game.result || cur.winner) {
    const w = game.result || cur.winner;
    main = w === settings.human ? `You win as ${w}!` : `The engine wins as ${w}.`;
    box.classList.add("over");
  } else if (isMine(cur)) {
    main = `Your decision (${settings.human}): ${pendText(cur)}`;
    if (cur.pend.kind === "window" && cur.pend.passed) sub = (sub ? sub + " " : "") + "The engine passed: if you pass too, the step ends.";
  } else {
    main = `Engine (${cur.toMove}) is thinking: ${pendText(cur)}…`;
    box.classList.add("engine");
  }
  box.replaceChildren(main, ...(sub ? [el("span", { class: "sub" }, sub)] : []));
}

function renderBanner() {
  const box = $("banner");
  const d = drawPrompt();
  if (!d) { box.hidden = true; box.replaceChildren(); return; }
  box.hidden = false;
  box.replaceChildren(el("p", {}, d.text),
    el("button", { class: "primary", type: "button", onclick: declareDraw }, "Declare draw"),
    el("button", { type: "button", onclick: () => { d.dismiss(); render(); } }, "Keep playing"));
}

function renderLog() {
  const box = $("log");
  box.classList.toggle("show-passes", $("show-passes").checked);
  box.replaceChildren();
  let lastTurn = 0;
  game.log.forEach((entries, k) => {
    const t = game.turns[k];
    if (t !== lastTurn) {
      lastTurn = t;
      const v = game.views[k];
      box.append(el("li", { class: "turn" }, `Turn ${t} · ${v.active} (${youOr(v.active)})`));
    }
    for (const e of entries) {
      if (e.kind === "event") box.append(el("li", { class: "event" }, e.text));
      else box.append(el("li", { class: e.kind === "pass" ? "pass hide" : "" },
        el("span", { class: `actor ${e.actor}` }, `${e.actor}${e.actor === settings.human ? " (you)" : ""}`), " ", e.text,
        e.who === "auto" ? el("span", { class: "dim" }, " (auto)") : null));
    }
  });
  if (game.result === "draw") box.append(el("li", { class: "event" }, "The game is declared a draw."));
  box.scrollTop = box.scrollHeight;
}

// ---- controls ----

function renderControls() {
  const box = $("controls");
  box.replaceChildren();
  if (game.result || cur.winner) {
    box.append(el("div", { class: "row" },
      el("button", { class: "primary", type: "button", onclick: restartSame }, "Play again"),
      el("button", { type: "button", onclick: openSetup }, "Change settings")));
    return;
  }
  if (!isMine(cur)) return;
  const v = cur;
  switch (v.pend.kind) {
    case "window": return windowControls(box, v);
    case "attack": return attackControls(box, v);
    case "block": return blockControls(box, v);
    case "order": return orderControls(box, v);
    case "damage": return damageControls(box, v);
    case "shuffle": return shuffleControls(box, v);
  }
}

function play(i) {
  flashStatus = "";
  if (applyMove(i, "user")) advance();
}

function costOf(m, me) {
  switch (m.k) {
    case "pump": return "{1}, {T}";
    case "elixir": return "{2}, {T}";
    case "cast": return m.x ? "{2}" : "{0}";
    case "castElixir": return "{1}";
    default: return "";
  }
}

function buttonLabel(v, m) {
  const me = v[v.toMove];
  switch (m.k) {
    case "pump": { const c = me.bf[m.w].c; return `Pump Walker ${m.w + 1} (${c}/${c} → ${c + 1}/${c + 1})`; }
    case "elixir": return `Activate Elixir: gain 5 life (${me.life} → ${me.life + 5}), shuffle it and your graveyard into your library`;
    case "cast": return m.x === 1 ? "Cast Hangarback Walker, X = 1" : "Cast Hangarback Walker, X = 0 (it dies at once, no Thopters)";
    case "castElixir": return "Cast Elixir of Immortality";
  }
  return moveText(v, m);
}

function windowControls(box, v) {
  const me = v[settings.human];
  const list = el("div", { class: "moves" });
  v.moves.forEach((m, i) => {
    const later = m.k !== "pass" && !v.filtered.includes(i);
    const label = m.k === "pass"
      ? (v.pend.passed ? `Pass (ends ${STEP_LABEL[v.pend.step]})` : "Pass priority")
      : buttonLabel(v, m);
    const b = el("button", { type: "button", class: m.k === "pass" ? "primary" : "", onclick: () => play(i) },
      el("span", {}, label, later ? el("span", { class: "later", title: "The solver's exploration filter (REDUCTION.md R6) drops this: the same action at a later window is at least as good." }, "usually better later") : null),
      el("span", { class: "cost" }, costOf(m, me)));
    list.append(b);
  });
  const manaNote = me.pool ? `You have ${me.pool} mana floating; it empties when the step ends.` : me.city ? "Paying a cost taps City of Traitors for {C}{C}; leftover mana empties at the end of the step." : "City of Traitors is tapped.";
  box.append(el("p", { class: "hint" }, manaNote), list,
    el("div", { class: "row" }, el("button", { type: "button", onclick: () => { passUntilTurn = turnNow() + 1; play(v.moves.findIndex((m) => m.k === "pass")); } },
      "Pass until next turn"), el("span", { class: "dim small" }, "stops if the engine acts")));
}

function stepper(label, value, min, max, onchange) {
  const out = el("output", {}, String(value));
  const dec = el("button", { type: "button", "aria-label": `fewer ${label}`, onclick: () => onchange(Math.max(min, value - 1)) }, "−");
  const inc = el("button", { type: "button", "aria-label": `more ${label}`, onclick: () => onchange(Math.min(max, value + 1)) }, "+");
  dec.disabled = value <= min;
  inc.disabled = value >= max;
  return el("span", { class: "stepper" }, dec, out, inc);
}

const sameList = (a, b) => a.length === b.length && a.every((x, i) => JSON.stringify(x) === JSON.stringify(b[i]));

// attack: choose Walkers and a number of Thopters
let attackDraft = null;
function attackControls(box, v) {
  const me = v[settings.human];
  const ready = [...new Set(v.moves.flatMap((m) => m.ws))].sort();
  const maxT = Math.max(0, ...v.moves.map((m) => m.t));
  if (!attackDraft || attackDraft.key !== v.fmt) attackDraft = { key: v.fmt, ws: [], t: 0 };
  const d = attackDraft;
  const find = () => v.moves.findIndex((m) => sameList(m.ws, [...d.ws].sort()) && m.t === d.t);
  const g = el("div", { class: "group" }, el("div", { class: "group-title" }, "Attack with"));
  if (ready.length) {
    g.append(el("div", { class: "seg" }, ready.map((i) => el("button", {
      type: "button", class: d.ws.includes(i) ? "on" : "", "aria-pressed": d.ws.includes(i) ? "true" : "false",
      onclick: () => { d.ws = d.ws.includes(i) ? d.ws.filter((x) => x !== i) : [...d.ws, i]; render(); },
    }, walkerName(me, i)))));
  } else g.append(el("span", { class: "empty" }, "No Walker can attack (tapped or summoning sick)."));
  if (maxT > 0) g.append(el("div", { class: "row" }, "Thopters:", stepper("Thopters", d.t, 0, maxT, (n) => { d.t = n; render(); }), el("span", { class: "dim small" }, `of ${maxT} untapped`)));
  const i = find();
  const none = v.moves.findIndex((m) => m.ws.length === 0 && m.t === 0);
  box.append(g, el("div", { class: "row" },
    el("button", { type: "button", class: "primary", disabled: i < 0 || i === none, onclick: () => play(i) }, "Declare attack"),
    el("button", { type: "button", onclick: () => play(none) }, "No attack")));
}

// block: assign each untapped Walker, and Thopters per attacker
let blockDraft = null;
function blockControls(box, v) {
  const me = v[settings.human];
  const att = v[v.active];
  const c = v.cmb;
  if (!blockDraft || blockDraft.key !== v.fmt) blockDraft = { key: v.fmt, wb: me.bf.map(() => null), tb: c.atk.map(() => 0), tr: 0 };
  const d = blockDraft;
  const find = () => v.moves.findIndex((m) => sameList(m.wb, d.wb) && sameList(m.tb, d.tb) && m.tr === d.tr);
  const usedT = d.tb.reduce((a, b) => a + b, 0) + d.tr;
  const free = me.thopU - usedT;
  if (me.bf.length && c.atk.length) {
    const g = el("div", { class: "group" }, el("div", { class: "group-title" }, "Your Walkers"));
    me.bf.forEach((w, j) => {
      if (w.tapped) { g.append(el("div", {}, `${walkerName(me, j)}: tapped, can't block`)); return; }
      g.append(el("div", {}, el("div", { class: "small" }, walkerName(me, j)), el("div", { class: "seg" },
        el("button", { type: "button", class: d.wb[j] === null ? "on" : "", onclick: () => { d.wb[j] = null; render(); } }, "Don't block"),
        c.atk.map((ai, a) => el("button", { type: "button", class: d.wb[j] === a ? "on" : "", onclick: () => { d.wb[j] = a; render(); } }, `Block ${walkerName(att, ai)}`)))));
    });
    box.append(g);
  } else if (me.bf.length) {
    box.append(el("p", { class: "hint" }, "Walkers can't block Thopters (flying)."));
  }
  if (me.thopU > 0) {
    const g = el("div", { class: "group" }, el("div", { class: "group-title" }, `Your untapped Thopters (${me.thopU})`));
    c.atk.forEach((ai, a) => {
      g.append(el("div", { class: "row" }, `On ${walkerName(att, ai)}:`, stepper("Thopters", d.tb[a], 0, d.tb[a] + free, (n) => { d.tb[a] = n; render(); })));
    });
    if (c.atkThop > 0) {
      g.append(el("div", { class: "row" }, `On attacking Thopters (${c.atkThop}):`, stepper("Thopters", d.tr, 0, Math.min(c.atkThop, d.tr + free), (n) => { d.tr = n; render(); })));
    }
    box.append(g);
  }
  // damage preview
  let dmg = c.atkThop - d.tr;
  c.atk.forEach((ai, a) => {
    if (d.tb[a] === 0 && !d.wb.includes(a)) dmg += att.bf[ai].c;
  });
  box.append(el("p", { class: "preview" }, dmg > 0 ? `Unblocked damage: ${dmg} (your life ${me.life} → ${me.life - dmg}${me.life - dmg <= 0 ? ", lethal" : ""}).` : "No damage gets through to you."));
  const i = find();
  const none = v.moves.findIndex((m) => m.wb.every((x) => x === null) && m.tb.every((x) => x === 0) && m.tr === 0);
  box.append(el("div", { class: "row" },
    el("button", { type: "button", class: "primary", disabled: i < 0, onclick: () => play(i) }, "Declare blocks"),
    el("button", { type: "button", onclick: () => play(none) }, "No blocks")));
}

// order: per attacker blocked by two or more, pick an order
let orderDraft = null;
function orderControls(box, v) {
  const att = v[v.active];
  const def = v[opp(v.active)];
  const c = v.cmb;
  if (!orderDraft || orderDraft.key !== v.fmt) orderDraft = { key: v.fmt, os: v.moves[0].os.map((x) => x) };
  const d = orderDraft;
  box.append(el("p", { class: "hint" }, "Choose the damage assignment order for each attacker blocked by more than one creature. Damage can only go to a later blocker once every earlier one has lethal damage."));
  c.atk.forEach((ai, a) => {
    const options = [];
    for (const m of v.moves) if (!options.some((o) => JSON.stringify(o) === JSON.stringify(m.os[a]))) options.push(m.os[a]);
    if (options.length < 2) return;
    box.append(el("div", { class: "group" }, el("div", { class: "group-title" }, walkerName(att, ai)),
      el("div", { class: "seg" }, options.map((o) => el("button", {
        type: "button", class: JSON.stringify(d.os[a]) === JSON.stringify(o) ? "on" : "",
        onclick: () => { d.os[a] = o; render(); },
      }, o.map((b) => blockerName(def, b)).join(" → "))))));
  });
  const i = v.moves.findIndex((m) => JSON.stringify(m.os) === JSON.stringify(d.os));
  box.append(el("div", { class: "row" }, el("button", { type: "button", class: "primary", disabled: i < 0, onclick: () => play(i) }, "Confirm order")));
}

// damage: per blocked attacker, how many blockers to kill
let damageDraft = null;
function damageControls(box, v) {
  const att = v[v.active];
  const def = v[opp(v.active)];
  const c = v.cmb;
  if (!damageDraft || damageDraft.key !== v.fmt) damageDraft = { key: v.fmt, js: v.moves[v.moves.length - 1].js.slice() };
  const d = damageDraft;
  box.append(el("p", { class: "hint" }, "Choose which blockers each attacker kills. Killing a Walker gives its owner a Thopter per counter, so killing fewer can be better."));
  c.atk.forEach((ai, a) => {
    const options = [...new Set(v.moves.map((m) => m.js[a]))].sort((x, y) => x - y);
    const bs = c.blk[a];
    if (options.length < 2) return;
    box.append(el("div", { class: "group" }, el("div", { class: "group-title" }, `${walkerName(att, ai)} blocked by ${bs.map((b) => blockerName(def, b)).join(", ")}`),
      el("div", { class: "seg" }, options.map((j) => el("button", {
        type: "button", class: d.js[a] === j ? "on" : "", onclick: () => { d.js[a] = j; render(); },
      }, j === 0 ? "Kill none" : `Kill ${bs.slice(0, j).map((b) => blockerName(def, b)).join(" + ")}`)))));
  });
  const i = v.moves.findIndex((m) => sameList(m.js, d.js));
  box.append(el("div", { class: "row" }, el("button", { type: "button", class: "primary", disabled: i < 0, onclick: () => play(i) }, "Deal damage")));
}

function shuffleControls(box, v) {
  box.append(el("p", { class: "hint" }, "Elixir shuffled B's graveyard and Elixir into B's library. In 3-Card Blind a shuffle resolves in the way most favourable to the opponent, so you choose the order. B draws from the top."));
  const list = el("div", { class: "moves" });
  v.moves.forEach((m, i) => list.append(el("button", { type: "button", onclick: () => play(i) }, `Top → bottom: ${m.lib.map(shortCard).join(", ")}`)));
  box.append(list);
}

// ---- setup and wiring ----

function openSetup() {
  const f = $("setup-form");
  f.human.value = settings.human;
  f.starter.value = settings.starter;
  f.budget.value = String(settings.budget);
  f.autopass.value = settings.autopass;
  f.lifeA.value = settings.lifeA;
  f.lifeB.value = settings.lifeB;
  $("setup-cancel").hidden = !game;
  $("setup").showModal();
}

function restartSame() {
  newGame();
  flashStatus = "";
  save();
  advance();
}

function wire() {
  $("setup").addEventListener("close", () => {
    if ($("setup").returnValue !== "start") {
      if (!game) openSetup();
      return;
    }
    const f = $("setup-form");
    const life = (x) => Math.max(1, Math.min(200, Math.floor(Number(x)) || 20));
    settings = {
      human: f.human.value,
      starter: f.starter.value,
      budget: Number(f.budget.value) || 1000,
      autopass: f.autopass.value,
      lifeA: life(f.lifeA.value),
      lifeB: life(f.lifeB.value),
    };
    $("app").hidden = false;
    restartSame();
  });
  $("btn-new").addEventListener("click", openSetup);
  $("btn-restart").addEventListener("click", () => { if (game) restartSame(); });
  $("btn-undo").addEventListener("click", () => { flashStatus = ""; undo(); });
  $("btn-draw").addEventListener("click", declareDraw);
  $("btn-about").addEventListener("click", () => $("about").showModal());
  $("show-passes").addEventListener("change", renderLog);
}

async function main() {
  try {
    engine = await loadEngine(new URL("engine.wasm", import.meta.url));
  } catch (err) {
    $("loading").textContent = `Could not load the engine (${err.message}). Serve this folder over HTTP, e.g. "python3 -m http.server", rather than opening the file directly.`;
    return;
  }
  wire();
  $("loading").hidden = true;
  if (restore()) {
    $("app").hidden = false;
    advance();
  } else {
    openSetup();
  }
}

main();
