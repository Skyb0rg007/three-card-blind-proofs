// Browser smoke test: drives headless Firefox over WebDriver BiDi (no
// geckodriver needed) against a served copy of site/dist.
//
//   python3 -m http.server 8731 -d site/dist &
//   node site/test/smoke-firefox.mjs FIREFOX_BIN http://127.0.0.1:8731/ OUT_DIR [CLICKS]
//
// It plays a game with random legal clicks at phone width as A and as B,
// checks for page errors and horizontal overflow, exercises undo, restart
// and draw, and saves screenshots to OUT_DIR.

import { spawn } from "node:child_process";
import { mkdirSync, writeFileSync, rmSync } from "node:fs";
import { join } from "node:path";

const [firefox, url, outDir, clicksArg] = process.argv.slice(2);
const CLICKS = Number(clicksArg || 120);
mkdirSync(outDir, { recursive: true });
const profile = join(outDir, "profile");
rmSync(profile, { recursive: true, force: true });
mkdirSync(profile, { recursive: true });
const port = 9300 + Math.floor(Math.random() * 500);
const ff = spawn(firefox, ["--headless", "--no-remote", "-profile", profile, `--remote-debugging-port=${port}`, "about:blank"], {
  stdio: ["ignore", "ignore", "pipe"],
});
let stderr = "";
ff.stderr.on("data", (d) => (stderr += d));
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function connect() {
  for (let k = 0; k < 100; k++) {
    if (/WebDriver BiDi listening/.test(stderr)) break;
    await sleep(200);
  }
  return new Promise((res, rej) => {
    const ws = new WebSocket(`ws://127.0.0.1:${port}/session`);
    ws.onopen = () => res(ws);
    ws.onerror = (e) => rej(new Error("websocket: " + (e.message || "failed")));
  });
}

const ws = await connect();
let nextId = 1;
const pending = new Map();
const errors = [];
ws.onmessage = (ev) => {
  const msg = JSON.parse(ev.data);
  if (msg.id && pending.has(msg.id)) {
    const { res, rej } = pending.get(msg.id);
    pending.delete(msg.id);
    msg.type === "error" ? rej(new Error(`${msg.error}: ${msg.message}`)) : res(msg.result);
  } else if (msg.method === "log.entryAdded") {
    const e = msg.params;
    if (e.level === "error") errors.push(`${e.type}: ${e.text}`);
  }
};
const send = (method, params = {}) =>
  new Promise((res, rej) => {
    const id = nextId++;
    pending.set(id, { res, rej });
    ws.send(JSON.stringify({ id, method, params }));
  });

await send("session.new", { capabilities: {} });
await send("session.subscribe", { events: ["log.entryAdded"] });
const tree = await send("browsingContext.getTree", {});
const context = tree.contexts[0].context;

async function evaluate(expression) {
  const r = await send("script.evaluate", { expression, target: { context }, awaitPromise: true, resultOwnership: "none" });
  if (r.type === "exception") throw new Error("page exception: " + JSON.stringify(r.exceptionDetails.text));
  const v = r.result;
  return v.type === "undefined" || v.type === "null" ? null : v.value;
}
async function shot(name) {
  const r = await send("browsingContext.captureScreenshot", { context, origin: "document" });
  writeFileSync(join(outDir, name + ".png"), Buffer.from(r.data, "base64"));
}
async function waitFor(expr, ms = 20000) {
  const t0 = Date.now();
  while (Date.now() - t0 < ms) {
    if (await evaluate(expr)) return true;
    await sleep(100);
  }
  throw new Error("timed out waiting for " + expr);
}
const check = (cond, what) => {
  if (!cond) throw new Error("check failed: " + what);
  console.log("ok   " + what);
};

// helpers evaluated in the page
const STATUS = `document.getElementById('status').textContent`;
const MY_TURN = `${STATUS}.startsWith('Your decision')`;
const OVER = `/win|draw/.test(${STATUS})`;
const OVERFLOW = `document.documentElement.scrollWidth > window.innerWidth + 1`;

async function startGame(human, starter) {
  await evaluate(`(() => {
    const d = document.getElementById('setup');
    if (!d.open) document.getElementById('btn-new').click();
    const f = document.getElementById('setup-form');
    f.human.value = '${human}'; f.starter.value = '${starter}'; f.budget.value = '300';
    document.getElementById('setup-start').click();
  })()`);
  await waitFor(`${MY_TURN} || ${OVER}`);
}

/// Click a random enabled button in the controls (never the shortcut).
async function randomClick(seed) {
  return evaluate(`(() => {
    const bs = [...document.querySelectorAll('#controls button')].filter(b => !b.disabled && b.textContent !== 'Pass until next turn' && !b.textContent.includes('X = 0'));
    if (!bs.length) return null;
    // prefer confirm buttons sometimes so composed forms get submitted
    const confirm = bs.filter(b => b.classList.contains('primary'));
    const pick = (${seed} % 3 === 0 && confirm.length) ? confirm[${seed} % confirm.length] : bs[${seed} % bs.length];
    const t = pick.textContent;
    pick.click();
    return t;
  })()`);
}

async function playRandom(n, label) {
  let clicks = 0;
  let seen = new Set();
  for (let k = 0; k < n; k++) {
    await waitFor(`${MY_TURN} || ${OVER}`, 30000);
    if (await evaluate(OVER)) break;
    const kind = await evaluate(`document.getElementById('status').firstChild.textContent`);
    const what = kind.replace(/^Your decision \([AB]\): /, "").replace(/ in .*/, "");
    if (!seen.has(what) && what !== "priority") await shot(`decision-${label.replace(/\W+/g, "-")}-${what.replace(/\W+/g, "-")}`);
    seen.add(what);
    const t = await randomClick(Math.floor(Math.random() * 1e6));
    if (t) clicks++;
    if (await evaluate(OVERFLOW)) throw new Error(`horizontal overflow after clicking "${t}"`);
    await sleep(30);
  }
  console.log(`     ${label}: ${clicks} clicks; decisions seen: ${[...seen].join(" | ")}`);
  return clicks;
}

try {
  await send("browsingContext.setViewport", { context, viewport: { width: 390, height: 844 } });
  await send("browsingContext.navigate", { context, url, wait: "complete" });
  await waitFor(`document.getElementById('setup').open`);
  check(true, "setup dialog opens on first visit");
  await shot("01-setup-phone");
  check(!(await evaluate(OVERFLOW)), "no horizontal overflow at 390px (setup)");

  await startGame("A", "A");
  check(await evaluate(MY_TURN), "game starts with a decision for the human (A, A first)");
  const firstControls = await evaluate(`[...document.querySelectorAll('#controls button')].map(b => b.textContent).join(' / ')`);
  console.log("     first controls: " + firstControls);
  check(/Cast Hangarback Walker, X = 1/.test(firstControls), "casting a Walker is offered in A's first main phase");
  await shot("02-first-decision-phone");

  // cast a Walker, then check the board shows it
  await evaluate(`[...document.querySelectorAll('#controls button')].find(b => b.textContent.startsWith('Cast Hangarback Walker, X = 1')).click()`);
  await waitFor(`document.querySelector('#side-bottom .card .pt') !== null`);
  check(/1\/1/.test(await evaluate(`document.querySelector('#side-bottom').textContent`)), "cast Walker appears as 1/1 on your battlefield");
  check(/summoning sick/.test(await evaluate(`document.querySelector('#side-bottom').textContent`)), "new Walker shows summoning sickness");

  // undo it
  await evaluate(`document.getElementById('btn-undo').click()`);
  await waitFor(MY_TURN);
  check((await evaluate(`document.querySelectorAll('#side-bottom .cards')[0].textContent`)).includes("no permanents"), "undo takes the cast back");

  await playRandom(CLICKS, "random play as A");
  await shot("03-midgame-A-phone");
  const logLen = await evaluate(`document.querySelectorAll('#log li').length`);
  check(logLen > 5, `move log has entries (${logLen})`);

  // restart as B with B going first
  await startGame("B", "B");
  check(await evaluate(`document.querySelector('#side-bottom .who').textContent.includes('Player B')`), "playing as B puts B at the bottom");
  await playRandom(CLICKS, "random play as B");
  await shot("04-midgame-B-phone");

  // draw
  if (!(await evaluate(OVER))) {
    await evaluate(`document.getElementById('btn-draw').click()`);
    await waitFor(OVER);
    check(/draw/.test(await evaluate(STATUS)), "declaring a draw ends the game");
  }

  // desktop layout and a reload resumes the game
  await send("browsingContext.setViewport", { context, viewport: { width: 1280, height: 900 } });
  await startGame("A", "B");
  await playRandom(20, "desktop warm-up");
  const before = await evaluate(`document.querySelectorAll('#log li').length`);
  await send("browsingContext.navigate", { context, url, wait: "complete" });
  await waitFor(`!document.getElementById('app').hidden`);
  const after = await evaluate(`document.querySelectorAll('#log li').length`);
  check(after === before, `reload resumes the saved game (${before} log lines)`);
  await shot("05-desktop");
  check(!(await evaluate(OVERFLOW)), "no horizontal overflow at 1280px");

  // Under a sub-path (GitHub Pages project site) every asset must load from
  // below the page's own directory, and the saved game must use a key that
  // won't collide with other pages on the same origin.
  const base = new URL(".", url).href;
  const resources = await evaluate(`JSON.stringify([location.href, ...performance.getEntriesByType('resource').map(e => e.name)])`);
  const outside = JSON.parse(resources).filter((u) => !u.startsWith(base));
  console.log(`     resources: ${JSON.parse(resources).map((u) => u.replace(base, "./")).join(", ")}`);
  check(outside.length === 0, `all resources load from under ${base}` + (outside.length ? ": " + outside.join(", ") : ""));
  const keys = JSON.parse(await evaluate(`JSON.stringify(Object.keys(localStorage))`));
  check(keys.length > 0 && keys.every((k) => k.startsWith("three-card-blind-proofs/")), `localStorage keys are namespaced (${keys.join(", ")})`);

  check(errors.length === 0, "no console errors" + (errors.length ? ": " + errors.join("; ") : ""));
  console.log("smoke test passed");
} catch (e) {
  console.error("FAILED: " + e.message);
  if (errors.length) console.error("console errors: " + errors.join("; "));
  try { await shot("failure"); } catch (_) {}
  process.exitCode = 1;
} finally {
  try { await send("session.end", {}); } catch (_) {}
  ws.close();
  ff.kill("SIGTERM");
}
