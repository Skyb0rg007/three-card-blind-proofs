// Runs the engine's search off the main thread, so the page stays
// responsive. The transposition table persists between requests.
import { loadEngine } from "./engine.js";

const ready = loadEngine(new URL("engine.wasm", import.meta.url));

self.onmessage = async (e) => {
  const { id, rec, budget } = e.data;
  try {
    const engine = await ready;
    const applied = engine.load(rec);
    if (applied !== rec.length - 3) throw new Error("game record did not replay");
    const r = engine.think(budget, 40);
    self.postMessage({ id, ok: true, ...r });
  } catch (err) {
    self.postMessage({ id, ok: false, error: String(err && err.message ? err.message : err) });
  }
};
