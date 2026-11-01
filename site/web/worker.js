// Runs the engine off the main thread, so the page stays responsive.
//
// Requests:
//   { type: "cert-load" }          load the B-first certificate in the
//                                  background (once); replies
//                                  { type: "cert-ready", ok, ... }.
//   { id, rec, mode: "cert" }      B's certified moves for the game record
//                                  (waits for the certificate; no time limit).
//   { id, rec, budget }            the bounded heuristic search.
// The search's transposition table persists between requests.
import { loadEngine, fetchCertTable } from "./engine.js";

const ready = loadEngine(new URL("engine.wasm", import.meta.url));
let cert = null; // promise of the load report

function loadCert() {
  if (!cert) {
    cert = (async () => {
      const engine = await ready;
      const t0 = performance.now();
      const f = await fetchCertTable(new URL("cert-bfirst.bin.gz", import.meta.url));
      const t1 = performance.now();
      const r = engine.loadCert(f.bytes);
      if (!r.ok) throw new Error(`certificate table: ${r.error}`);
      return {
        records: r.records,
        checksum: r.checksum,
        gzBytes: f.gzBytes,
        bytes: f.bytes.length,
        fetchMs: f.fetchMs,
        inflateMs: f.inflateMs,
        decodeMs: performance.now() - t1,
        totalMs: performance.now() - t0,
      };
    })();
  }
  return cert;
}

const errText = (err) => String(err && err.message ? err.message : err);

self.onmessage = async (e) => {
  const msg = e.data;
  if (msg.type === "cert-load") {
    try {
      self.postMessage({ type: "cert-ready", ok: true, ...(await loadCert()) });
    } catch (err) {
      cert = null; // allow a retry
      self.postMessage({ type: "cert-ready", ok: false, error: errText(err) });
    }
    return;
  }
  const { id, rec, budget, mode } = msg;
  try {
    const engine = await ready;
    if (mode === "cert") await loadCert();
    const applied = engine.load(rec);
    if (applied !== rec.length - 3) throw new Error("game record did not replay");
    if (mode === "cert") {
      self.postMessage({ id, mode, ...engine.certPlan() });
    } else {
      const r = engine.think(budget, 40);
      self.postMessage({ id, mode: "search", ok: true, ...r });
    }
  } catch (err) {
    self.postMessage({ id, mode, ok: false, error: errText(err) });
  }
};
