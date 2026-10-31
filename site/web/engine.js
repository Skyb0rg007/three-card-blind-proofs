// Thin wrapper around engine.wasm (site/engine, which compiles
// rsolver/src/model.rs unchanged). Used by the page, the search worker and
// the node walk harness.

const decoder = new TextDecoder();

export async function loadEngine(source) {
  let bytes;
  if (source instanceof ArrayBuffer || ArrayBuffer.isView(source)) {
    bytes = source;
  } else {
    const r = await fetch(source);
    if (!r.ok) throw new Error(`could not fetch ${source}: ${r.status}`);
    bytes = await r.arrayBuffer();
  }
  const imports = { env: { now_ms: () => performance.now() } };
  const { instance } = await WebAssembly.instantiate(bytes, imports);
  return new Engine(instance.exports);
}

export class Engine {
  constructor(ex) {
    this.ex = ex;
  }

  out() {
    const p = this.ex.out_ptr();
    const n = this.ex.out_len();
    return decoder.decode(new Uint8Array(this.ex.memory.buffer, p, n));
  }

  /// Replace the current state with the game record
  /// [starter (0 = A, 1 = B), lifeA, lifeB, ...move indices].
  /// Returns how many moves were legal and applied.
  load(rec) {
    const n = rec.length;
    const p = this.ex.alloc_words(n);
    new Uint32Array(this.ex.memory.buffer, p, n).set(rec);
    const k = this.ex.load(p, n);
    this.ex.free_words(p, n);
    return k;
  }

  /// Apply move `i` (an index into view().moves). Returns false if illegal.
  play(i) {
    return this.ex.play(i) === 1;
  }

  view() {
    this.ex.view();
    return JSON.parse(this.out());
  }

  /// The block `rsolver walk` prints for the current state.
  walkBlock() {
    this.ex.walk_block();
    return this.out();
  }

  /// The whole walk, generated inside WASM.
  walk(seed, steps, bias) {
    const s = BigInt(seed);
    this.ex.walk(Number(s & 0xffffffffn), Number((s >> 32n) & 0xffffffffn), steps, bias ? 1 : 0);
    return this.out();
  }

  think(budgetMs, maxDepth = 40) {
    this.ex.think(budgetMs, maxDepth);
    return JSON.parse(this.out());
  }

  resetSearch() {
    this.ex.reset_search();
  }
}
