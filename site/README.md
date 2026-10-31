# Play site

A static web page for playing the matchup against a computer opponent:

- A: Hangarback Walker ×2, City of Traitors
- B: Hangarback Walker, Elixir of Immortality, City of Traitors

You choose which side you play and who goes first. The page offers only legal
moves, as buttons and small forms. It shows the whole board and keeps a move
log, and it has undo, restart, draw, and a saved game that survives a reload.

## Layout

| Path | What it is |
| --- | --- |
| `engine/` | Rust crate `tcb-engine`, built to `engine.wasm`. |
| `engine/src/lib.rs` | Includes `rsolver/src/{model,reduce,fix,walk}.rs` by `#[path]`, unchanged, and exports a small C-ABI API for JavaScript. |
| `engine/src/search.rs` | The computer opponent (see below). |
| `engine/src/bench.rs` | Native tool: engine self-play and timing, and `trace` for the tests. |
| `web/` | `index.html`, `style.css`, `app.js` (UI), `engine.js` (WASM wrapper), `worker.js` (search in a Web Worker). |
| `test/walk-check.mjs` | Byte-for-byte comparison with `rsolver walk`. |
| `test/trace-check.mjs` | Targeted traces (multi-blocks, damage orders) compared with the native build. |
| `test/smoke-firefox.mjs` | Headless Firefox smoke test over WebDriver BiDi. |
| `build.sh`, `check.sh`, `shell.nix` | Build, test and toolchain. |
| `dist/` | Build output (git-ignored). |
| `target/` | Cargo build directory (git-ignored). |

## Build and serve

```sh
nix-shell site/shell.nix --run site/build.sh      # writes site/dist/
python3 -m http.server 8000 -d site/dist           # then open http://localhost:8000/
```

`site/shell.nix` provides cargo, rustc, lld and node. The nixpkgs rustc
already ships the `wasm32-unknown-unknown` standard library. No wasm-bindgen
or wasm-pack is needed.

Without nix, a rustup toolchain works too, and doesn't need lld because the
wasm target links with rustup's bundled `rust-lld`:

```sh
rustup target add wasm32-unknown-unknown
site/build.sh
```

Build notes:

- The only crates are `md-5` and `rustc-hash`, the same ones rsolver uses.
  Offline, set `CARGO_NET_OFFLINE=true`.
- The build uses the lockfile (`--locked`) and `-j4`. Set `JOBS` to change
  the job count.
- An existing `CARGO_TARGET_DIR` is respected.

`dist/` is plain static files: about 260 KB, of which `engine.wasm` is about
200 KB. It also contains `.nojekyll`. Any static file server works, at any
path, because every reference is relative: `style.css` and `app.js`, plus
`new URL(..., import.meta.url)` for the WASM and the worker. Opening `index.html` straight from
disk (`file://`) does **not** work, because browsers refuse to fetch WASM or
start module workers from `file://` URLs.

## GitHub Pages

`.github/workflows/pages.yml` publishes the site to
<https://skyb0rg007.github.io/three-card-blind-proofs/>.

- **Triggers:** pushes to `main` that touch `site/**`, `rsolver/src/**` or
  the workflow itself. It can also be run by hand from the Actions tab.
- **Steps:** it installs stable Rust with the wasm32 target
  (`dtolnay/rust-toolchain`) and runs `site/build.sh`. Then it runs
  `site/check.sh 5000`, so an engine that drifts from `rsolver walk` is
  never deployed. Finally it uploads `site/dist` with the official Pages
  actions.

**One-time setup:** in the repository, open **Settings → Pages** and set
**Source** to **GitHub Actions**.

The build reads `rsolver/src/*.rs` and `rsolver/Cargo.{toml,lock}`, which
`check.sh` uses to build rsolver, so those files must be committed.

All of a user's `*.github.io` project pages share one origin, and so one
`localStorage`. The saved game therefore uses a repository-namespaced key,
`three-card-blind-proofs/hangarback-game/v1`.

To test the sub-path locally, serve a parent directory that holds the build
under the repository name:

```sh
mkdir -p /tmp/pages && cp -r site/dist /tmp/pages/three-card-blind-proofs
python3 -m http.server 8732 -d /tmp/pages &
node site/test/smoke-firefox.mjs "$(command -v firefox)" \
  http://127.0.0.1:8732/three-card-blind-proofs/ /tmp/smoke 150
```

The smoke test checks that every resource the page loads comes from below
its own URL, and that the storage key is namespaced.

## The rules engine

The page doesn't re-implement any rules. `engine.wasm` is
`rsolver/src/model.rs`, the port of `theories/Model.v`, compiled
unchanged, together with `reduce.rs` and `fix.rs`.

- A game is stored as `[starter, lifeA, lifeB, m1, m2, …]`, where each `m`
  is an index into `model::moves` of the state at that point.
- Undo, the saved game and the worker all just replay that record.
- `view()` returns the state and its legal moves as JSON. The UI builds its
  controls from that move list, so it can only submit legal moves.

### Validation

```sh
nix-shell site/shell.nix --run 'site/check.sh 20000'
```

1. **`test/walk-check.mjs`** runs `rsolver walk SEED STEPS [bias]` for each
   seed, with and without `bias`, and compares it with two outputs:
   - the walk generated inside WASM;
   - the same walk driven from JavaScript through the page's own API
     (`load`/`play`/`view`, using the walk's seeded choices).

   Both must match the native output byte for byte. That covers every
   state, the M/F/AM/BM move lists, and the turn-start keys and MD5
   digests. The default seeds are 1, 2, 7, 42, 1234, 987654321 and
   12345678901, which exercises the high seed word. At 20,000 steps every
   walk is identical.
2. **`test/trace-check.mjs`** covers the gap left by the random walk, which
   never reaches a multi-block (`ChooseOrder`). It plays 60 games that
   prefer large blocks through the WASM API. The native build of the same
   library then replays each record (`engine-bench trace`), and the two
   outputs must be identical.

`check.sh` uses `rsolver/target/release/rsolver` if it exists. Otherwise it
builds rsolver into `site/target/rsolver`, so it never touches
`rsolver/target`.

Browser smoke test (needs a Firefox binary; it uses Firefox's built-in
WebDriver BiDi, so geckodriver isn't needed):

```sh
python3 -m http.server 8731 -d site/dist &
node site/test/smoke-firefox.mjs "$(command -v firefox)" http://127.0.0.1:8731/ /some/tmp/dir 150
```

## The computer opponent

The opponent is a **strong bounded search, not optimal play.** The game is
unsolved (see `REDUCTION.md`), and the solver's tables are far too big to
ship. The page says this in the setup dialog and in About.

- **Depth counts whole turns.** Iterative deepening goes 0, 1, 2, … turns
  past the current one. Inside a turn, every decision is searched exactly
  by minimax: each pass, attack, block, damage order and assignment, and
  library order.
- **Transposition table.** It is keyed on (canonical position, turns left)
  and stored as 128-bit SipHash keys, capped at about 70 MB. The many
  orders of passing that reach the same position are searched only once.
  The table persists in the worker between moves.
- **Move sets.**
  - At the root, the engine chooses among the moves in `reduce::filtered`,
    the exploration filter of REDUCTION.md R6. It drops moves that are
    matched by the same move at a later window.
  - Inside the tree, both sides use the macro sets `reduce::a_macro` and
    `reduce::b_macro`. These keep the extreme attacks, blocks and damage
    assignments, which bounds branching when there are many Thopters.
- **Horizon evaluation** (A's point of view) at a turn start:
  - the life difference;
  - counters (3 each);
  - Walker bodies (6 on the battlefield, 5 in hand);
  - Thopters (3 each);
  - an untapped City;
  - B's Elixir, by zone and library position, and graveyard Walkers it
    will shuffle back;
  - ±400 when the player about to attack threatens lethal damage. This
    counts unblockable Thopters and Walkers beyond the defender's blockers,
    with 5 life added if B can still activate Elixir.
  - A win scores ±1,000,000, and a sooner win scores higher.
- **Time budget.** You choose 0.3 s, 1 s or 3 s. The search runs in a Web
  Worker, so the page stays responsive. An unfinished iteration is
  discarded. Decisions with only one candidate are played at once.
- **Typical depth.** At 1 s, native and WASM run at about 1.5M positions/s
  and reach 4 to 8 turns ahead. Self-play stays balanced for 70+ turns,
  which fits the research below. The engine beats a random player from
  both sides.

**Research so far** (shown in the About panel):

- From the A-first opening, the solver shows A cannot force a win: B
  survives from 20 life.
- A wins if B starts with 15 life or less.
- B is believed to need about 25 life to force a win.
- So the game is believed to be a draw. That is unproven for B's side.

## Long games and draws

Walkers grow forever and Elixir loops, so a game need not end. The page
offers a draw in two cases:

- the same turn-start position has occurred three times;
- the game reaches turn 60. If you keep playing, it asks again 30 turns
  later.

The Draw button ends the game as a draw at any time.

## Playing notes

- **Automatic passing.** By default, the page passes for you at windows
  where every non-pass move is one that REDUCTION.md R6 drops. It still
  stops at your own main phases whenever you can cast something.
  - You can switch to passing only when Pass is your only legal move.
  - Moves the filter would drop are still offered, marked "usually better
    later".
- **Pass until next turn** passes for you until the next turn begins. It
  stops early if the engine does something, or if you have an attack,
  block or other non-priority decision.
- **Undo** takes back your last deliberate decision, including any moves
  the engine made after it.
- **Starting life** can be changed under "Variant" in the setup dialog.
  The real game uses 20.
