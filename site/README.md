# Play site

A static web page for playing the matchup against a computer opponent:

- A: Hangarback Walker ×2, City of Traitors
- B: Hangarback Walker, Elixir of Immortality, City of Traitors

You choose which side you play and who goes first. When you play A and B goes
first, the computer plays B from the certificate Rocq checks for the B-first
theorem, so it cannot lose (see [Certified play](#certified-play-for-b)). In
the other set-ups it plays a bounded heuristic search. The page offers only legal
moves, as buttons and small forms. It shows the whole board and keeps a move
log, and it has undo, restart, draw, and a saved game that survives a reload.

## Layout

| Path | What it is |
| --- | --- |
| `engine/` | Rust crate `tcb-engine`, built to `engine.wasm`. |
| `engine/src/lib.rs` | Includes `rsolver/src/{model,reduce,fix,walk}.rs` by `#[path]`, unchanged, and exports a small C-ABI API for JavaScript. |
| `engine/src/search.rs` | The heuristic computer opponent (see below). |
| `engine/src/cert.rs` | Certified B: the certificate table, and a port of Rocq's `key`, `enc`/`dec`, `lookup`/`below` and `check_win` that chooses B's moves. |
| `engine/src/certtest.rs` | Self-play of certified B against several A players, and the checker trace for the OCaml comparison. |
| `engine/src/certtool.rs` | Native tool `cert-tool`: packs `proofs/bfirst/Data.v` for the site, checks every record, self-play. |
| `engine/src/bench.rs` | Native tool: engine self-play and timing, and `trace` for the tests. |
| `web/` | `index.html`, `style.css`, `app.js` (UI), `engine.js` (WASM wrapper), `worker.js` (search and certified play in a Web Worker). |
| `test/walk-check.mjs` | Byte-for-byte comparison with `rsolver walk` (or the extracted OCaml model's `main.exe walk`). |
| `test/trace-check.mjs` | Targeted traces (multi-blocks, damage orders) compared with the native build. |
| `test/cert-check.mjs` | Certified B in WASM: loads the table as the worker does, then self-play. |
| `test/cert-ocaml.sh`, `test/cert_ocaml.ml` | Certified B against the Rocq model extracted to OCaml. |
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

`dist/` is plain static files: about 1.6 MB. `engine.wasm` is about 240 KB and
the certificate table `cert-bfirst.bin.gz` is about 1.3 MB; the page fetches
the table only for certified play. The build makes the table from
`proofs/bfirst/Data.v.xz` with `cert-tool pack` (a native build of the same
crate), so it also needs `xz` and `gzip`. It also contains `.nojekyll`. Any static file server works, at any
path, because every reference is relative: `style.css` and `app.js`, plus
`new URL(..., import.meta.url)` for the WASM and the worker. Opening `index.html` straight from
disk (`file://`) does **not** work, because browsers refuse to fetch WASM or
start module workers from `file://` URLs.

## GitHub Pages

`.github/workflows/pages.yml` publishes the site to
<https://skyb0rg007.github.io/three-card-blind-proofs/>.

- **Triggers:** pushes to `main` that touch `site/**`, `rsolver/src/**`,
  `proofs/bfirst/Data.v.xz` or the workflow itself. It can also be run by hand from the Actions tab.
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
its own URL, and that the storage key is namespaced. It also plays a game as
A against the certified B, which B must win with no error. It checks the
"Not certified" fallback for B on 16 life, and prints the table's load
timings.

## The rules engine

The page doesn't re-implement any rules. `engine.wasm` is
`rsolver/src/model.rs`, the port of `spec/Model.v`, compiled
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

3. **The certificate.** `cert-tool same` checks that the gzipped table in
   `dist/` holds exactly the arrays and constants of `proofs/bfirst/Data.v`.
   Then **`test/cert-check.mjs`** loads the table into WASM the way the
   worker does and plays `CERT_GAMES` (default 200) games of certified B
   against each A player of the next section, plus games driven from
   JavaScript through `load`/`certPlan`/`play`. B must win every one.

`check.sh` uses `rsolver/target/release/rsolver` if it exists. Otherwise it
builds rsolver into `site/target/rsolver`, so it never touches
`rsolver/target`.

Browser smoke test (needs a Firefox binary; it uses Firefox's built-in
WebDriver BiDi, so geckodriver isn't needed):

```sh
python3 -m http.server 8731 -d site/dist &
node site/test/smoke-firefox.mjs "$(command -v firefox)" http://127.0.0.1:8731/ /some/tmp/dir 150
```

## Certified play for B

When you play A and B goes first, **the computer plays B from the
certificate, so it cannot lose.** Its moves are certified to win, not optimal:
it doesn't look for the fastest win, only for one the certificate
guarantees.

**The table.** It is exactly the table Rocq checks for the B-first theorem:
`proofs/bfirst/Data.v`, with the arrays `K1`, `K2`, `RV` (1,512,056 records)
and the constants `H = 15`, `ott = 14`, `tt = 14`, `fuel = 200`. `cert-tool
pack` parses `Data.v`, checks that it is sorted by key and rank, and writes
three varint columns behind a header with an FNV checksum. That file is 8.9 MB
raw and 1.3 MB gzipped. The worker fetches it only for this set-up,
decompresses it with `DecompressionStream`, and WASM decodes it and checks the
checksum and the opening record. In headless Firefox on a local server this
takes about 0.4 s: 0.1 s to inflate and 0.25 s to decode. It uses about
30 MB of WASM memory.

**The port.** `engine/src/cert.rs` ports what Rocq runs, line by line:

- from `proofs/core/Checker.v`: `key`, `entry`, `huge_event`, `too_many`
  and `is_turn_start`;
- from `proofs/core/Packed.v`: `enc`, `dec`, `lower`/`start`, `scan`,
  `scan_below`, `lookup`, `below`, `rank_of` and `val_of`, including the
  fuel of 32 and 64 and the check that a state decodes back to itself;
- from `proofs/core/WinCert.v`: `check_win`, with Packed's `hint` that lets
  B try every move.

The rules are `model.rs`, the same as everywhere else on the page.

**How B plays.** Rocq proves that every record passes `check_win`
(`Chunk*.v`), and that a passing record is a real win (`WinCert.cert_wins`).

- At each turn start `t` (Checker's `is_turn_start`), B takes the record of
  `key t` with the lowest rank among those that need at most B's actual life.
- B then follows an abstract copy of the game for the rest of the turn: the
  certificate's position `entry (key t) life`, stepped with the same moves.
  It stands for the real position in the sense of `Checker.R`: A's Walkers
  are clamped at 15 counters and B's Thopters are cut to 14.
- At each B decision, B plays the first legal move after which `check_win`
  still passes. That is the move the checker itself finds.
- A's moves need no choice: `check_win` passed for all of them. A's legal
  moves in the real game are the same as in the abstract one (WinCert's
  `moves_theirs`), and the engine checks this on every move.
- Ranks fall strictly from one turn start to the next, so the game ends.

The search uses B's actual life, since more life only helps. If a check
failed on the actual life, B would fall back to the record's own value,
which is exactly what Rocq checked. In all the testing below that never
happened.

The worker answers each request by replaying the game, so undo, reload and
the saved game need nothing special. The answer is either B's moves until A is
next to move, or one of two failures:

- **not covered:** the position is outside the certificate, and the page
  falls back to the heuristic search with a "Not certified" label. This
  happens only if the game didn't start from a covered position: B on less
  than 17 life, or A on anything but 20 (the "Variant" setting).
- **error:** the search failed where the certificate should cover the
  position. This is impossible unless something is wrong, so the page shows
  an error and the computer stops. It never falls back silently. The same
  applies if the game ever leaves the certificate through A's move or a
  certified B move.

Certified requests have no time limit, and every B decision goes through
them, even ones with a single filtered candidate. They take a few
milliseconds, at most a few thousand checker nodes. The page makes no move
until the table has loaded. The certified B never offers or accepts a draw,
so the repetition and turn-60 prompts and the Draw button are off.

### Verification

`cert-tool` (native) and the tests check the following:

- **Every record.** `cert-tool check-all TABLE` runs the port's `record_ok`
  on all 1,512,056 records, and all pass, as in Rocq. That takes 17 s on 4
  threads, with 505M checker nodes and at most 7,755 for one record.
  `cert-tool mutants` shows that the check is not vacuous: with one life
  less, or rank 0, most records fail.
- **The extracted Rocq model.** `test/cert-ocaml.sh STRIDE [GAMES]`
  compiles `test/cert_ocaml.ml` against `_build/default/solver/model.ml`
  (the extracted `check_win`, `key`, `moves`, `step`, …). It reads `Data.v`
  itself and implements Packed's `lookup`/`below` independently of
  `cert.rs`. For every STRIDE-th record it digests the whole search
  `check_win` makes, on both sides: every node's state, its legal moves in
  order, and every lookup. The digests must match, and the extracted
  `check_win` must accept every record. Given game records, it also compares
  every position and its legal moves along certified self-play games. A's
  moves in those games include real positions beyond the certificate's
  abstraction.
- **Self-play.** `cert-tool selfplay TABLE ADV GAMES SEED` plays certified B
  from the opening against A = `random`, `bias` (random, avoiding passes and
  pumps), `searchMS` (the heuristic search), `rank` and `val`. The last two
  are adversaries that run the checker's search with A maximising (and B
  following its certified moves) to pick the move that forces the worst
  next record for B, by rank or by value. On every A decision they check
  that every A move stays inside the certificate. Every game must be a B
  win with no failure, and on every move the abstract state must stand for
  the real one (`Checker.R`).

## The heuristic opponent

In the other set-ups, the opponent is a **strong bounded search, not optimal
play.** Those openings are unsolved for B's win (see `REDUCTION.md`), and the
solver's other tables are far too big to ship. The page says this in the
setup dialog and in About.

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

**What is proved** (shown in the About panel): when B goes first, B can
force a win; when A goes first, A can't force a win, and whether B can is
still open.

## Long games and draws

Against the heuristic search, Walkers grow forever and Elixir loops, so a game
need not end. The page then offers a draw in two cases:

- the same turn-start position has occurred three times;
- the game reaches turn 60. If you keep playing, it asks again 30 turns
  later.

The Draw button ends the game as a draw at any time. Against the certified B
there are no draw prompts and the Draw button is disabled: B wins in finitely
many turns.

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
