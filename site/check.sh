#!/usr/bin/env bash
# Check that the WASM engine reproduces `rsolver walk` byte for byte, then
# run the targeted trace check (multi-blocks, damage orders) against the
# native build of the same library.
#   site/check.sh [STEPS [SEED...]]
# Uses rsolver/target/release/rsolver if it exists; otherwise builds rsolver
# into site/target/rsolver (leaving rsolver/target alone).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
steps="${1:-5000}"
shift || true
seeds=("$@")
[ ${#seeds[@]} -gt 0 ] || seeds=(1 2 7 42 1234 987654321 12345678901)
[ -f "$here/dist/engine.wasm" ] || "$here/build.sh"
rsolver="$here/../rsolver/target/release/rsolver"
if [ ! -x "$rsolver" ]; then
  CARGO_TARGET_DIR="$here/target/rsolver" cargo build --release -j"${JOBS:-4}" \
    --manifest-path "$here/../rsolver/Cargo.toml"
  rsolver="$here/target/rsolver/release/rsolver"
fi
node "$here/test/walk-check.mjs" "$here/dist/engine.wasm" "$rsolver" "$steps" "${seeds[@]}"
CARGO_TARGET_DIR="$here/target" cargo build --release -j"${JOBS:-4}" --bin engine-bench \
  --manifest-path "$here/engine/Cargo.toml"
node "$here/test/trace-check.mjs" "$here/dist/engine.wasm" "$here/target/release/engine-bench" 60
