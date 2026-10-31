#!/usr/bin/env bash
# Build the static site into site/dist/.
# Needs cargo and rustc with the wasm32-unknown-unknown target:
#  - nix: site/shell.nix (nixpkgs' rustc links wasm with lld, which it provides);
#  - rustup / CI: `rustup target add wasm32-unknown-unknown` (links with the
#    bundled rust-lld, nothing else needed).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$here/target}"
cargo build --locked --release -j"${JOBS:-4}" --lib --target wasm32-unknown-unknown \
  --manifest-path "$here/engine/Cargo.toml"
rm -rf "$here/dist"
mkdir -p "$here/dist"
cp "$here"/web/index.html "$here"/web/style.css "$here"/web/*.js "$here/dist/"
cp "$CARGO_TARGET_DIR/wasm32-unknown-unknown/release/tcb_engine.wasm" "$here/dist/engine.wasm"
# Plain static files: tell GitHub Pages not to run Jekyll over them.
touch "$here/dist/.nojekyll"
echo "built $here/dist ($(du -sh "$here/dist" | cut -f1))"
