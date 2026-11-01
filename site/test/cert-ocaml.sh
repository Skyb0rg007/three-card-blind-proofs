#!/usr/bin/env bash
# Compare the site's certified B with the Rocq model extracted to OCaml.
#
#   site/test/cert-ocaml.sh STRIDE [GAMES_FILE]
#
# Needs the extracted model, built from the repository root with
#   nix-shell --run 'dune build --root . ./solver/main.exe'
# and runs inside that nix-shell (for ocamlfind/ocamlopt), with
# site/target/release/cert-tool built (cargo build --release --bin cert-tool).
#
# 1. For every STRIDE-th record of proofs/bfirst/Data.v, the search
#    check_win makes (every node, state, legal move list and lookup) is
#    digested on both sides and must match; the extracted check_win must
#    accept every record, as the Rust port must.
# 2. If GAMES_FILE is given (game records, e.g. from
#    `TCB_DUMP=... cert-tool selfplay`), every position of every game and
#    its legal moves must match.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$here/../.."
stride="${1:-100}"
games="${2:-}"
model="$root/_build/default/solver/model.ml"
tool="$here/../target/release/cert-tool"
[ -f "$model" ] || { echo "missing $model: run dune build --root . ./solver/main.exe" >&2; exit 1; }
[ -x "$tool" ] || { echo "missing $tool" >&2; exit 1; }
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cp "$model" "$root/_build/default/solver/model.mli" "$tmp/"
cp "$here/cert_ocaml.ml" "$tmp/"
(cd "$tmp" && ocamlfind ocamlopt -O2 -w -a model.mli model.ml cert_ocaml.ml -o cert_ocaml 2>/dev/null \
  || ocamlfind ocamlopt -w -a model.mli model.ml cert_ocaml.ml -o cert_ocaml)
xz -dc "$root/proofs/bfirst/Data.v.xz" > "$tmp/Data.v"
n=$(( ($(grep -o ';' <<<"$(grep '^Definition RV' "$tmp/Data.v")" | wc -l) + 1 + stride - 1) / stride ))
echo "records: every ${stride}th, $n of them"
jobs=3
per=$(( (n + jobs - 1) / jobs ))
for k in $(seq 0 $((jobs - 1))); do
  start=$(( k * per * stride ))
  nice "$tmp/cert_ocaml" trace "$tmp/Data.v" "$start" "$stride" "$per" 0 > "$tmp/ocaml.$k" &
  nice "$tool" trace "$tmp/Data.v" "$start" "$stride" "$per" 0 > "$tmp/rust.$k" 2>/dev/null &
done
wait
cat "$tmp"/ocaml.* > "$tmp/ocaml"
cat "$tmp"/rust.* > "$tmp/rust"
lines=$(wc -l < "$tmp/rust")
nodes=$(awk '{s += $4} END {print s}' "$tmp/rust")
if grep -q MISMATCH "$tmp/ocaml"; then echo "FAIL: OCaml traversal disagrees with extracted check_win"; grep MISMATCH "$tmp/ocaml" | head; exit 1; fi
if grep -qv ' true ' "$tmp/ocaml"; then echo "FAIL: extracted check_win rejects a record"; grep -v ' true ' "$tmp/ocaml" | head; exit 1; fi
if ! cmp -s "$tmp/ocaml" "$tmp/rust"; then
  echo "FAIL: traces differ"; diff "$tmp/ocaml" "$tmp/rust" | head; exit 1
fi
echo "records: $lines identical searches ($nodes trace lines), all accepted by the extracted check_win"
if [ -n "$games" ]; then
  # streamed and digested: the replays run to gigabytes
  o=$(nice "$tmp/cert_ocaml" replay < "$games" | md5sum)
  r=$(nice "$tool" replay < "$games" | md5sum)
  if [ "$o" != "$r" ]; then echo "FAIL: game replays differ"; exit 1; fi
  echo "games: $(grep -c . "$games") games, $(awk '{n += NF - 2} END {print n}' "$games") positions with identical legal moves"
fi
