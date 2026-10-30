#!/usr/bin/env bash
# Download the Comprehensive Rules versions cited in RULES.md and verify them.
# Usage: scripts/fetch-cr.sh [output-dir]   (default: cr/)
set -euo pipefail

out="${1:-cr}"
mkdir -p "$out"

fetch() {
  local name="$1" sha="$2"
  curl -fsSL -o "$out/$name" "https://media.wizards.com/2024/downloads/MagicCompRules%20${name#MagicCompRules }"
  echo "$sha  $out/$name" | sha256sum -c -
}

# Pinned version: effective July 30, 2024 (pre-Foundations, has damage assignment order).
fetch "MagicCompRules 20240802.txt" 072395073f9b79f840c36f458b0d35997787b741f2357cfe3dd8ed9f74c7884d
# Comparison version: effective November 8, 2024 (Foundations, no damage assignment order).
fetch "MagicCompRules 20241108.txt" c5bf04bff59654d843d6897b9ee83c736af69b126a0fa96ad3f5efdf12b06096
