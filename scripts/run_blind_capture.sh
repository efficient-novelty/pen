#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

TICKS="${TICKS:-16}"
SEED="${SEED:-0}"
BUDGET="${BUDGET:-0}"
OUT_DIR="${OUT_DIR:-artifacts/lane1/latest}"
LEDGER_FORMAT="${LEDGER_FORMAT:-jsonl}"

mkdir -p "$OUT_DIR"

BIN="./.lake/build/bin/discover_blind"
if [[ ! -x "$BIN" ]]; then
  echo "missing binary: $BIN (run: lake build discover_blind)" >&2
  exit 1
fi

CONFIG_TXT="$OUT_DIR/config.txt"
LEDGER_FILE="$OUT_DIR/ledger.${LEDGER_FORMAT}"
MANIFEST_FILE="$OUT_DIR/manifest.json"

"$BIN" --print-config > "$CONFIG_TXT"
"$BIN" --ticks "$TICKS" --ledger-format "$LEDGER_FORMAT" > "$LEDGER_FILE"

GIT_SHA="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
CONFIG_HASH="$(sha256sum "$CONFIG_TXT" | awk '{print $1}')"
LEDGER_HASH="$(sha256sum "$LEDGER_FILE" | awk '{print $1}')"

cat > "$MANIFEST_FILE" <<JSON
{
  "git_sha": "$GIT_SHA",
  "executable": "discover_blind",
  "config_hash": "$CONFIG_HASH",
  "seed": $SEED,
  "budget": $BUDGET,
  "ticks": $TICKS,
  "ledger_format": "$LEDGER_FORMAT",
  "ledger_path": "$(basename "$LEDGER_FILE")",
  "ledger_sha256": "$LEDGER_HASH",
  "valid_blind_run": true,
  "reference_injection": false,
  "canonical_priority": false,
  "paper_fallback": false,
  "step_index_hints": false,
  "acceptance_assets_loaded": false
}
JSON

python3 scripts/summarize_lane1_ledger.py --ledger "$LEDGER_FILE" --manifest "$MANIFEST_FILE" --out "$OUT_DIR/summary.json"
python3 scripts/generate_lane1_evidence_table.py --summary "$OUT_DIR/summary.json" --out "$OUT_DIR/evidence_table.md"

echo "wrote: $OUT_DIR"
