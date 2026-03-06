#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

OUT_DIR="${OUT_DIR:-artifacts/lane1/baseline}"
TICKS="${TICKS:-16}"
SEED="${SEED:-0}"
BUDGET="${BUDGET:-0}"

mkdir -p "$OUT_DIR"

TICKS="$TICKS" SEED="$SEED" BUDGET="$BUDGET" OUT_DIR="$OUT_DIR" LEDGER_FORMAT="jsonl" \
  ./scripts/run_blind_capture.sh

cat > "$OUT_DIR/reproduce.sh" <<REPRO
#!/usr/bin/env bash
set -euo pipefail
cd "\$(dirname "$0")/../.."
TICKS=$TICKS SEED=$SEED BUDGET=$BUDGET OUT_DIR=artifacts/lane1/baseline LEDGER_FORMAT=jsonl ./scripts/run_blind_capture.sh
REPRO
chmod +x "$OUT_DIR/reproduce.sh"

echo "baseline artifacts available in $OUT_DIR"
