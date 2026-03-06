#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

BASE_DIR="${BASE_DIR:-artifacts/lane1/baseline}"
TMP_DIR="artifacts/lane1/replay_tmp"

if [[ ! -f "$BASE_DIR/manifest.json" || ! -f "$BASE_DIR/ledger.jsonl" ]]; then
  echo "missing baseline artifacts in $BASE_DIR; run scripts/run_lane1_baseline.sh first" >&2
  exit 1
fi

rm -rf "$TMP_DIR"
mkdir -p "$TMP_DIR"

TICKS="$(python3 - <<'PY'
import json
print(json.load(open('artifacts/lane1/baseline/manifest.json'))['ticks'])
PY
)"
SEED="$(python3 - <<'PY'
import json
print(json.load(open('artifacts/lane1/baseline/manifest.json'))['seed'])
PY
)"
BUDGET="$(python3 - <<'PY'
import json
print(json.load(open('artifacts/lane1/baseline/manifest.json'))['budget'])
PY
)"

TICKS="$TICKS" SEED="$SEED" BUDGET="$BUDGET" OUT_DIR="$TMP_DIR" LEDGER_FORMAT="jsonl" ./scripts/run_blind_capture.sh

python3 - <<'PY'
import json, hashlib, sys
from pathlib import Path
b = Path('artifacts/lane1/baseline')
r = Path('artifacts/lane1/replay_tmp')

def h(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

bl = h(b/'ledger.jsonl')
rl = h(r/'ledger.jsonl')
if bl != rl:
    print('ledger hash mismatch', file=sys.stderr)
    sys.exit(1)

bs = json.loads((b/'summary.json').read_text())
rs = json.loads((r/'summary.json').read_text())
for key in ['total_steps','recovered_prefix_length','divergence_onset_tick','lane1_ref_zero_pass']:
    if bs.get(key) != rs.get(key):
        print(f'summary mismatch for {key}: {bs.get(key)} != {rs.get(key)}', file=sys.stderr)
        sys.exit(1)
print('replay verification passed')
PY
