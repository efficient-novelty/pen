#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

CLAIM_FILE="docs/LANE1_CLAIM.md"
if [[ ! -f "$CLAIM_FILE" ]]; then
  echo "No $CLAIM_FILE present; skipping Lane 1 publication gate."
  exit 0
fi

./scripts/test_blindness.sh

for f in artifacts/lane1/baseline/ledger.jsonl artifacts/lane1/baseline/manifest.json artifacts/lane1/baseline/summary.json artifacts/lane1/baseline/evidence_table.md; do
  [[ -f "$f" ]] || { echo "missing required artifact: $f" >&2; exit 1; }
done

./scripts/replay_lane1_blind.sh

python3 - <<'PY'
import json, sys
s = json.load(open('artifacts/lane1/baseline/summary.json'))
if not s.get('lane1_ref_zero_pass', False):
    print('lane1_ref_zero_pass is not true', file=sys.stderr)
    sys.exit(1)
print('lane1_ref_zero_pass check passed')
PY
