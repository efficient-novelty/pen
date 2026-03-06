#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lake build discover_blind >/dev/null

# Positive smoke: defaults should print all forbidden flags OFF.
CONFIG_OUTPUT="$(./.lake/build/bin/discover_blind --print-config)"
echo "$CONFIG_OUTPUT" | rg -q '^reference_injection=false$'
echo "$CONFIG_OUTPUT" | rg -q '^canonical_name_ranking=false$'
echo "$CONFIG_OUTPUT" | rg -q '^paper_table_fallback=false$'
echo "$CONFIG_OUTPUT" | rg -q '^step_indexed_target_hints=false$'

# Positive smoke: machine-readable ledger has required fields in JSONL mode.
LEDGER_JSON="$(./.lake/build/bin/discover_blind --ticks 1 --ledger-format jsonl)"
echo "$LEDGER_JSON" | rg -q '"mode":"discover_blind"'
echo "$LEDGER_JSON" | rg -q '"source":"'
echo "$LEDGER_JSON" | rg -q '"selector_policy":"'
echo "$LEDGER_JSON" | rg -q '"hints_enabled":false'
echo "$LEDGER_JSON" | rg -q '"forbidden_checks_passed":true'

# Positive smoke: machine-readable ledger has required header in CSV mode.
LEDGER_CSV="$(./.lake/build/bin/discover_blind --ticks 1 --ledger-format csv)"
echo "$LEDGER_CSV" | head -n1 | rg -q '^tick,mode,source,selector_policy,hints_enabled,forbidden_checks_passed$'

# Forbidden flags must fail-closed with nonzero exit.
set +e
./.lake/build/bin/discover_blind --enable-ref-injection >/tmp/blind_ref.err 2>&1
RC_REF=$?
./.lake/build/bin/discover_blind --enable-canonical-ranking >/tmp/blind_canon.err 2>&1
RC_CANON=$?
./.lake/build/bin/discover_blind --enable-paper-fallback >/tmp/blind_paper.err 2>&1
RC_PAPER=$?
./.lake/build/bin/discover_blind --enable-step-index-hints >/tmp/blind_hints.err 2>&1
RC_HINTS=$?
set -e

[[ $RC_REF -ne 0 ]] && rg -q 'FAIL-CLOSED' /tmp/blind_ref.err
[[ $RC_CANON -ne 0 ]] && rg -q 'FAIL-CLOSED' /tmp/blind_canon.err
[[ $RC_PAPER -ne 0 ]] && rg -q 'FAIL-CLOSED' /tmp/blind_paper.err
[[ $RC_HINTS -ne 0 ]] && rg -q 'FAIL-CLOSED' /tmp/blind_hints.err

# Dependency guard: discover_blind must not import acceptance assets.
if rg -n 'import PEN\.Acceptance\.ReferenceAssets' DiscoverBlind.lean >/dev/null; then
  echo "discover_blind imports acceptance assets; this violates lane separation" >&2
  exit 1
fi

echo "blindness compliance checks passed"
