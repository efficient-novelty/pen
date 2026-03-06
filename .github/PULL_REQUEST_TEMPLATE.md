## Summary

<!-- Describe what changed and why. -->

## Lane 1 Blind Discovery Release Gate (required for Lane 1 publication claims)

If this PR makes or updates a Lane 1 blind-discovery claim, all items below are required:

- [ ] `make test-blindness` passes.
- [ ] Baseline artifacts exist in `artifacts/lane1/baseline/`:
  - [ ] `ledger.jsonl`
  - [ ] `manifest.json`
  - [ ] `summary.json`
  - [ ] `evidence_table.md`
- [ ] `./scripts/replay_lane1_blind.sh` passes.
- [ ] `artifacts/lane1/baseline/summary.json` has `"lane1_ref_zero_pass": true`.
- [ ] Lane 1 evidence table is linked in manuscript/docs.

## Testing

<!-- List commands run and outcomes. -->
