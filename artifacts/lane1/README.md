# Lane 1 Blind Artifacts

Generate baseline blind artifacts with:

```bash
./scripts/run_lane1_baseline.sh
```

This produces under `artifacts/lane1/baseline/`:
- `ledger.jsonl`
- `manifest.json`
- `summary.json`
- `evidence_table.md`
- `reproduce.sh`

Replay/verify determinism with:

```bash
./scripts/replay_lane1_blind.sh
```
