#!/usr/bin/env python3
import argparse, csv, json
from pathlib import Path


def load_rows(path: Path):
    if path.suffix == '.jsonl':
        rows = []
        for line in path.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
        return rows
    if path.suffix == '.csv':
        with path.open() as f:
            return list(csv.DictReader(f))
    raise SystemExit(f"unsupported ledger format: {path}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--ledger', required=True)
    ap.add_argument('--manifest', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    ledger_path = Path(args.ledger)
    manifest = json.loads(Path(args.manifest).read_text())
    rows = load_rows(ledger_path)

    total = len(rows)
    source_counts = {}
    for r in rows:
        s = r.get('source', 'UNKNOWN')
        source_counts[s] = source_counts.get(s, 0) + 1

    # Proxy metric: prefix of non-idle selections from tick 1.
    recovered_prefix_length = 0
    for r in rows:
        if r.get('source') == 'NONE':
            break
        recovered_prefix_length += 1

    divergence_onset_tick = None
    for r in rows:
        if r.get('source') == 'REF':
            divergence_onset_tick = int(r.get('tick', 0))
            break

    source_mix_pct = {
        k: (v / total * 100.0 if total else 0.0)
        for k, v in sorted(source_counts.items())
    }

    summary = {
        'manifest_path': str(Path(args.manifest)),
        'ledger_path': str(ledger_path),
        'total_steps': total,
        'recovered_prefix_length': recovered_prefix_length,
        'divergence_onset_tick': divergence_onset_tick,
        'source_counts': source_counts,
        'source_mix_pct': source_mix_pct,
        'lane1_ref_zero_pass': source_counts.get('REF', 0) == 0,
        'selector_policy': rows[0].get('selector_policy') if rows else None,
        'mode': rows[0].get('mode') if rows else None,
        'hints_enabled_all_false': all(str(r.get('hints_enabled')).lower() == 'false' for r in rows),
        'forbidden_checks_all_true': all(str(r.get('forbidden_checks_passed')).lower() == 'true' for r in rows),
        'manifest': manifest,
    }

    Path(args.out).write_text(json.dumps(summary, indent=2) + '\n')


if __name__ == '__main__':
    main()
