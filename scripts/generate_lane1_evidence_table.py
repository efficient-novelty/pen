#!/usr/bin/env python3
import argparse, json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    s = json.loads(Path(args.summary).read_text())
    mix = s.get('source_mix_pct', {})

    rows = [
        ("Recovered prefix length", str(s.get('recovered_prefix_length'))),
        ("Divergence onset tick (REF)", str(s.get('divergence_onset_tick'))),
        ("Source mix ENUM (%)", f"{mix.get('ENUM', 0.0):.2f}"),
        ("Source mix MCTS (%)", f"{mix.get('MCTS', 0.0):.2f}"),
        ("Source mix REF (%)", f"{mix.get('REF', 0.0):.2f}"),
        ("REF must be 0% (Lane 1)", "PASS" if s.get('lane1_ref_zero_pass') else "FAIL"),
        ("Selector policy", str(s.get('selector_policy'))),
    ]

    md = [
        "# Lane 1 Evidence Table (Auto-generated)",
        "",
        "| Metric | Value |",
        "|---|---|",
    ]
    md += [f"| {k} | {v} |" for k, v in rows]
    md += ["", f"Generated from `{s.get('ledger_path')}` and `{s.get('manifest_path')}`."]

    Path(args.out).write_text("\n".join(md) + "\n")


if __name__ == '__main__':
    main()
