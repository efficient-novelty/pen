# Lane 1 Action Plan: One-Shot Path to Fully Blind Discovery

**Goal:** Deliver a discovery pipeline that is genuinely blind (no reference telescope injection, no canonical-name priority, no paper lookup/fallback tables, no hidden step-index hints) and can be defended as such in paper and artifact form.

## One-shot steps

1. **Freeze and codify the Lane 1 blindness contract.**  
   Create `docs/blind_contract.md` with explicit prohibitions, allowed inputs, and required runtime assertions for blind mode.
   - **Done when:** contract is merged and linked from README + discovery docs.

2. **Introduce a dedicated blind executable/profile (`discover_blind`) with hard defaults.**  
   Add a separate entrypoint/config that cannot inherit acceptance/audit settings implicitly.
   - **Done when:** `discover_blind --print-config` shows all hint/reference knobs OFF by default.

3. **Implement hard fail-closed guards for forbidden features.**  
   In `discover_blind`, abort at startup if any of the following are enabled: REF injection, canonical-name ranking, paper-table fallback, step-indexed target hints.
   - **Done when:** each forbidden flag triggers a nonzero exit with a clear error message.

4. **Physically separate data dependencies for discovery vs acceptance.**  
   Move reference telescopes and canonical lookup assets into an acceptance-only path/module so blind builds cannot import them accidentally.
   - **Done when:** dependency graph for `discover_blind` has no import/path edge to acceptance reference assets.

5. **Add selector decision reason-codes to blind ledger output.**  
   Emit per-step machine-readable fields (`mode`, `source`, `selector_policy`, `hints_enabled`, `forbidden_checks_passed`).
   - **Done when:** every blind run produces CSV/JSON ledger rows with these fields populated.

6. **Add an automated "blindness compliance" test suite.**  
   Add tests that intentionally try to enable forbidden knobs in blind mode and assert startup failure; include a positive smoke test that runs with all checks passing.
   - **Done when:** CI has a dedicated target (e.g., `test:blindness`) and it is required for merge.

7. **Create a provenance manifest for each blind run.**  
   Auto-write a manifest containing git SHA, executable name, config hash, seed, and explicit boolean attestations for each blind constraint.
   - **Done when:** manifest is generated on each run and referenced by ledger/artifacts.
   - **Status:** ✅ Implemented via `scripts/run_blind_capture.sh` (`manifest.json`, `summary.json`).

8. **Run a baseline blind benchmark and publish raw artifacts.**  
   Execute `discover_blind` under fixed seeds/budgets; publish full ledgers, manifest, and summary table without post-hoc editing.
   - **Done when:** artifact bundle is reproducible from clean checkout with documented commands.
   - **Status:** ✅ Implemented via `scripts/run_lane1_baseline.sh` + `artifacts/lane1/baseline/reproduce.sh` generation flow.

9. **Add a paper-ready Lane 1 evidence table with source transparency.**  
   Build a compact table showing recovered prefix length, source mix (ENUM/MCTS/REF), divergence onset, and note that REF must be 0% in Lane 1.
   - **Done when:** table is auto-generated from blind ledgers and linked in manuscript.
   - **Status:** ✅ Implemented via `scripts/generate_lane1_evidence_table.py` -> `evidence_table.md`.

10. **Add an independent replay script for reviewer verification.**  
   Provide a one-command replay that re-runs blind discovery and checks hash/shape consistency of ledger + manifest outputs.
   - **Done when:** replay passes on CI and in a clean local/container environment.
   - **Status:** ✅ Implemented via `scripts/replay_lane1_blind.sh` (`make lane1-replay`).

11. **Install release gating: no Lane 1 claim without compliance artifacts.**  
   Add a pre-release checklist requiring blind compliance tests, baseline artifacts, replay success, and zero REF usage in Lane 1 outputs.
   - **Done when:** checklist is part of release PR template and blocks publication claims when unmet.
   - **Status:** ✅ Implemented via `.github/PULL_REQUEST_TEMPLATE.md`, `scripts/check_lane1_release_gate.sh`, and CI workflow `lane1-release-gate.yml` (gated when `docs/LANE1_CLAIM.md` exists).

## Definition of success for Lane 1

Lane 1 is complete only if a skeptical reviewer can verify, from code and artifacts alone, that the reported discovery run had no reference leakage or target-aware ranking aids and that all evidence was produced by the blind executable under fail-closed constraints.
