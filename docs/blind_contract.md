# Lane 1 Blindness Contract (`discover_blind`)

## Purpose

This contract defines what **must** be true for Lane 1 runs to be considered **fully blind discovery**. Any violation invalidates a run for Lane 1 claims.

---

## 1) Prohibitions (MUST be disabled)

The `discover_blind` mode MUST NOT use, directly or indirectly:

1. **Reference telescope injection** (including step-indexed reference telescopes).
2. **Canonical-name priority** in ranking, tie-breaking, or capability unlocking.
3. **Paper lookup/fallback tables** (canonical sequences, milestone maps, or hand-authored target lists used during selection).
4. **Hidden target hints** keyed by step index (`τ`) or milestone position.
5. **Acceptance/audit assets** imported at runtime for discovery decisions.

If any prohibited feature is enabled or reachable, `discover_blind` MUST fail closed before the first selection step.

---

## 2) Allowed inputs for blind runs

`discover_blind` MAY use only the following categories of inputs:

1. **Declared finite discovery action alphabet** used for admissibility and novelty computations.
2. **Current runtime state** (context/state, horizon policy, selector policy) exactly as documented for discovery mode.
3. **General search controls** that do not carry target knowledge (`budget`, `seed`, `timeout`, deterministic/reproducibility toggles).
4. **Structural scoring features** that are target-agnostic (i.e., they cannot encode canonical milestone identity or step-index guidance).

### Explicit allowlist examples

- Allowed: exploration budget caps, RNG seed, timeout, frontier width limits, deterministic mode flags.
- Allowed: structural complexity/effort measures derived from currently reachable states.
- Not allowed under this section: anything keyed to canonical names, milestone indices, paper tables, or acceptance reference assets (prohibited in Section 1).

### Metadata obligation for allowed controls

“Allowed” does **not** mean “unlogged.” Every active control in this section MUST be emitted in run metadata/manifest, including:

- `action_alphabet_id` (or equivalent hash/version identifier)
- `selector_policy`
- `horizon_policy`
- `budget`
- `seed`
- `timeout`
- `deterministic_mode`
- `config_hash`

A Lane 1 run is non-compliant if any active allowed control is omitted from metadata.

---

## 3) Required runtime assertions (fail-closed)

At startup, `discover_blind` MUST assert all of the following:

- `reference_injection == false`
- `canonical_priority == false`
- `paper_fallback == false`
- `step_index_hints == false`
- `acceptance_assets_loaded == false`

If any assertion fails:

- Exit with nonzero status.
- Print machine-readable error code + human-readable reason.
- Emit a partial manifest marked `valid_blind_run=false`.

---

## 4) Required ledger and manifest fields

Every blind run MUST emit machine-readable artifacts containing at minimum:

### Per-step ledger fields
- `mode` (must be `discover_blind`)
- `source` (ENUM/MCTS/REF/other)
- `selector_policy`
- `hints_enabled` (must be `false`)
- `forbidden_checks_passed` (must be `true`)

### Run-level manifest fields
- `git_sha`
- `executable`
- `config_hash`
- `seed`
- `valid_blind_run`
- `reference_injection`
- `canonical_priority`
- `paper_fallback`
- `step_index_hints`
- `acceptance_assets_loaded`

Lane 1 claims are valid only when all required fields are present and consistent.

---

## 5) Lane separation requirements

To prevent accidental leakage:

- Acceptance/audit assets must live in acceptance-only paths/modules.
- `discover_blind` dependency graph must have no import edge to those assets.
- CI must include a blindness-compliance target that verifies these constraints.

---

## 6) Compliance gates for publication claims

A result may be labeled “Lane 1 blind discovery” only if all are true:

1. Startup assertions passed.
2. Manifest states `valid_blind_run=true`.
3. Ledger shows `mode=discover_blind` for all steps.
4. Ledger shows `hints_enabled=false` and `forbidden_checks_passed=true` for all steps.
5. `source` contains **no REF-derived selections**.
6. Run is reproducible with documented replay command from clean checkout.

---

## 7) Non-compliance handling

Any non-compliant run must be labeled as:

- `acceptance/audit`, or
- `guided reconstruction`,

and MUST NOT be presented as autonomous blind discovery.
