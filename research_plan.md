# Research Plan: From Guided Reconstruction to Credible Target-Independent Discovery

## 1) Objective and Positioning

### Current assessment (from review)
The project is judged as:
- **Highly original and technically serious** with a real, reproducible codebase.
- **Not yet evidentially strong enough** for the strongest physics-facing claim.
- Better described today as a **guided synthesis/reconstruction framework** than a blind derivation of physics.

### Plan objective
Over the next revision cycle, produce a publication package where:
1. The **main claim is exactly matched** to the strongest clean experimental evidence.
2. Discovery and verification pipelines are **strictly separated**.
3. The mechanized theorem kernel and experimental results are **version-aligned, auditable, and reviewer-proof**.

---

## 2) Claim Strategy and Paper Reframing

## 2.1 New claim boundary (immediate)
Adopt a claim hierarchy in all prose, abstract, and title:

- **Tier A (defensible now):** mechanized bounded typed search + efficiency scoring can reconstruct a physics-relevant kinematic hierarchy under explicit structural constraints.
- **Tier B (requires new evidence):** partial target-independence under ablations and negative controls.
- **Tier C (defer):** algorithmic origin of physics as a foundational conclusion.

### Deliverables
- Replace “algorithmic origin of the kinematic framework of physics” style wording with constrained alternatives.
- Add a **Claim Matrix** table in paper:
  - Claim
  - Evidence type
  - Current support status (Supported / Partial / Conjectural)

---

## 3) Experimental Architecture Split

## 3.1 Create two hard-separated lanes

### Lane 1: Discovery (blind)
Must run without:
- reference telescope injection,
- canonical-name priority,
- paper lookup tables/fallback,
- hidden step-indexed target hints.

### Lane 2: Acceptance/Audit
May use:
- reference telescope,
- canonical mapping,
- regression checks against canonical sequence,
- certificate replay and reproducibility checks.

### Implementation requirements
- Distinct executables/config profiles (`discover_blind`, `acceptance_audit`) with explicit, logged flags.
- Output ledger fields must include:
  - `mode`
  - `source` (ENUM / MCTS / REF / other)
  - `hints_enabled` boolean set
  - per-step selector policy

### Success criterion
No figure/table may present Lane 2 outcomes as autonomous discovery.

---

## 4) Selector-Theory Consistency Program

## 4.1 Align theorem, prose, and code
The review identifies a mismatch: prose suggests minimal overshoot while implementation appears to include additional priorities in some modes.

### Tasks
1. **Formal selector specification** document:
   - exact objective
   - tie-breakers
   - mode-specific deviations
2. **Code conformance audit**:
   - instrument selector decisions with reason codes (`overshoot`, `kappa_tiebreak`, `canonical_priority`, etc.).
3. **Paper sync patch**:
   - update theorem statements and algorithm pseudocode to exactly match implementation behavior.

### Decision gate
If canonical-priority or κ-first policies remain, these are explicitly presented as **heuristics**, not implied by theorem-level optimality claims.

---

## 5) Ablation Suite (Core Credibility Upgrade)

## 5.1 Mandatory ablations
Run full 15-step recovery experiments under controlled toggles:

1. Reference injection: ON/OFF
2. Canonical-name priority: ON/OFF
3. Prerequisite gating strictness levels
4. MCTS component: ON/OFF
5. Budget cap variants
6. Late-stage ν amplifiers: each individually removed

### Metrics per run
- Recovered prefix length (exact canonical match length)
- Step-wise source mix (% ENUM / % MCTS / % REF)
- ν, κ, ρ trajectories
- Divergence onset tick
- Stability across random seeds (when stochastic components active)

### Table requirements
- Publish a single “hard ablation table” in main paper.
- Move verbose run logs to appendix/repo artifact folder.

---

## 6) Negative Controls (Target-Independence Stress Test)

## 6.1 Control families
Construct near-canonical alternative trajectories and test how easily they can be made “optimal” under modest perturbations:

- ν weighting perturbations
- κ definition variants
- budget policy variations
- grammar neighborhood perturbations

### Evidence goal
Quantify whether canonical trajectory is:
- uniquely robust (strong support),
- one of few robust trajectories (moderate support),
- one of many easy-to-fit trajectories (weak support).

### Reporting
Add robustness section with:
- uniqueness score,
- sensitivity heatmap,
- rank stability under perturbation.

---

## 7) Version Drift Elimination Plan (Immediate Priority)

## 7.1 Single source of truth
Resolve `43/60/105` vs `46/62/103` and any similar discrepancies across:
- TeX tables,
- bundled baselines,
- source constants,
- acceptance tests,
- docs/readmes.

### Steps
1. Declare authoritative sequence file (`data/canonical_sequence.<format>`).
2. Refactor pipelines so paper tables and baselines are generated from this file.
3. Add CI check that fails if generated tables or artifacts diverge.
4. Stamp every run with git SHA + sequence version ID.

### Success criterion
A reviewer can identify exactly one canonical ν-sequence and trace every figure/table back to it.

---

## 8) Documentation and Formalization Synchronization

## 8.1 Mechanization status transparency
Address mismatch between high-level mechanization claims and “TODO/stub” labels.

### Deliverables
- Add **Mechanization Coverage Matrix**:
  - component
  - status (formalized / executable only / stub)
  - evidence pointer (file/module/test)
- Update all READMEs to consistent phase status.
- Add explicit boundary statement:
  - what is proven in proof assistant,
  - what is validated experimentally in Haskell/engine,
  - what remains conjectural.

---

## 9) Lead Result Reordering

## 9.1 Promote mathematical kernel
Reorder manuscript structure:
1. Coherence-window / recurrence / growth theorem package (lead)
2. Mechanized search framework
3. Discovery and ablation evidence
4. Physics interpretation as discussion/conjecture layer

### Rationale
This foregrounds the strongest, most defensible contribution and reduces overclaim risk.

---

## 10) Reproducibility and Auditability Enhancements

## 10.1 Artifact standards
Every reported run must include:
- executable name + mode
- full config snapshot
- random seed(s)
- git SHA
- canonical sequence version
- machine-readable ledger CSV/JSON
- replay command

## 10.2 Reviewer quickstart
Provide a 3-command replication path:
1. regenerate baseline tables
2. run blind discovery benchmark
3. run acceptance/audit checks

Target total runtime should be documented with a “fast” and “full” profile.

---

## 11) Milestone Plan and Timeline

## Phase 0 (Week 1): Stabilize narrative and data truth
- Freeze claim hierarchy and provisional title.
- Resolve ν-sequence version drift.
- Publish canonical sequence artifact and generation scripts.

**Exit criteria:** no conflicting numbers anywhere in repo/paper.

## Phase 1 (Weeks 2–3): Pipeline separation and selector audit
- Implement hard split of discovery vs acceptance lanes.
- Add selector reason-code logging and policy docs.
- Update prose/theorems to match executable behavior.

**Exit criteria:** discovery outputs contain no REF/canonical leakage when blind mode is active.

## Phase 2 (Weeks 4–6): Ablations + negative controls
- Run mandatory ablation matrix.
- Run perturbation-based negative controls.
- Produce robust summary tables and plots.

**Exit criteria:** one main-paper table each for ablations and robustness.

## Phase 3 (Weeks 7–8): Manuscript restructuring and package release
- Reorder paper around theorem/mechanization core.
- Narrow title/claims.
- Release synchronized artifact bundle with replication guide.

**Exit criteria:** major-revision-ready submission package.

---

## 12) Risk Register and Mitigations

1. **Risk:** Blind mode fails to recover enough of sequence.
   - **Mitigation:** state this honestly; position guided lane as engineered synthesis; avoid autonomy claims.

2. **Risk:** Negative controls show many alternative trajectories fit.
   - **Mitigation:** shift contribution toward search-framework methodology and mechanized efficiency principles, not physics-origin conclusion.

3. **Risk:** Formalization coverage remains partial.
   - **Mitigation:** tighten language to “partially formalized + executable mechanization,” with explicit boundaries.

4. **Risk:** Runtime costs for ablation matrix too high.
   - **Mitigation:** staged benchmarking (smoke vs full), deterministic caching, and published compute budget.

---

## 13) Definition of Done for Next Submission
A revised paper is “ready” when all are true:
- Main title and abstract make only claims directly supported by blind or clearly-labeled guided evidence.
- Discovery and audit lanes are technically and rhetorically disentangled.
- A full ablation table and negative-control analysis are included.
- All ν values and milestones are version-consistent across code, artifacts, tests, and manuscript.
- Mechanization coverage is explicitly documented and synchronized.
- Reproduction from clean checkout succeeds with documented commands.

---

## 14) Suggested Revised Title Candidates
1. **Mechanized Efficiency-Guided Reconstruction of a Physics-Relevant Kinematic Hierarchy under Bounded Typed Search**
2. **A Reproducible Search-and-Selection Framework for Kinematic Hierarchies: Mechanization, Ablations, and Limits**
3. **From Coherence-Constrained Growth to Kinematic Sequence Reconstruction: A Mechanized Study**

---

## 15) One-Paragraph Positioning for Cover Letter / Rebuttal
This revision narrows the central claim from a broad origin thesis to a mechanized, reproducible reconstruction result under explicit bounded-search assumptions. We separate blind discovery from acceptance audit pipelines, publish full ablations and negative controls, and synchronize all artifacts around a single canonical ν-sequence to eliminate version drift. The paper now leads with the formal growth/coherence kernel and treats physics interpretation as a conjectural layer, improving evidentiary alignment and scientific defensibility.
