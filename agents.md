## 0) Scope (what to build / not build)

**Goal.** Mechanize the PEN framework in Lean 4 to **discover and select** bundles of atomic declarations (“candidates X”) that maximize **efficiency**
[
\rho(X)=\nu(X)/\kappa(X)
]
under the axioms, producing the **Genesis Sequence** with Fibonacci-timed realizations, the efficiency growth profile, and the specific table of 16 milestones shown in the paper.

**Out of scope.** Proving semantic meta-theorems inside Lean (e.g., Unbounded Growth theorem) is not required—only the executable selection/search that reproduces the sequence and logs auditable certificates.

---

## 1) Foundations and vocabulary mapping

Paper → Code mapping (use consistently in comments and function names):

| Paper term                                                           | Meaning                                                          | Lean code locus                                                                       |
| -------------------------------------------------------------------- | ---------------------------------------------------------------- | ------------------------------------------------------------------------------------- |
| **State** (\mathcal R(\tau))                                         | Cumulative context of realized declarations                      | `PEN.CAD.Context` (lists of universes, type formers, ctors, elims, comp rules, terms) |
| **Atomic declaration**                                               | One irreducible add step                                         | `PEN.CAD.AtomicDecl`                                                                  |
| **Cumulative growth (Axiom 1)**                                      | Context only extends                                             | `step`, `applyAll?` are monotone                                                      |
| **Effort kernel** (K_{\mathcal B}(Y))                                | Minimal atomic steps to realize Y from base                      | `PEN.CAD.kappaMin?` (IDDFS over finite action alphabet)                               |
| **Sealing / Interface basis**                                        | Coherence obligations with last two layers                       | `PEN.Novelty.Novelty.interfaceBasis` + `interactionProfile` (size contributes to κ)   |
| **Horizon** (H)                                                      | Effort budget policy                                             | `EngineState.H`; updates in `tick`/`tickDiscover`                                     |
| **Frontier** (\mathcal S(\mathcal B,H))                              | Post‐reachable targets within budget                             | `Novelty.frontierAllScoped` / `Scope.frontier`                                        |
| **Novelty** (\nu)                                                    | Count of targets whose pre-cost > post-cost (with caps & keying) | `Scope.contrib01` (binary) + reductions and caps; aggregated in `NoveltyReport`       |
| **Efficiency** (\rho)                                                | (\nu/\kappa)                                                     | `NoveltyReport.rho`                                                                   |
| **Selection bar** (\mathrm{Bar}(\tau)=\Phi(\tau)\cdot\Omega(\tau-1)) | Acceptance threshold                                             | `PEN.Select.Bar.barGlobal`                                                            |
| **Two-layer integration optimality**                                 | Only last two layers matter                                      | `EngineState.layers` carries last frontier schemas; `interfaceBasis` uses last two    |
| **Genesis tick** (\tau)                                              | External step counter                                            | `EngineState.τ`                                                                       |

**Cubical Type Theory (CTT) stance.** We emulate CTT’s 2D coherence by **counting** sealing obligations (size of interaction profile with the last two layers). We do not implement Kan fillers; we *charge* for them via `J(X,B)` size.

---

## 2) Axioms and operationalization

**Axiom 1 — Cumulative growth.**
Context is append-only. Enforced by `isValidInContext` and idempotent inserts in `Context.add*`.

**Axiom 2 — Horizon policy.**

* After a realization: set `H := 2`.
* After idle: `H := H + 1`.
  Implemented in `Engine.tick` / `Engine.tickDiscover`.

**Axiom 3 — Admissibility.**
A candidate X is admissible iff:

* Derivable from base within budget `H` (via `kappaMin?` using the same action alphabet used for novelty).
* Foundation/level discipline holds (no “future” strata leakage):

  * Let `L* = contextLevel(B)`. All prerequisites in the derivation must be at level `L* or L*-1`.
  * The final targets for installation may live at `L*+1`.
    See `foundationOKForTargets` and `targetLevel`.

**Axiom 4 — Selection.**
Among admissible candidates, accept those with `rho > Bar(τ)`; pick minimal overshoot `(rho - Bar)`; tiebreak by minimal κ; superpose if κ ties. Implemented in `selectWinners` and `selectWinnersX`.

**Axiom 5 — Coherent integration (two layers).**
Sealing cost adds `|J(X,B)|`, where `J` is the filters of interface basis `I` (last two layers) against X’s targets. In code: `kX := kDeriv + |interactionProfile(I, targetsX)|`. Layers tracked in `EngineState.layers` and updated with each realization (`frontierTargets` of realized `NoveltyReport`).

---

## 3) Effort κ, Novelty ν, Efficiency ρ — exact counting rules

### 3.1 Effort κ(X|B)

* Compute **minimal derivation length** to install all `targetsX` from base `B` under budget `H`. (`iddfsMin` + certificate.)
* **Sealing addend:** compute `I := interfaceBasis(last two layers)` then `J := interactionProfile(I, targetsX)` and set
  [
  \kappa = \texttt{kDeriv} + |J|
  ]
  (Already implemented in `Novelty.noveltyForPackage?` as `kDeriv + J.length`.)

**Special handling:** Sealed Π/Σ dual bundles may lift the raw budget (+2 steps) because sealing enforces a minimal (C,E,R) endo-triple. Code: `liftForSealedDual`.

### 3.2 Frontier construction (post, H)

* Actions = **finite alphabet**; novelty considers **all** action atoms not excluded.
* Compute `κ_post(Y)` under post context with post-bound; filter `κ_post ≤ H`.
* Compute truncated `κ_preEff(Y)` from base with pre-bound; failures count as `H+1`.
* Apply **schema keying** (Axiom 3′) to collapse duplicates and suppress endogenous attachments:

  * Universes keyed per level.
  * **All type formers collapse** to one class (endogenous).
  * Constructors keyed by **host** type.
  * Eliminators keyed by host; **comp rules keyed by eliminator**.
  * General terms keyed by host **except** Π/Σ aliases, classifier schemas, and constructor-neighborhood terms which are **exact**.
  * Endogenous classifier attachments (e.g., `schema_T`, eliminator of `T`) are removed via `excludeKeys`.
  * Optional host-specific suppressions at small H to avoid spurious gains.
* Result: `List FrontierEntry {target, kPost, kPreEff}`.

### 3.3 Novelty ν

* Default paper uses “count-improvement” notion. We implement **binary contribution per schema key**:
  [
  \Delta(Y) = 1 \ \text{iff}\ \tilde{\kappa}*{pre}(Y) > \kappa*{post}(Y)
  ]
* Sum over deduplicated entries (`sumContrib01`).
  (Alternate capped sums exist in `sumContribWithCaps` but the main run uses 0/1.)

### 3.4 Efficiency ρ

[
\rho(X)=\nu(X)/\kappa(X)
]
with `κ = kDeriv + |J|`, `ν = sumContrib01(frontier)`.

---

## 4) Selection Bar and timing

**Bar** at tick τ:
[
\text{Bar}(\tau) = \Phi(\tau)\cdot \Omega(\tau-1),
\quad \Phi(\tau)=\tau / \tau_{<}
]
computed by `PEN.Select.Bar.barGlobal(τ, lastRealizedTau?, history)`.

**Running average**
[
\Omega = \frac{\sum \nu}{\sum \kappa}
]
given by `omega(history)`.

**Fibonacci schedule.** With two-layer integration and the Complexity Scaling Hypothesis (CSH), the realized ticks follow `τ = F_{n+1}`. We do **not** hardcode Fib acceptance (unless using `schedule = .fibonacci` for gating experiments); instead, the engine should reproduce it empirically.

---

## 5) Data structures & modules (what each file must guarantee)

### Core CAD (atoms, derivations, κ-search)

* `PEN.CAD.Atoms`

  * `AtomicDecl`: universe / typeFormer / constructor / eliminator / compRule / term
  * `Context`: monotone, idempotent adders; `isValidInContext` enforces local prerequisites (e.g., eliminator requires host TF & usually a ctor).
* `PEN.CAD.Derivation`

  * `DerivCert {start}` witnessing `applyAll? start deriv = some finish`.
* `PEN.CAD.Kappa`

  * **IDDFS** search for minimal derivation to hit a goal; memoized finder `kappaMin?` returning `(k, DerivCert)`.

### Novelty scope & frontier

* `PEN.Novelty.Scope`

  * `ScopeConfig { actions, horizon, pre/post bounds, exclude, excludeKeys }`
  * Frontier enumerators (generic “missing elims”, “missing comp rules”; Π/Σ aliases; classifier maps).
  * **Schema keying** machinery `FrontierKey`, `keyOfTarget`, `dedupFrontierByKey`.
  * Contribution functions `contrib01`, `sumContrib01`.

### Novelty evaluation

* `PEN.Novelty.Novelty`

  * `interfaceBasis(last two layers)`, `interactionProfile`
  * `noveltyForPackage?` computes `κ`, frontier, `ν`, `ρ` and post context.

### Selection engine

* `PEN.Select.Bar`

  * Running `Ω`, `Bar` (`barGlobal`) and helpers.
* `PEN.Select.Engine`

  * **Package mode** and **Discovery mode**:

    * **Discovery:** build X bundles by mining `actions` via `Select.Discover` (single goals, TF-pairs, HIT bundles), enforce admissibility, seal, evaluate novelty, compare to bar, realize winners, update layers/horizon/history.
    * **Package:** same pipeline with curated `Pkg`s.
  * `EngineState` maintains `B`, `H`, `history`, `τ`, `lastRealizedTau?`, `layers`.

### Candidate discovery (Discovery mode)

* `PEN.Select.Discover`

  * From `actions`, for each not-yet-true atom `Y`, compute minimal derivation under `H`; delta vs base = **candidate X**.
  * Additionally constructs *pair TF bundles* and *HIT bundles* (TF + ≥2 ctors + elim).
  * **Sealing hints:** `sealHITTargets`, `sealPiSigmaTargets` add the canonical endo-triples for Π/Σ or full HITs so κ/ν reflect coherence.

### Effort heuristics (optional)

* `PEN.Select.Effort`

  * Bookkeeping to explain `κ` components (intro rules, essential elims, coherence discount). Not required by the engine but useful for reports.

### Certificates & checks

* `PEN.Cert.Types`, `PEN.Cert.Check`

  * Wraps κ/ν calculations into auditable packages, frontier entries, novelty bundles; replays κ-searches; verifies sums and `ρ` reproducibility.

---

## 6) Action alphabet (the finite search menu)

You **must** expose a stable, deterministic **finite list** of `AtomicDecl` actions that represent the “language of moves.” The current project already sets this up in `PEN.Genesis.globalActions`, including:

* Universes: `U0`, optionally `U1`
* Unit (`Unit`, `star`, `rec_Unit`, comp)
* Π / Σ (type formers, a canonical ctor/elim/comp to model endo-coherence)
* Basic HITs:

  * `S1` (1 point, 1 loop, with recursor + comp rules)
  * `S2` (1 point, 1 surface, with recursor + comp rules)
  * `S3` (TF; group structure emerges later via packages/terms)
* Hopf fibration scaffolding and affordances
* Classifier (e.g., `Man` with closure schema and eliminator)
* Optional late-stage DCT skeleton TFs & terms

**Do not** add unbounded generators; always keep actions finite and deterministic.

---

## 7) Per-tick algorithm (Discovery mode) — exact steps

1. **Bar**: compute `bar := barGlobal(τ, lastRealizedTau?, history)`.
2. **Discover candidates** X under the current budget `H`:

   * Singles (all not-yet-true goals) → delta vs base
   * TF pairs (classifier pair bundles if `H > 2`)
   * Generic HIT bundles (host with ≥2 ctors + elim)
   * Suppress strict sub-bundles (if X ⊂ Y as targets).
3. **Admissibility gates**:

   * Level discipline (`targetLevel ≤ L*+1`, derivation steps in `L*-1..L*`).
   * Small radius caps at `H≤2` (forbid multi-host TF-only, forbid ctor bursts, etc.).
   * Bundle sanity: for a non-classifier host, require **full HIT** (TF + ≥2 ctors + elim) if that host “looks like HIT” in actions; for classifiers, require sealed bundles for Π/Σ or `Man`.
4. **Sealing**:

   * `targetsCore := sealHITCoreNoElim(actions, X.targets)` → add missing TF/ctors as needed deterministically.
   * `targetsFinal := sealPiSigmaTargets(actions, targetsCore)` for Π/Σ duals.
   * Build `ScopeConfig` with:

     * `actions` possibly augmented with Π/Σ aliases, classifier maps, ctor neighborhoods, and “jump extras” (schema term of newly opened host).
     * `exclude := targetsFinal` and `excludeKeys := keysOfTargets(targetsFinal) ++ endoKeysForTFSet(targetsFinal) ++ host/elim suppressions`.
5. **Evaluate novelty** with interface basis from last two layers:
   `report := noveltyForPackage?(B, targetsFinal, scope, I=interfaceBasis(layers))`
   yields `post`, `kX`, `frontier`, `nu`, `rho`.
6. **Selection**: keep those with `rho > bar`; choose **minimal overshoot**, then **minimal κ**, then superpose ties.
7. **Realize**: union posts, pushTick with `Σν, Σκ`, set `H := 2`, `τ := τ+1`, `lastRealizedTau := previous τ`, and update layers to `[dedup frontierTargets_of_winners] ++ take 1 old`.
8. **Idle** (no winner): set `H := H+1`, `τ := τ+1`.

---

## 8) Genesis Sequence (target table)

The engine should reproduce the following (first 16 major realizations). Keep it as a **regression oracle**: your ledger must match within the same κ/ν across runs.

|    τ | Structure                    |   ν |  κ | ρ=ν/κ |  Bar |
| ---: | ---------------------------- | --: | -: | ----: | ---: |
|    1 | Universe 𝒰₀:𝒰₁             |   1 |  2 |  0.50 |    — |
|    2 | Unit 𝟙                      |   1 |  1 |  1.00 | 1.00 |
|    3 | Witness `⋆:𝟙`               |   2 |  1 |  2.00 | 1.00 |
|    5 | Π/Σ                          |   5 |  3 |  1.67 | 1.67 |
|    8 | S¹                           |   7 |  3 |  2.33 | 2.06 |
|   13 | Propositional truncation     |   8 |  3 |  2.67 | 2.60 |
|   21 | S²                           |  10 |  3 |  3.33 | 2.98 |
|   34 | S³ ≅ SU(2)                   |  18 |  5 |  3.60 | 3.44 |
|   55 | Hopf fibration               |  17 |  4 |  4.25 | 4.01 |
|   89 | Generic Lie groups           |   9 |  2 |  4.50 | 4.47 |
|  144 | Cohesion                     |  19 |  4 |  4.75 | 4.67 |
|  233 | Principal bundle connections |  26 |  5 |  5.20 | 5.06 |
|  377 | Curvature tensors            |  34 |  6 |  5.67 | 5.53 |
|  610 | Metric + ON frame bundle     |  43 |  7 |  6.14 | 6.05 |
|  987 | Hilbert functional           |  60 |  9 |  6.67 | 6.60 |
| 1597 | Dynamical Cohesive Topos     | 150 |  8 | 18.75 | 7.25 |

**Absorption principle.** NAT, Booleans, etc., are **not** separate realizations—Π/Σ absorbs them; likewise identity/path structure is **bundled** at the first HIT that needs it (e.g., S¹).

---

## 9) Naming conventions & deterministic choices

* **Constructor & eliminator names**: use the ones already present (`rec_S1`, `pair_Sigma`, etc.). Never generate random names.
* **Neighborhood terms**: `refl_<ctor>`, `transport_<ctor>` (pointed/transport around given constructor).
* **Classifier maps & schemas**: `schema_<T>`, and fixed short map set for `Man` (atlas, chart, transition, frame, …).
* **Alias terms for Π/Σ**:
  Π: `alias_arrow`, `alias_forall`, `alias_eval`
  Σ: `alias_prod`, `alias_exists`
  These are **exact-keyed** in novelty (do not collapse them away).

---

## 10) Levels & foundation discipline

* `PEN.Core.Levels` assigns *levels* (`LevelEnv`) to type formers & related atoms. Enforce:

  * Derivation **steps** for prerequisites are in current or previous stratum.
  * Final installation can be `L*+1`.
* Anything violating this is **inadmissible** and must be filtered out before evaluation.

---

## 11) Certificates and reproducibility

All outputs that affect selection must be **certified** and reproducible:

* κ-minimal derivation certificates (`DerivCert`) for installing X (`kDeriv`).
* Novelty reports (frontier entries with `kPost`, `kPreEff`), `nu`, `rho`.
* Optional: `PEN.Cert.Check` can re-run κ searches and frontier recomputations to assert consistency (used in tests and ledger runs).

---

## 12) Tests & acceptance criteria

### Must pass (deterministic)

1. **Early sanity:**

   * From empty `B`, `H=2`, installing `Unit` (TF only) yields novelty `ν=2` with endogenous eliminator suppressed (see `PEN.Tests.Novelty`).
   * Installing `star:Unit` after `Unit` yields `ν=2` via `refl_star`, `transport_star`.

2. **Fibonacci ticks** (discovery mode):

   * Running discovery with the provided `globalActions` and default config reproduces ticks 1..1597 as in the table (you can check first 16 rows for regression).

3. **Bar discipline**:

   * Winners must satisfy `rho > bar` and be the **closest above** the bar (minimal overshoot); κ tie → superpose winners.

4. **Two-layer integration**:

   * `EngineState.layers` must be updated with the **dedup frontier targets** of winners; `interfaceBasis` must take last two layers only.

### Nice to have

* Toggle `DiscoverConfig.debugFrontier := true` to dump a structured frontier audit (diagnose which targets were excluded, which keys collapsed, etc.).

---

## 13) Extending the sequence (how to add later steps safely)

* **Add actions** for new structures as **finite atoms**: TFs, ctors, elim, comp rules, canonical terms. Keep naming consistent.
* Provide **sealing hints** (like for Π/Σ or HITs) so the search derives minimal, coherent bundles deterministically.
* Update **level env** if new strata are introduced.
* Add **unit tests** mirroring `PEN.Tests.Novelty` that pin down ν and κ for a few new steps.

---

## 14) DCT (τ=1597) — minimal agent brief

* DCT is realized as a compact axiomatized **bundle** (TFs: `Topos`, `Coh`, `Time`, `DCT` + key terms: `Coh.shape`, `Coh.flat`, `Coh.sharp`, `Time.flow`, `DCT.evolve`) whose novelty spans geometry, logic, and time simultaneously.
* Keep it light: define these as **type formers** and **terms** in the action alphabet; sealing will charge |J| against the last two layers (cohesion & dynamics).
* Do **not** attempt to formalize the full category-theoretic semantics—just expose the atoms so the novelty engine can count affordances.

---

## 15) Do / Don’t (agent rules of thumb)

**Do**

* Always use the **same action alphabet** for κ-admissibility and for frontier κ-post computations at the current `H`.
* Always **seal** hosts (HITs) and Π/Σ duals deterministically before evaluation.
* Always enforce **level discipline** on derivations (prereqs at `L*-1..L*`).
* Keep **finite** and **deterministic** enumerations; deduplicate consistently (`dedupBEq`).

**Don’t**

* Don’t add or remove atoms during sealing that weren’t part of canonical sealing rules.
* Don’t count endogenous attachments of a TF towards its own novelty.
* Don’t let discovery mode bypass admissibility caps at small `H` (no multi-host TF-only bursts at `H ≤ 2`).

---

## 16) Quickstart for the agent

* Use **Discovery mode**:

  * Config = `PEN.Genesis.dcfg` (bar = twoTap by default; you can switch to golden-ratio by using `barGlobal` which is already used in discovery).
  * Actions = `PEN.Genesis.globalActions`.
* Drive **N ticks** with `PEN.Genesis.runDiscoverNTicksWithLedger dcfg st0 N`.
* Log each ledger line via `PEN.Genesis.fmt` and verify against the table.

---

## 17) Known corner cases & failure modes

* **k=1 integration** (using only last layer) will stall at Π/Σ because 2D coherence cannot be witnessed—this is intended; ensure `layers` carries two last frontiers.
* **Over-eager enumerators** can inflate the frontier; rely on schema keying and `excludeKeys` to keep novelty honest.
* **Budget starvation**: if κ-min search fails at `H`, it must return `none`; novelty computation should then **exclude** that target or treat pre as `H+1` (already done).

---

## 18) Files checklist (ensure these are present & hooked)

* `PEN/CAD/Atoms.lean` ✅
* `PEN/CAD/Derivation.lean` ✅
* `PEN/CAD/Kappa.lean` ✅
* `PEN/Novelty/Scope.lean` ✅
* `PEN/Novelty/Enumerators.lean` ✅
* `PEN/Novelty/Novelty.lean` ✅
* `PEN/Select/Bar.lean` ✅
* `PEN/Select/Discover.lean` ✅
* `PEN/Select/Effort.lean` (optional, for reporting) ✅
* `PEN/Select/Engine.lean` ✅
* `PEN/Core/Levels.lean` ✅
* `PEN/Cert/Types.lean`, `PEN/Cert/Check.lean` ✅
* `PEN/Genesis.lean` (runner, ledger formatting, global actions) ✅
* `PEN/Tests/Novelty.lean` (unit checks) ✅

---

## 19) Acceptance summary (what success looks like)

* Running discovery with the provided `globalActions` yields the **Genesis Sequence** milestones (at least the first 16) with **matching** `(τ, ν, κ, ρ, Bar)` as in the table.
* Efficiency rises monotonically in the ledger; the bar and horizons update per policy.
* Interface layers rotate (last two) and sealing cost is accounted as `+|J|`.
* Audits (`Cert.Check`) pass: κ-derivation certificates are minimal; frontier recomputations match recorded values.

---

If you follow this spec exactly, the agent will faithfully reproduce the paper’s dynamics and produce the Genesis Sequence deterministically in Lean 4.
