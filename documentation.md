# High-Level Overview of the PEN Framework Implementation

This Lean 4 codebase implements the Principle of Efficient Novelty (PEN) framework from the attached paper. It's an automated system that discovers mathematical structures in a specific order by maximizing "efficiency" (novelty per unit of effort).

## Core Architecture

The code is organized into several layers that mirror the paper's theoretical structure:

### 1. **Foundation Layer (PEN/CAD/)**
The "Context And Declarations" module implements the basic state space:

- **`Atoms.lean`**: Defines atomic operations in type theory (declaring universes, type formers, constructors, eliminators, computation rules, terms). Each is a single irreducible step.
- **`Derivation.lean`**: Sequences of atomic steps with validity certificates proving they execute successfully.
- **`Kappa.lean`**: Computes **effort κ** - the minimal number of atomic steps needed to derive a goal from a base context, using iterative-deepening depth-first search.

**This implements the effort kernel KB(Y) from Definition 2.**

### 2. **Novelty Layer (PEN/Novelty/)**
Measures how much a candidate structure "unlocks":

- **`Scope.lean`**: Defines the **frontier** S(B,H) - all structures derivable within horizon H. Implements the key "schema keying" system (Axiom 3) that groups similar structures (e.g., all constructors for a given type) into equivalence classes.
- **`Novelty.lean`**: Computes **novelty ν** by comparing frontiers before/after adding a candidate: how many structures become cheaper or newly accessible? Implements Definition 7 and sealing (Definition 4).
- **`Enumerators.lean`**: Provides reusable enumerators for common patterns (Π/Σ aliases, classifier maps).

**This implements the novelty measure ν(X|B,H) and frontier computation.**

### 3. **Selection Engine (PEN/Select/)**
The evolutionary dynamics:

- **`Bar.lean`**: Computes the selection threshold Bar(τ) = Φ(τ)·Ω(τ-1) from Definition 9. Tracks running efficiency average Ω and time dilation factor Φ.
- **`Discover.lean`**: **Automatically discovers candidate bundles** by running κ-search for each atomic goal, extracting the "delta" (new atoms introduced), and bundling related structures (e.g., type former + constructors + eliminator for HITs).
- **`Engine.lean`**: **The main evolution loop** implementing all 5 axioms:

**Implementation of the 5 Axioms:**

1. **Axiom 1 (Cumulative Growth)**: State B grows monotonically - `EngineState` accumulates declarations, never removes them.

2. **Axiom 2 (Horizon Policy)**: Horizon H tracks search depth. After realization: `H := 2`. After idle tick: `H := H + 1`. (See `tick` function in `Engine.lean`)

3. **Axiom 3 (Admissibility)**: Candidates must be:
   - Derivable from B (checked by κ-search succeeding)
   - Within horizon: κ(X|B) ≤ H
   - Properly sealed with coherence witnesses (enforced by `sealHITTargets`, `sealPiSigmaTargets`)
   
4. **Axiom 4 (Selection)**: `selectWinnersX` function implements:
   - Filter to ρ(X) ≥ Bar(τ)
   - Pick **minimal overshoot** (ρ - Bar)
   - Tie-break by minimal κ
   - Superposition if still tied

5. **Axiom 5 (Coherent Integration)**: The "two-layer integration" from Section 4:
   - New structures must establish coherence with previous two integration layers Ln, Ln-1
   - Implemented via `mkScope` which excludes endogenous attachments using `excludeKeys`
   - Integration gap ∆n+1 = |interface basis| grows as Fibonacci sequence

### 4. **Pattern Recognition (PEN/Grammar/)**
Pre-defined templates for common structures:

- **`HIT.lean`**: Specifications for Higher Inductive Types (circles, spheres) with their constructors and eliminators.
- **`Classifier.lean`**: Classifier-level structures (like manifolds) with closure schemas.

These are **not hardcoded into the selection** - they're just convenient abstractions. The discovery process (`Discover.lean`) automatically finds these patterns.

### 5. **Auditing (PEN/Cert/)**
Generates certificates proving calculations are correct:

- **`Types.lean`**: Certificate structures (PackageCert, FrontierEntryCert, NoveltyCert)
- **`Check.lean`**: Validators that replay computations to verify κ, ν, and ρ

## How It Generates the Genesis Sequence

The **`Genesis.lean`** orchestrator runs the discovery loop:

```lean
tickDiscover : DiscoverConfig → EngineState → XTickResult
```

**Each tick:**

1. **Compute current bar**: `Bar(τ) = (τ/τ_prev) × Ω(τ-1)` using `barGlobal`

2. **Discover candidates**: `discoverCandidates` tries every atomic goal not yet in B:
   - Run κ-search within horizon H
   - Extract delta (new atoms)
   - Bundle related structures (pairs, HIT cores)
   - Apply level discipline (Axiom 4's foundation constraint)

3. **Evaluate each candidate**: `evalX?` computes:
   - Sealed targets (adding required coherence)
   - Exact κ using the same action alphabet
   - Novelty ν via frontier comparison
   - Efficiency ρ = ν/κ

4. **Select winners**: `selectWinnersX`:
   - Keep only ρ ≥ Bar
   - Prefer "attached" work (builds on existing structures)
   - Pick minimal overshoot
   - Realize all κ-tied candidates (superposition)

5. **Update state**: `applyRealizationX`:
   - Merge winner contexts into B
   - Push (Σν, Σκ) to history
   - Reset H := 2
   - Update integration layers

**The Fibonacci timing emerges from the two-layer integration:**
- Each new structure seals against interfaces from Ln and Ln-1
- Interface size grows as σn+1 = σn + σn-1 (Complexity Scaling Hypothesis)
- Integration gaps ∆n = Fn exactly (observed, conjectured to be structural)
- Realization times τn = Σ∆i = Fn+1

## Key Design Decisions

1. **Automatic discovery**: The system doesn't have a pre-loaded library. It discovers S¹, Π-types, etc. by trying all atomic goals and bundling the efficient derivations.

2. **Schema keying** (Axiom 3): Groups structures by "host type" (e.g., all terms on S¹) or exact names (Π/Σ aliases) to prevent double-counting endogenous attachments.

3. **Sealing** enforces coherence: Adding the circle requires not just the type and loop constructor, but witnesses that transport, connections, etc. behave correctly.

4. **Certificates throughout**: Every κ, ν computation produces a certificate with the actual derivation, making results auditable.

The paper's Theorem 1 (unbounded growth) and Theorem 7 (Fibonacci timing) are validated by running `runDiscoverNTicksWithLedger` which produces Table 5.1's Genesis Sequence with zero deviations from predicted timing.