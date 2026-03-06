# The Principle of Efficient Novelty (PEN)

This repository contains the Lean 4 research prototype for the "Principle of Efficient Novelty" (PEN), a computational framework for modeling mathematical discovery. The core thesis, theoretical proofs, and empirical results are detailed in two companion papers.

## Abstract

Why do some mathematical abstractions feel more fundamental than others? This project investigates that question by modeling mathematical discovery as an evolutionary process under selection pressure for **efficiency**—the ratio of a concept's enabling power (novelty) to its definitional complexity (effort).

The framework proves that mathematical evolution in foundations with two-dimensional coherence (like Homotopy Type Theory) is not arbitrary but is governed by precise dynamical laws. Key findings include:

1.  **Unbounded Growth:** Efficiency-driven discovery compels unbounded growth in conceptual power, or else it must stagnate completely.
2.  **The Extensional/Intensional Divide:** Foundations with one-dimensional equality (like ZFC set theory or MLTT+UIP) are proven to stagnate. Unbounded growth requires two-dimensional equality structure.
3.  **The Complexity Scaling Theorem:** A proven coherence theorem showing that the complexity of integrating new ideas in 2D foundations follows the Fibonacci sequence ($\sigma_{n+1} = \sigma_n + \sigma_{n-1}$).
4.  **The Genesis Sequence:** The model generates a specific, reproducible sequence of mathematical structures, heavily dominated by geometry, culminating in a novel framework we call the **Dynamical Cohesive Topos**.

This work suggests that the efficient organization of mathematical knowledge is constrained by deep, computable, and universal principles, with the golden ratio ($\phi \approx 1.618$) emerging as a fundamental constant of conceptual acceleration.

## Primary Artifacts: The Papers

The definitive presentation of this research is in the two companion papers. **These are the primary artifacts for review and citation.**

  * **Part I: The Theory**

      * **Title:** *The Principle of Efficient Novelty: Fibonacci Timing and Coherence Theorems in Type Theory*
      * **Focus:** Establishes the formal PEN framework, proves the four core theorems (Unbounded Growth, 2-Layer Optimality, No-Go Theorem, Complexity Scaling), and presents the cross-foundational validation.
      * [**Paper 1 (PDF)**](https://github.com/efficient-novelty/pen/blob/main/pen_cst.pdf)

  * **Part II: The Content**

      * **Title:** *The Genesis Sequence: Emergent Mathematical Structures from Efficient Novelty*
      * **Focus:** Provides a detailed analysis of the first sixteen emergent structures, explains patterns like absorption and geometric dominance, and provides a full technical exposition of the novel Dynamical Cohesive Topos.
      * [**Paper 2 (PDF)**](https://github.com/efficient-novelty/pen/blob/main/pen_genesis.pdf)
 

## Project Status & Code

This repository contains the complete Lean 4 implementation used to generate and validate the results presented in the papers.

**Please Note:** This is a research prototype. The code is provided for transparency and reproducibility. While largely complete, it is a work-in-progress and may contain minor bugs. The CI/CD infrastructure is not yet fully configured, so automated test reports may not reflect the correct status of the codebase. The papers should be considered the canonical source.

### Blind discovery executable and compliance checks

This repo includes a dedicated Lane 1 executable, `discover_blind`, intended for fail-closed blind discovery runs.

- Print defaults: `discover_blind --print-config`
- Emit machine-readable blind ledger rows: `discover_blind --ticks <n> --ledger-format jsonl|csv`
- Run compliance suite: `make test-blindness`
- Generate baseline blind artifacts: `make lane1-baseline`
- Replay and verify baseline: `make lane1-replay`

The blindness CI job is named `test:blindness` (`.github/workflows/blindness.yml`).
The publication gate job is `lane1-release-gate` (`.github/workflows/lane1-release-gate.yml`) and is activated when `docs/LANE1_CLAIM.md` exists.

Baseline outputs are written to `artifacts/lane1/baseline/`, including auto-generated `evidence_table.md` for manuscript linkage.

### Repository Structure

The core logic is found in the `PEN/` directory:

  * `PEN/CAD/`: The Contextual Atomic Declaration language, the foundational layer for representing mathematical contexts.
  * `PEN/Novelty/`: The implementation of the novelty-search engine, including frontier enumerators and the scope configuration.
  * `PEN/Select/`: The core PEN selection engine, including the bar mechanism and discovery algorithms.
  * `PEN/Genesis.lean`: The main executable file for running the discovery process and generating the Genesis Sequence.

### How to Cite

If you would like to cite this work, please use the following BibTeX entry (replace arXiv ID once available):

```
@misc{lande2025pen,
      title={The Principle of Efficient Novelty I: Fibonacci Timing and Coherence Theorems in Type Theory}, 
      author={Halvor Lande},
      year={2025},
      eprint={YYMM.NNNNN},
      archivePrefix={arXiv},
      primaryClass={cs.LO}
}
```

### Contact

Halvor Lande - [halvor.s.lande@gmail.com](mailto:halvor.s.lande@gmail.com)