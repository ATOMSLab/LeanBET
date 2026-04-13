# LeanBET

**Formally verified BET surface area analysis in Lean 4.**

LeanBET is a fully executable and formally verified implementation of the Brunauer–Emmett–Teller (BET) surface area analysis pipeline, implemented in the [Lean 4](https://leanprover.github.io/) theorem prover. It covers the complete BETSI-style workflow — window enumeration, monotonicity checks, knee selection, and linear regression — and connects each computational step to a machine-checked mathematical proof.

> Associated manuscript: *LeanBET: Formally-verified surface area calculations in Lean* — Ugwuanyi, Jones, Velkey, and Josephson (2026).

---

## Overview

BET surface area analysis is standard in materials characterization, but its results can vary significantly depending on how the fitting range is chosen. BETSI (BET Surface Identification) addresses this by exhaustively enumerating fitting windows and applying the Rouquerol consistency criteria algorithmically. LeanBET goes further: it not only reproduces the BETSI workflow, but formally proves that each step does what it is supposed to do.

The key design idea is **polymorphism**: the same implementation runs over `Float` for computation and over `ℝ` (the real numbers) for proof. This is managed through the `BETLike` typeclass, which provides arithmetic, ordering, absolute value, and square root operations for both types.

```
f(x : α)
   ├── f(x : ℝ)    →  Proofs
   └── f(x : Float) →  Execution
```

---

## What is Formally Verified

LeanBET provides machine-checked proofs for the following:

| Theorem | What it guarantees |
|---|---|
| **A.1** BET linearization | The BET-transformed quantity is exactly affine in relative pressure whenever the nonlinear BET equation holds |
| **A.2** Window enumeration | The procedure returns *exactly* the valid contiguous fitting windows — no more, no less |
| **A.3** Monotonicity checks | A passing check certifies the nondecreasing property in the mathematical sense |
| **A.4** Linear regression | A successful fit is a global least-squares minimizer of the residual sum of squares |
| **A.5** BET parameter extraction | Reported `nm` and `C` values agree with their specification-level definitions |
| **A.6** Knee filtering | The maximal-end-index filter keeps exactly the intended candidates |
| **A.7** Final selection | The reported result is drawn from the admissible, maximal-end-index candidates |

---

## Results

LeanBET was benchmarked against the BETSI reference implementation on 19 adsorption isotherms from the Osterrieth et al. (2022) round-robin dataset:

- **18 of 19 isotherms** agree with BETSI to machine precision (IEEE 754 floating-point)
- **UiO-66** shows a deviation of ~0.36 m²/g (~0.03%), the cause of which remains under investigation

---

## Getting Started

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (developed on Lean 4.27.0)
- [Mathlib4](https://github.com/leanprover-community/mathlib4) (managed automatically via `lake`)

### Build

```bash
git clone https://github.com/ATOMSLab/LeanBET
cd LeanBET
lake update
lake build
```

### Run the benchmark

```bash
lake exe LeanBET
```

This runs the BETSI-style pipeline on the benchmark isotherms and reports results alongside BETSI reference values.

---

## Key Design Decisions

### `BETLike` typeclass

The `BETLike` typeclass is the central abstraction that enables polymorphism between `Float` and `ℝ`. It provides arithmetic operations, proposition-valued ordering with `DecidableRel` instances, `abs`, and `sqrt`. Unlike purely computational typeclasses (such as `RealLike` in [LeanLJ](https://github.com/ATOMSLab/LeanLJ)), `BETLike` uses `Prop`-valued comparisons, which integrate naturally with Lean's mathematical proof infrastructure.

### Polymorphic functions

All core functions (`linearRegression`, `betLinearize`, `enumerateWindows`, etc.) are polymorphic over `[BETLike α]`. This means:
- Instantiating with `Float` gives an executable pipeline
- Instantiating with `ℝ` gives the proof target

The two are linked: proving a property for the `ℝ` version provides the mathematical justification for trusting the `Float` version.

### Separation of checks and specifications

Each executable check (e.g., monotonicity scanning, admissibility filtering) is kept distinct from its mathematical specification. The proofs then formally connect the two, establishing soundness: *if the check passes, the specification holds*.

---

## Limitations and Notes

- Proofs are over `ℝ`; floating-point execution carries the usual IEEE 754 caveats. For the adsorption datasets here, experimental noise far exceeds double-precision round-off.
- LeanBET uses linear interpolation where BETSI uses PCHIP (Piecewise Cubic Hermite Interpolating Polynomial) interpolation. This does not violate the formal specifications but can affect window selection in borderline cases (as seen with UiO-66).
- The `BETLike ℝ` instance is `noncomputable`, as expected for real-number arithmetic in Lean/Mathlib.
- Writing polymorphic functions from the start adds typeclass complexity. We recommend developing `Float` and `ℝ` versions separately first, then merging — see the manuscript for details on our development process.

---

## Citation

If you use LeanBET in your work, please cite:

```bibtex
@article{ugwuanyi2026leanbet,
  title   = {LeanBET: Formally-verified surface area calculations in Lean},
  author  = {Ugwuanyi, Ejike D. and Jones, Colin T. and Velkey, John and Josephson, Tyler R.},
  year    = {2026},
}
```

---

## Acknowledgements

This material is based on work supported by the National Science Foundation (NSF) CAREER Award #2236769.

---

## Contact

Tyler R. Josephson — [tjo@umbc.edu](mailto:tjo@umbc.edu)  
ATOMS Lab, University of Maryland, Baltimore County
