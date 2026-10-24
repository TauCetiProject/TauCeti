/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank.Closed
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic

/-!
# Rank sublevel sets on the symmetric subspace

The symmetric matrices of rank at most `k` form a closed, hence measurable, subset of
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)`, as the restriction of the closed set of all
matrices of rank at most `k` (`Matrix.isClosed_setOfPred_rank_le`).

Measurability is what upgrades an everywhere-true rank bound for a symmetric-matrix distribution,
such as the Gaussian-Gram Wishart law, to an almost-everywhere statement.

## Main declarations

* `TauCeti.isClosed_setOfPred_rank_le` — the symmetric matrices of rank at most `k` are closed.
* `TauCeti.measurableSet_setOfPred_rank_le` — they are measurable.
-/

public section

namespace TauCeti

variable {p : ℕ}

/-- **The symmetric matrices of rank at most `k` are closed.** -/
theorem isClosed_setOfPred_rank_le (k : ℕ) :
    IsClosed {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ k} :=
  (Matrix.isClosed_setOfPred_rank_le k).preimage continuous_subtype_val

/-- The symmetric matrices of rank at most `k` are measurable. -/
theorem measurableSet_setOfPred_rank_le (k : ℕ) :
    MeasurableSet {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ k} :=
  (isClosed_setOfPred_rank_le k).measurableSet

end TauCeti
