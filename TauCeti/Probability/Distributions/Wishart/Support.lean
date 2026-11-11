/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Wishart.Inverse.Basic

/-!
# Topological support of the Wishart density families

The nonsingular Wishart and inverse-Wishart densities are positive exactly on the open
positive-definite cone. Their topological supports are its closure, the positive-semidefinite
cone: singular positive-semidefinite matrices have zero probability but every neighbourhood
of one has positive probability.

The formulas cover every parameter value. Invalid scales or degrees give empty support,
and dimension zero gives the singleton symmetric space whenever the degree exceeds `-1`.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

open MeasureTheory Set

namespace TauCeti.Probability

variable {p : ℕ}

open scoped Classical in
/-- The topological support of a nonsingular Wishart law is the positive-semidefinite cone
at valid scale and degree, and empty otherwise. The singular boundary is included. -/
@[simp]
theorem support_nonsingularWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    (nonsingularWishartMeasure n S).support =
      if S.PosDef ∧ (p : ℝ) - 1 < n then
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef} else ∅ := by
  by_cases hS : S.PosDef
  · by_cases hn : (p : ℝ) - 1 < n
    · rw [ite_eq_left ⟨hS, hn⟩, nonsingularWishartMeasure_of_posDef hS hn,
        Measure.support_withDensity_eq_closure (measurable_nonsingularWishartPDF n S)
          (isOpen_posDefMatrix p), closure_posDefMatrix]
      ext A
      exact pos_iff_ne_zero.symm.trans (nonsingularWishartPDF_pos_iff hS hn)
    · simp [hn, nonsingularWishartMeasure_of_le S (le_of_not_gt hn)]
  · simp [hS]

open scoped Classical in
/-- The topological support of an inverse-Wishart law is the positive-semidefinite cone
at valid scale and degree, and empty otherwise. Inversion does not remove the singular
boundary from the topological support. -/
@[simp]
theorem support_inverseWishartMeasure (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    (inverseWishartMeasure n S).support =
      if S.PosDef ∧ (p : ℝ) - 1 < n then
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef} else ∅ := by
  by_cases hS : S.PosDef
  · by_cases hn : (p : ℝ) - 1 < n
    · rw [ite_eq_left ⟨hS, hn⟩, inverseWishartMeasure_of_posDef hS hn,
        Measure.support_withDensity_eq_closure (measurable_inverseWishartPDF n S)
          (isOpen_posDefMatrix p), closure_posDefMatrix]
      ext A
      exact pos_iff_ne_zero.symm.trans (inverseWishartPDF_pos_iff hS hn)
    · simp [hn, inverseWishartMeasure_of_le S (le_of_not_gt hn)]
  · simp [hS]

end TauCeti.Probability
