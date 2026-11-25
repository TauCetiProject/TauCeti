/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.EmpiricalMeasure

/-!
# Empirical measures of orbits

A uniform, quantitative form of Mathlib's
`MeasureTheory.tendsto_integral_comp_sub_integral_empiricalMeasure_of_isBoundedUnder`: for a
function `g` bounded by `C`, the integrals of `g ∘ T` and `g` against the empirical measure of an
orbit of length `n + 1` differ by at most `2 * C / (n + 1)`, whatever the starting point.
-/

public section

open MeasureTheory

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The empirical measure of the orbit of `x` of length `n + 1` integrates `g ∘ T - g` to
`(g (T^[n + 1] x) - g x) / (n + 1)`, which is at most `2 * C / (n + 1)` in norm when `g` is
bounded by `C`. -/
theorem norm_integral_comp_sub_integral_empiricalMeasure_le (T : X → X) {g : X → E} {C : ℝ}
    (hg : ∀ y, ‖g y‖ ≤ C) (x : X) (n : ℕ) :
    ‖(∫ y, (g ∘ T) y ∂(empiricalMeasure T x n)) - ∫ y, g y ∂(empiricalMeasure T x n)‖ ≤
      2 * C / (n + 1) := by
  by_cases hE : CompleteSpace E
  swap
  · rw [integral_of_not_completeSpace hE, integral_of_not_completeSpace hE, sub_zero, norm_zero]
    have := (norm_nonneg (g x)).trans (hg x)
    positivity
  rw [integral_empiricalMeasure_eq_birkhoffaverage, integral_empiricalMeasure_eq_birkhoffaverage,
    birkhoffAverage_comp_apply, ← dist_eq_norm,
    birkhoffAverage_apply_congr_ring (R := NNReal) ℝ, birkhoffAverage_apply_congr_ring
      (R := NNReal) ℝ, dist_birkhoffAverage_apply_birkhoffAverage]
  push_cast
  gcongr
  have h1 := hg (T^[n + 1] x)
  have h2 := hg x
  exact (dist_le_norm_add_norm _ _).trans (by linarith)

end TauCeti
