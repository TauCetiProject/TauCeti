/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# A constant bounded almost everywhere by a function in `Lᵖ`

If a real number `t` satisfies `t ≤ ‖u y‖` for almost every `y` with respect to a nonzero finite
measure `μ`, then taking `Lᵖ(μ)` seminorms of both sides gives `t ≤ μ(X)^{-1/p} ‖u‖_{Lᵖ(μ)}`
(`MeasureTheory.le_toReal_eLpNorm_div_of_ae_le`). Applied to a restricted measure `μ.restrict s`
and to `t - A`, this is the averaging step that turns a pointwise oscillation bound
`t ≤ ‖u y‖ + A` on `s` into a sup bound.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- **A constant bounded by `‖u‖` almost everywhere.** Let `p ≠ 0`, let `μ` be a nonzero finite
measure and let `u` have finite `Lᵖ(μ)` seminorm. If `t ≤ ‖u y‖` for almost every `y`, then
`t ≤ ‖u‖_{Lᵖ(μ)} / μ(X)^{1/p}`. -/
theorem le_toReal_eLpNorm_div_of_ae_le (hp : p ≠ 0) (h0 : μ ≠ 0) (htop : μ Set.univ ≠ ∞)
    {u : X → F} (hu : eLpNorm u p μ ≠ ∞) {t : ℝ} (h : ∀ᵐ y ∂μ, t ≤ ‖u y‖) :
    t ≤ (eLpNorm u p μ).toReal / (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rcases lt_or_ge t 0 with ht | ht
  · exact ht.le.trans (by positivity)
  have hle : eLpNorm (fun _ : X => t) p μ ≤ eLpNorm u p μ :=
    eLpNorm_mono_ae aestronglyMeasurable_const
      (h.mono fun y hy => by rwa [Real.norm_of_nonneg ht])
  rw [eLpNorm_const _ hp h0] at hle
  have hreal := ENNReal.toReal_mono hu hle
  rw [ENNReal.toReal_mul, toReal_eNorm, Real.norm_of_nonneg ht, ← ENNReal.toReal_rpow] at hreal
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (ENNReal.toReal_pos (by simpa using h0) htop) _)]
  exact hreal

end MeasureTheory
