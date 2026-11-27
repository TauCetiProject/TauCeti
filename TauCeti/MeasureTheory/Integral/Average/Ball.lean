/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Averages over concentric balls

Let `μ` be an additive Haar measure on a finite-dimensional real normed space of dimension `n`. On
concentric balls `B_ρ ⊆ B_r` the volume ratio is `(ρ / r)ⁿ`, so the average over the smaller ball
of a nonnegative function is at most `(r / ρ)ⁿ` times its average over the larger one:

`⨍_{B_ρ} g ≤ (r / ρ)ⁿ ⨍_{B_r} g`.

This passes a bound on the larger ball to every smaller ball, at the cost of the volume ratio, as
in mean oscillation estimates where the comparison function is controlled only on the larger
ball.

## Main results

* `TauCeti.setAverage_ball_le_div_pow_mul_setAverage_ball`: `⨍_{B_ρ} g ≤ (r / ρ)ⁿ ⨍_{B_r} g`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Averages over concentric balls.** For `0 < ρ ≤ r` and `g ≥ 0` integrable on `B_r`, the
average of `g` over `B_ρ = ball x₀ ρ` is at most `(r / ρ)ⁿ` times its average over
`B_r = ball x₀ r`, where `n` is the dimension. -/
theorem setAverage_ball_le_div_pow_mul_setAverage_ball {g : E → ℝ} {x₀ : E} {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hg0 : 0 ≤ᵐ[μ.restrict (ball x₀ r)] g)
    (hg : IntegrableOn g (ball x₀ r) μ) :
    ⨍ x in ball x₀ ρ, g x ∂μ ≤ (r / ρ) ^ finrank ℝ E * ⨍ x in ball x₀ r, g x ∂μ := by
  have hr : 0 < r := hρ.trans_le hρr
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ 0 one_pos
  have hmono : ∫ x in ball x₀ ρ, g x ∂μ ≤ ∫ x in ball x₀ r, g x ∂μ :=
    setIntegral_mono_set hg hg0 (ball_subset_ball hρr).eventuallySubset
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, μ.addHaar_real_ball_of_pos x₀ hρ,
    μ.addHaar_real_ball_of_pos x₀ hr]
  calc (ρ ^ finrank ℝ E * μ.real (ball (0 : E) 1))⁻¹ * ∫ x in ball x₀ ρ, g x ∂μ
      ≤ (ρ ^ finrank ℝ E * μ.real (ball (0 : E) 1))⁻¹ * ∫ x in ball x₀ r, g x ∂μ :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by
        rw [div_pow]
        field_simp

end TauCeti
