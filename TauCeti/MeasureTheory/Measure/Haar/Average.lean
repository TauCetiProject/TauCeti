/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Averages over balls for an additive Haar measure

For an additive Haar measure on a finite-dimensional real normed space, the measure of a ball of
radius `R` is `(R / ρ) ^ dim E` times the measure of a ball of radius `ρ`. Consequently the average
of a nonnegative function over a ball `B(x, ρ) ⊆ B(x₀, R)` is at most `(R / ρ) ^ dim E` times its
average over `B(x₀, R)`: the integral can only grow on the larger ball, and the ratio of the
volumes is explicit. This comparison is the basic step of stopping-time arguments with balls.

## Main statements

* `TauCeti.setLAverage_ball_le`: the average over `B(x, ρ) ⊆ B(x₀, R)` is at most
  `(R / ρ) ^ dim E` times the average over `B(x₀, R)`.
* `TauCeti.setAverage_ball_le`: the same for the Bochner average of a nonnegative real function.
* `TauCeti.setIntegral_ball_le_of_setAverage_ball_le`: an averaged decay bound
  `⨍_{B(x₀, ρ)} f ≤ K (ρ / R) ⨍_{B(x₀, R)} g` on concentric balls gives the integrated one
  `∫_{B(x₀, ρ)} f ≤ K (ρ / R) ^ (dim E + 1) ∫_{B(x₀, R)} g`.
* `TauCeti.mul_ofReal_div_pow_le_setLAverage_ball`: if `g ≥ δ` on `B(z, ρ) ⊆ B(c, r)`, the
  average of `g` over `B(c, r)` is at least `δ (ρ / r) ^ dim E`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The average over a ball `B(x, ρ) ⊆ B(x₀, R)` is at most `(R / ρ) ^ dim E` times the average over
`B(x₀, R)`. -/
theorem setLAverage_ball_le (g : E → ℝ≥0∞) {x x₀ : E} {ρ R : ℝ} (hρ : 0 < ρ)
    (hsub : ball x ρ ⊆ ball x₀ R) :
    ⨍⁻ y in ball x ρ, g y ∂μ ≤
      ENNReal.ofReal ((R / ρ) ^ finrank ℝ E) * ⨍⁻ y in ball x₀ R, g y ∂μ := by
  have hR : 0 < R := by
    have := hsub (mem_ball_self hρ)
    exact dist_nonneg.trans_lt (mem_ball.1 this)
  refine (setLAverage_le_div_mul_setLAverage_of_subset hsub measure_ball_lt_top.ne).trans_eq ?_
  congr 1
  have hball : μ (ball x₀ R) = ENNReal.ofReal ((R / ρ) ^ finrank ℝ E) * μ (ball x ρ) := by
    conv_lhs => rw [← div_mul_cancel₀ R hρ.ne']
    rw [Measure.addHaar_ball_mul_of_pos μ x₀ (div_pos hR hρ), Measure.addHaar_ball_center μ x]
  rw [hball, ENNReal.mul_div_cancel_right (measure_ball_pos μ x hρ).ne' measure_ball_lt_top.ne]

/-- The real form of `TauCeti.setLAverage_ball_le`: the average of a nonnegative function `g`,
integrable on `B(x₀, R)`, over a ball `B(x, ρ) ⊆ B(x₀, R)` is at most `(R / ρ) ^ dim E` times its
average over `B(x₀, R)`. -/
theorem setAverage_ball_le {g : E → ℝ} {x x₀ : E} {ρ R : ℝ} (hρ : 0 < ρ)
    (hsub : ball x ρ ⊆ ball x₀ R) (hg : IntegrableOn g (ball x₀ R) μ)
    (hg0 : ∀ y ∈ ball x₀ R, 0 ≤ g y) :
    ⨍ y in ball x ρ, g y ∂μ ≤ (R / ρ) ^ finrank ℝ E * ⨍ y in ball x₀ R, g y ∂μ := by
  have hR : 0 < R := pos_of_mem_ball (hsub (mem_ball_self hρ))
  have h0 : 0 ≤ᵐ[μ.restrict (ball x₀ R)] g := (ae_restrict_mem measurableSet_ball).mono hg0
  have h := setLAverage_ball_le (μ := μ) (fun y ↦ ENNReal.ofReal (g y)) hρ hsub
  rw [setLAverage_eq, setLAverage_eq, ← ofReal_setAverage (hg.mono_set hsub)
    (ae_restrict_of_ae_restrict_of_subset hsub h0), ← ofReal_setAverage hg h0,
    ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (average_nonneg_of_ae h0))).1 h

/-- **Integrated decay from averaged decay.** An averaged decay bound on concentric balls gives the
integrated one, one order faster: if `⨍_{B(x₀, ρ)} f ≤ K (ρ / R) ⨍_{B(x₀, R)} g` with `0 ≤ ρ`,
then `∫_{B(x₀, ρ)} f ≤ K (ρ / R) ^ (dim E + 1) ∫_{B(x₀, R)} g`, since
`μ(B(x₀, ρ)) = (ρ / R) ^ dim E μ(B(x₀, R))`. -/
theorem setIntegral_ball_le_of_setAverage_ball_le {f g : E → ℝ} {x₀ : E} {ρ R K : ℝ}
    (hρ : 0 ≤ ρ) (h : ⨍ x in ball x₀ ρ, f x ∂μ ≤ K * (ρ / R) * ⨍ x in ball x₀ R, g x ∂μ) :
    ∫ x in ball x₀ ρ, f x ∂μ ≤ K * (ρ / R) ^ (finrank ℝ E + 1) * ∫ x in ball x₀ R, g x ∂μ := by
  rcases hρ.eq_or_lt with rfl | hρ
  · simp
  have hω : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  rw [setAverage_eq, smul_eq_mul, μ.addHaar_real_ball_of_pos x₀ hρ,
    inv_mul_le_iff₀ (by positivity)] at h
  rcases le_or_gt R 0 with hR | hR
  · simpa [ball_eq_empty.2 hR] using h
  rw [setAverage_eq, smul_eq_mul, μ.addHaar_real_ball_of_pos x₀ hR] at h
  refine h.trans_eq ?_
  simp only [div_pow]
  field_simp
  ring

/-- **A lower bound from a sub-ball.** If `g ≥ δ` on a ball `B(z, ρ) ⊆ B(c, r)`, then the average
of `g` over `B(c, r)` is at least `δ (ρ / r) ^ dim E`. With `g = ‖f - a‖ₑ` and `a` the average of
`f` over `B(c, r)`, this bounds the mean oscillation of `f` on `B(c, r)` from below. -/
theorem mul_ofReal_div_pow_le_setLAverage_ball {g : E → ℝ≥0∞} {c z : E} {r ρ : ℝ} {δ : ℝ≥0∞}
    (hρ : 0 < ρ) (hsub : ball z ρ ⊆ ball c r) (h : ∀ y ∈ ball z ρ, δ ≤ g y) :
    δ * ENNReal.ofReal ((ρ / r) ^ finrank ℝ E) ≤ ⨍⁻ y in ball c r, g y ∂μ := by
  have hr : 0 < r := pos_of_mem_ball (hsub (mem_ball_self hρ))
  have hδ : δ ≤ ⨍⁻ y in ball z ρ, g y ∂μ := by
    rw [← setLAverage_const (μ := μ) (measure_ball_pos μ z hρ).ne' measure_ball_lt_top.ne δ]
    exact laverage_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ h))
  have hcancel :
      ENNReal.ofReal ((r / ρ) ^ finrank ℝ E) * ENNReal.ofReal ((ρ / r) ^ finrank ℝ E) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, div_mul_div_cancel₀ hρ.ne',
      div_self hr.ne']
    simp
  calc δ * ENNReal.ofReal ((ρ / r) ^ finrank ℝ E)
      ≤ ENNReal.ofReal ((r / ρ) ^ finrank ℝ E) * (⨍⁻ y in ball c r, g y ∂μ) *
          ENNReal.ofReal ((ρ / r) ^ finrank ℝ E) := by
        gcongr
        exact hδ.trans (setLAverage_ball_le g hρ hsub)
    _ = ⨍⁻ y in ball c r, g y ∂μ := by
        rw [mul_right_comm, hcancel, one_mul]

end TauCeti
