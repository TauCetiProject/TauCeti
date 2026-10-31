/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.LevyMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrability of the compensated stable characteristic kernel

For non-Gaussian stable parameters, the Lévy measure has infinite mass near zero. Its
second moment on a bounded neighbourhood of zero is nevertheless finite. Consequently the
compensation
`exp (t * x * I) - 1 - t * sin x * I` is absolutely integrable: it vanishes quadratically
at zero and is bounded outside a neighbourhood of zero. The cutoff integrals converge to
this integral,
which is the analytic input to compensated compound Poisson approximations.

The estimates reuse Mathlib's complex exponential remainder bound and its local
integrability criterion for radial powers.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology

namespace TauCeti.Probability

/-- The small jumps of a stable Lévy measure have a finite second moment on every ball.
The assertion includes the zero measures at invalid parameters. -/
theorem integrableOn_sq_stableLevyMeasure (α β r : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ 2) (Metric.ball 0 r) (stableLevyMeasure α β) := by
  by_cases h : 0 < α ∧ α < 2 ∧ |β| ≤ 1
  · have hd : Measurable (stableLevyDensity α β) :=
      measurable_stableLevyDensity.comp
        (measurable_const.prodMk measurable_id :
          Measurable (fun x : ℝ ↦ ((α, β), x)))
    rw [IntegrableOn, stableLevyMeasure_def, restrict_withDensity measurableSet_ball,
      integrable_withDensity_iff_integrable_smul' hd.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (stableLevyDensity_nonneg _ _ _), smul_eq_mul]
    apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ ℝ)
      (α := α - 1) (C := 2 * (Gamma (1 + α) * sin (π * α / 2) / π))
      (by simp only [Module.finrank_self]; norm_num; linarith [h.2.1]) ?_ (by fun_prop)
    filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0)] with x hx
    have hnorm : ‖stableLevyDensity α β x * x ^ 2‖ = stableLevyDensity α β x * x ^ 2 :=
      Real.norm_of_nonneg (mul_nonneg (stableLevyDensity_nonneg _ _ _) (sq_nonneg _))
    have hp : |x| ^ (-(α + 1)) * x ^ 2 = |x| ^ (1 - α) := by
      rw [← sq_abs, ← rpow_two, ← rpow_add (abs_pos.mpr hx)]
      congr 1
      ring
    have hb : (if 0 < x then 1 + β else 1 - β) ≤ 2 := by
      split_ifs <;> linarith [(abs_le.mp h.2.2).1, (abs_le.mp h.2.2).2]
    rw [hnorm, stableLevyDensity_of_ne_zero ⟨h.1, h.2.1⟩ h.2.2 hx, mul_assoc, hp,
      Real.norm_eq_abs, neg_sub]
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (stableLevyDensity_coefficient_pos ⟨h.1, h.2.1⟩).le)
      (rpow_nonneg (abs_nonneg x) (1 - α))]
  · simp [IntegrableOn, stableLevyMeasure_eq_zero_of_not h]

/-- The sine-compensated characteristic kernel is absolutely integrable against the stable
Lévy measure, including at shape one and both full-skewness boundaries. -/
theorem integrable_exp_sub_one_sub_sin_stableLevyMeasure (α β t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I) (stableLevyMeasure α β) := by
  have hcont : Continuous (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I) := by fun_prop
  -- On the unit ball, split off the linear exponential term. Both remaining errors
  -- are dominated by the integrable square of the jump size.
  have hsmall : IntegrableOn (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I) (Metric.ball 0 1) (stableLevyMeasure α β) := by
    refine ((integrableOn_sq_stableLevyMeasure α β 1).const_mul
      (t ^ 2 * exp |t| + |t|)).mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxlt : |x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
    have hx1 : |x| ≤ 1 := hxlt.le
    have hrem : ‖Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
        (t * x : ℝ) * Complex.I‖ ≤ (|t| * |x|) ^ 2 * exp (|t| * |x|) := by
      simpa [Finset.sum_range_succ, sub_add_eq_sub_sub, norm_mul, abs_mul] using
        Complex.norm_exp_sub_sum_le_norm_mul_exp ((t * x : ℝ) * Complex.I) 2
    have hsin : |x - sin x| ≤ x ^ 2 := by
      have := abs_sub_sin_le x
      have := mul_le_mul_of_nonneg_left hx1 (sq_nonneg |x|)
      nlinarith [sq_abs x]
    have he : exp (|t| * |x|) ≤ exp |t| :=
      exp_le_exp.mpr (by nlinarith [abs_nonneg t])
    have hsplit : Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
        (t * sin x : ℝ) * Complex.I =
        (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * x : ℝ) * Complex.I) +
          (t * (x - sin x) : ℝ) * Complex.I := by push_cast; ring
    rw [hsplit]
    calc
      _ ≤ ‖Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * x : ℝ) * Complex.I‖ +
          ‖(t * (x - sin x) : ℝ) * Complex.I‖ := norm_add_le _ _
      _ ≤ (|t| * |x|) ^ 2 * exp (|t| * |x|) + |t| * |x - sin x| := by
        simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
        exact add_le_add hrem le_rfl
      _ ≤ (t ^ 2 * exp |t| + |t|) * x ^ 2 := by
        have h₁ := mul_le_mul_of_nonneg_left he (sq_nonneg (|t| * |x|))
        have h₂ := mul_le_mul_of_nonneg_left hsin (abs_nonneg t)
        calc
          _ ≤ (|t| * |x|) ^ 2 * exp |t| + |t| * x ^ 2 := add_le_add h₁ h₂
          _ = _ := by rw [mul_pow, sq_abs, sq_abs]; ring
  -- Outside a smaller ball, the Lévy measure is finite and the kernel is bounded.
  -- These two regions overlap and cover the line.
  have htail : IntegrableOn (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I) {x | (1 : ℝ) / 2 < |x|} (stableLevyMeasure α β) := by
    have := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (α := α) (β := β)
      (by norm_num : (0 : ℝ) < 1 / 2)
    apply Integrable.of_bound hcont.aestronglyMeasurable.restrict (2 + |t|)
    apply ae_of_all
    intro x
    calc
      _ ≤ ‖Complex.exp ((t * x : ℝ) * Complex.I)‖ + ‖(1 : ℂ)‖ +
          ‖(t * sin x : ℝ) * Complex.I‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = 2 + |t| * |sin x| := by
        simp only [Complex.norm_exp_ofReal_mul_I, norm_one, norm_mul, Complex.norm_real,
          Complex.norm_I, mul_one, Real.norm_eq_abs]
        ring
      _ ≤ 2 + |t| := by nlinarith [abs_sin_le_one x, abs_nonneg t]
  have hcover : Metric.ball (0 : ℝ) 1 ∪ {x | (1 : ℝ) / 2 < |x|} = univ := by
    ext x
    simp only [mem_union, Metric.mem_ball, Real.dist_eq, sub_zero, mem_ofPred_eq,
      mem_univ, iff_true]
    by_cases hx : |x| < 1
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  exact integrableOn_univ.mp (hcover ▸ hsmall.union htail)

/-- Removing a shrinking neighbourhood of zero from the compensated integral recovers the
full integral. No one-sided restriction on the cutoff is needed. -/
theorem tendsto_integral_exp_sub_one_sub_sin_stableLevyMeasure (α β t : ℝ) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℝ | ε < |x|},
      Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I
        ∂stableLevyMeasure α β) (𝓝 0)
      (𝓝 (∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
        (t * sin x : ℝ) * Complex.I ∂stableLevyMeasure α β)) := by
  have hi := integrable_exp_sub_one_sub_sin_stableLevyMeasure α β t
  have hs (ε : ℝ) : MeasurableSet {x : ℝ | ε < |x|} := by measurability
  simp_rw [← integral_indicator (hs _)]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ ↦ ‖Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I‖)
  · exact .of_forall fun ε ↦ hi.aestronglyMeasurable.indicator (hs ε)
  · exact .of_forall fun ε ↦ ae_of_all _ fun x ↦ norm_indicator_le_norm_self _ _
  · exact hi.norm
  · apply ae_of_all
    intro x
    by_cases hx : x = 0
    · simp [hx, indicator_apply]
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_lt_nhds (abs_pos.mpr hx)] with ε hε
      simp only [indicator_apply, mem_ofPred_eq, ite_eq_left hε]

end TauCeti.Probability
