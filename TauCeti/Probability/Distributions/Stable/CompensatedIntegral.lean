/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.SmallJump.Basic
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Integrability of the compensated stable characteristic kernel

For non-Gaussian stable parameters, the Lévy measure has infinite mass near zero. Its
second moment on a bounded neighbourhood of zero is nevertheless finite. Consequently the
compensation
`exp (t * x * I) - 1 - t * sin x * I` is absolutely integrable: it vanishes quadratically
at zero and is bounded outside a neighbourhood of zero. The same argument applies along any
unit complex direction `u` in place of `I` once the exponential term is essentially bounded,
which covers the real kernel `exp (t * x) - 1 - t * sin x` on a half-line carrying the Lévy
measure. The cutoff integrals converge to this integral,
which is the analytic input to compensated compound Poisson approximations.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology

namespace TauCeti.Probability

/-- On the unit ball the compensated kernel is integrable: its error is dominated by the
integrable square of the jump size. -/
private theorem integrableOn_ball_cexp_sub_one_sub_sin_stableLevyMeasure
    {α β t : ℝ} {u : ℂ} (hu : ‖u‖ = 1) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * u) - 1 -
      (t * sin x : ℝ) * u) (Metric.ball 0 1) (stableLevyMeasure α β) := by
  have hcont : Continuous (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * u) - 1 -
      (t * sin x : ℝ) * u) := by fun_prop
  refine ((integrableOn_sq_stableLevyMeasure α β 1).const_mul
    (t ^ 2 * exp |t| + |t|)).mono' hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hxlt : |x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hx1 : |x| ≤ 1 := hxlt.le
  have hrem : ‖Complex.exp ((t * x : ℝ) * u) - 1 - (t * x : ℝ) * u‖ ≤
      (|t| * |x|) ^ 2 * exp (|t| * |x|) := by
    simpa [Finset.sum_range_succ, sub_add_eq_sub_sub, norm_mul, abs_mul, hu] using
      Complex.norm_exp_sub_sum_le_norm_mul_exp ((t * x : ℝ) * u) 2
  have hsin : |x - sin x| ≤ x ^ 2 := by
    have := abs_sub_sin_le x
    have := mul_le_mul_of_nonneg_left hx1 (sq_nonneg |x|)
    nlinarith [sq_abs x]
  have he : exp (|t| * |x|) ≤ exp |t| :=
    exp_le_exp.mpr (by nlinarith [abs_nonneg t])
  have hsplit : Complex.exp ((t * x : ℝ) * u) - 1 - (t * sin x : ℝ) * u =
      (Complex.exp ((t * x : ℝ) * u) - 1 - (t * x : ℝ) * u) +
        (t * (x - sin x) : ℝ) * u := by push_cast; ring
  rw [hsplit]
  calc
    _ ≤ ‖Complex.exp ((t * x : ℝ) * u) - 1 - (t * x : ℝ) * u‖ +
        ‖(t * (x - sin x) : ℝ) * u‖ := norm_add_le _ _
    _ ≤ (|t| * |x|) ^ 2 * exp (|t| * |x|) + |t| * |x - sin x| := by
      simp only [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_eq_abs]
      exact add_le_add hrem le_rfl
    _ ≤ (t ^ 2 * exp |t| + |t|) * x ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_left he (sq_nonneg (|t| * |x|))
      have h₂ := mul_le_mul_of_nonneg_left hsin (abs_nonneg t)
      calc
        _ ≤ (|t| * |x|) ^ 2 * exp |t| + |t| * x ^ 2 := add_le_add h₁ h₂
        _ = _ := by rw [mul_pow, sq_abs, sq_abs]; ring

/-- Away from zero the Lévy measure is finite and the compensated kernel is essentially
bounded. -/
private theorem integrableOn_abs_gt_cexp_sub_one_sub_sin_stableLevyMeasure
    {α β t C : ℝ} {u : ℂ} (hu : ‖u‖ = 1)
    (hexp : ∀ᵐ x ∂stableLevyMeasure α β, ‖Complex.exp ((t * x : ℝ) * u)‖ ≤ C) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * u) - 1 -
    (t * sin x : ℝ) * u) {x | (1 : ℝ) / 2 < |x|} (stableLevyMeasure α β) := by
  have hcont : Continuous (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * u) - 1 -
      (t * sin x : ℝ) * u) := by fun_prop
  have := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (α := α) (β := β)
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine Integrable.of_bound hcont.aestronglyMeasurable.restrict (C + 1 + |t|) ?_
  filter_upwards [ae_restrict_of_ae hexp] with x hx
  calc
    _ ≤ ‖Complex.exp ((t * x : ℝ) * u)‖ + ‖(1 : ℂ)‖ + ‖(t * sin x : ℝ) * u‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖Complex.exp ((t * x : ℝ) * u)‖ + 1 + |t| * |sin x| := by
      simp only [norm_one, norm_mul, Complex.norm_real, hu, mul_one, Real.norm_eq_abs]
    _ ≤ C + 1 + |t| := by nlinarith [abs_sin_le_one x, abs_nonneg t]

/-- Along a unit complex direction `u`, the sine-compensated exponential kernel
`exp (t * x * u) - 1 - t * sin x * u` is absolutely integrable against the stable Lévy measure
whenever its exponential term is essentially bounded. The direction `u = I` gives the
characteristic kernel and `u = 1` the real exponential kernel. -/
theorem integrable_cexp_mul_sub_one_sub_mul_sin_mul_stableLevyMeasure {α β t C : ℝ} {u : ℂ}
    (hu : ‖u‖ = 1)
    (hexp : ∀ᵐ x ∂stableLevyMeasure α β, ‖Complex.exp ((t * x : ℝ) * u)‖ ≤ C) :
    Integrable (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * u) - 1 - (t * sin x : ℝ) * u)
      (stableLevyMeasure α β) := by
  have hsmall :=
    integrableOn_ball_cexp_sub_one_sub_sin_stableLevyMeasure (α := α) (β := β) (t := t) hu
  have htail := integrableOn_abs_gt_cexp_sub_one_sub_sin_stableLevyMeasure hu hexp
  have hcover : Metric.ball (0 : ℝ) 1 ∪ {x | (1 : ℝ) / 2 < |x|} = univ := by
    ext x
    simp only [mem_union, Metric.mem_ball, Real.dist_eq, sub_zero, mem_ofPred_eq,
      mem_univ, iff_true]
    by_cases hx : |x| < 1
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  exact integrableOn_univ.mp (hcover ▸ hsmall.union htail)

/-- The sine-compensated characteristic kernel is absolutely integrable against the stable
Lévy measure, including at shape one and both full-skewness boundaries. -/
theorem integrable_exp_sub_one_sub_sin_stableLevyMeasure (α β t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I) (stableLevyMeasure α β) :=
  integrable_cexp_mul_sub_one_sub_mul_sin_mul_stableLevyMeasure Complex.norm_I
    (ae_of_all _ fun _ ↦ (Complex.norm_exp_ofReal_mul_I _).le)

/-- If `t * x ≤ 0` for almost every jump `x` of the stable Lévy measure, then the real
compensated kernel `exp (t * x) - 1 - t * sin x` is integrable against the Lévy measure. -/
theorem integrable_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure {α β t : ℝ}
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Integrable (fun x : ℝ ↦ exp (t * x) - 1 - t * sin x) (stableLevyMeasure α β) := by
  -- This is the real part of the complex kernel along the direction `1`.
  have h := integrable_cexp_mul_sub_one_sub_mul_sin_mul_stableLevyMeasure (C := 1) norm_one
    (ht.mono fun x hx ↦ by
      rw [mul_one, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
      exact exp_le_one_iff.mpr hx)
  simpa only [mul_one, RCLike.re_to_complex, Complex.sub_re, Complex.exp_ofReal_re,
    Complex.one_re, Complex.ofReal_re] using h.re

/-- Removing a shrinking neighbourhood of zero from the compensated integral recovers the
full integral. No one-sided restriction on the cutoff is needed. -/
theorem tendsto_integral_exp_sub_one_sub_sin_stableLevyMeasure (α β t : ℝ) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℝ | ε < |x|},
      Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I
        ∂stableLevyMeasure α β) (𝓝 0)
      (𝓝 (∫ x : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
        (t * sin x : ℝ) * Complex.I ∂stableLevyMeasure α β)) := by
  exact tendsto_integral_abs_gt
    (integrable_exp_sub_one_sub_sin_stableLevyMeasure α β t) (by simp)

/-- If `t * x ≤ 0` for almost every jump, removing a shrinking neighbourhood of zero
recovers the real compensated Lévy integral. No one-sided restriction on the cutoff is needed. -/
theorem tendsto_integral_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure {α β t : ℝ}
    (ht : ∀ᵐ x ∂stableLevyMeasure α β, t * x ≤ 0) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℝ | ε < |x|},
      exp (t * x) - 1 - t * sin x ∂stableLevyMeasure α β) (𝓝 0)
      (𝓝 (∫ x, exp (t * x) - 1 - t * sin x ∂stableLevyMeasure α β)) := by
  exact tendsto_integral_abs_gt
    (integrable_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure ht) (by simp)

end TauCeti.Probability
