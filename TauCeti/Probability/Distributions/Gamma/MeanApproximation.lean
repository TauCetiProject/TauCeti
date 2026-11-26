/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Approximating a Lipschitz test by its Gamma average

The error of replacing the expectation of a Lipschitz function under a Gamma law by its
value at the mean is bounded by the Lipschitz constant times the standard deviation.
This compares the function pointwise to its smoothed value, as needed in Laplace inversion.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- A Gamma average differs from evaluation at its mean by at most the Lipschitz constant
times `√a / r`, the standard deviation of the law with shape `a` and rate `r`. -/
theorem norm_integral_gammaMeasure_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    {f : ℝ → E} {L : ℝ≥0} (hf : LipschitzOnWith L f (Ioi 0)) :
    ‖(∫ x, f x ∂gammaMeasure a r) - f (a / r)‖ ≤ L * (Real.sqrt a / r) := by
  let μ := gammaMeasure a r
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure ha hr
  have hpos : ∀ᵐ x ∂μ, x ∈ Ioi (0 : ℝ) := ae_pos_gammaMeasure a r
  have hmean : ∫ x, id x ∂μ = a / r := integral_id_gammaMeasure ha hr
  have hcenter : MemLp (fun x : ℝ ↦ x - a / r) 2 μ :=
    (memLp_id_gammaMeasure ha hr).sub (memLp_const _)
  have hLip : ∀ᵐ x ∂μ, ‖f x - f (a / r)‖ ≤ (L : ℝ) * ‖x - a / r‖ :=
    hpos.mono fun {x} hx ↦ by
      simpa only [dist_eq_norm] using hf.dist_le_mul x hx (a / r) (div_pos ha hr)
  have hmeas : AEStronglyMeasurable f μ := by
    have hm := hf.continuousOn.aestronglyMeasurable (μ := μ) measurableSet_Ioi
    rwa [Measure.restrict_eq_self_of_ae_mem hpos] at hm
  have hbound := (hcenter.integrable (by norm_num)).norm.const_mul (L : ℝ)
  have hdiff := hbound.mono' (hmeas.sub aestronglyMeasurable_const) hLip
  have hfi : Integrable f μ := by
    simpa using hdiff.add (integrable_const (f (a / r)))
  have hsub : (∫ x, f x - f (a / r) ∂μ) = (∫ x, f x ∂μ) - f (a / r) := by
    simp [integral_sub hfi (integrable_const (f (a / r)))]
  rw [← hsub]
  have hmoment : ∫ x, ‖x - a / r‖ ^ 2 ∂μ = a / r ^ 2 := by
    rw [← variance_id_gammaMeasure ha hr, variance_eq_integral (μ := μ)
      measurable_id.aemeasurable, hmean]
    simp only [id_eq, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ∫ x, ‖f x - f (a / r)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (L : ℝ) * ‖x - a / r‖ ∂μ := integral_mono_ae hdiff.norm hbound hLip
    _ ≤ _ := by
      have hsd : Real.sqrt (a / r ^ 2) = Real.sqrt a / r := by
        rw [Real.sqrt_div ha.le, Real.sqrt_sq hr.le]
      rw [integral_const_mul, ← hsd]
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      rw [← hmoment]
      simpa using hcenter.norm.integrable_sq.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul
        (μ := μ) (f := fun x : ℝ ↦ x - a / r) (k := 1) (by simp)

end TauCeti.Probability
