/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Lipschitz tests of a Gamma law

The average of a Lipschitz test differs from its value at the mean by at most the Lipschitz
constant times the standard deviation. For a Gamma law of shape `a` and rate `r`, this gives
the error bound `K * √a / r` used to approximate a function by normalized Laplace coefficients.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- Averaging a function that is `K`-Lipschitz on the positive ray against a Gamma law changes
its value at the mean `a / r` by at most `K * √a / r`. -/
theorem norm_integral_gammaMeasure_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Ioi 0)) :
    ‖(∫ x, f x ∂gammaMeasure a r) - f (a / r)‖ ≤ (K : ℝ) * √a / r := by
  set μ := gammaMeasure a r
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure ha hr
  have hμ : ∀ᵐ x ∂μ, x ∈ Ioi (0 : ℝ) := ae_pos_gammaMeasure a r
  have hmeas : AEStronglyMeasurable f μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμ]
    exact hf.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hX : MemLp id 2 μ := memLp_id_gammaMeasure ha hr
  have hY : MemLp (fun x ↦ x - a / r) 2 μ := hX.sub (memLp_const _)
  have hbound : ∀ᵐ x ∂μ, ‖f x - f (a / r)‖ ≤ (K : ℝ) * ‖x - a / r‖ := by
    filter_upwards [hμ] with x hx
    simpa only [dist_eq_norm] using hf.dist_le_mul x hx (a / r) (div_pos ha hr)
  have hdom := hY.norm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdom' := hdom.const_mul (K : ℝ)
  have hdiff : Integrable (fun x ↦ f x - f (a / r)) μ :=
    hdom'.mono' (hmeas.sub aestronglyMeasurable_const) hbound
  have hfInt : Integrable f μ := (hdiff.add (integrable_const (f (a / r)))).congr
    (.of_forall fun _ ↦ sub_add_cancel _ _)
  have hmean : (∫ x, x ∂μ) = a / r := integral_id_gammaMeasure ha hr
  have hvar : (∫ x, ‖x - a / r‖ ^ 2 ∂μ) = a / r ^ 2 := by
    simpa only [id_eq, Real.norm_eq_abs, sq_abs, hmean] using
      (variance_eq_integral hX.aemeasurable).symm.trans (variance_id_gammaMeasure ha hr)
  have hdev : (∫ x, ‖x - a / r‖ ∂μ) ≤ √a / r := by
    have hCS := hY.norm.integrable_sq.abs_integral_le_sqrt_integral_sq (μ := μ) (by simp)
    rw [abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), hvar, Real.sqrt_div ha.le,
      Real.sqrt_sq hr.le] at hCS
    exact hCS
  calc
    _ = ‖∫ x, f x - f (a / r) ∂μ‖ := by
      rw [integral_sub hfInt (integrable_const _), integral_const]
      simp
    _ ≤ ∫ x, (K : ℝ) * ‖x - a / r‖ ∂μ := norm_integral_le_of_norm_le hdom' hbound
    _ ≤ _ := by rw [integral_const_mul, mul_div_assoc]; gcongr

end TauCeti.Probability
