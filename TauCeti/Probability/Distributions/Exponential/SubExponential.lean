/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Moments.SubExponential
public import TauCeti.Analysis.SpecialFunctions.Exp.CenteredBound
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Exponential variables are sub-exponential

For a positive rate `r`, the exponential law is sub-exponential with parameter `2 / r`,
but neither it nor its centered version is sub-Gaussian.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

/-- A quadratic MGF bound for `t ≤ r/2`. -/
theorem mgf_centered_expMeasure_le {r t : ℝ} (hr : 0 < r) (ht : t ≤ r / 2) :
    mgf (fun x : ℝ => x - r⁻¹) (expMeasure r) t ≤ exp (2 * (t / r) ^ 2) := by
  have ht1 : t < r := by linarith
  have htr : t / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]
    linarith
  rw [mgf_sub_const_expMeasure hr ht1 r⁻¹]
  simp only [← div_eq_mul_inv]
  have heq : r / (r - t) = 1 / (1 - t / r) := by
    field_simp
  rw [heq]
  simpa [div_eq_mul_inv] using Real.exp_neg_div_one_sub_le htr

/-- Every positive-rate exponential law is sub-exponential with parameter `2 / r`. -/
theorem hasSubexponentialMGF_expMeasure {r : ℝ} (hr : 0 < r) :
    letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
    HasSubexponentialMGF (fun x : ℝ => x) (2 / r) (expMeasure r) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hmean : ∫ x : ℝ, x ∂expMeasure r = r⁻¹ := integral_id_expMeasure hr
  have hparam : 0 < 2 / r := div_pos (by norm_num) hr
  refine ⟨hparam, (memLp_id_expMeasure hr).integrable (by norm_num), ?_, ?_⟩ <;>
    rw [inv_div]
  · intro t ht
    rw [hmean]
    apply (integrable_exp_mul_sub_expMeasure_iff hr t r⁻¹).2
    linarith [(abs_le.mp ht).2]
  · intro t ht
    rw [hmean]
    refine (mgf_centered_expMeasure_le hr (abs_le.mp ht).2).trans (exp_le_exp.mpr ?_)
    have : 0 ≤ (t / r) ^ 2 := sq_nonneg _
    have heq : (2 / r) ^ 2 * t ^ 2 = 4 * (t / r) ^ 2 := by ring
    rw [heq]
    linarith

/-- No constant shift of a positive-rate exponential law is sub-Gaussian. -/
theorem not_hasSubgaussianMGF_sub_expMeasure {r : ℝ} (hr : 0 < r) (a : ℝ) (c : ℝ≥0) :
    ¬ HasSubgaussianMGF (fun x : ℝ => x - a) c (expMeasure r) := by
  intro h
  have hi := h.integrable_exp_mul r
  exact lt_irrefl r ((integrable_exp_mul_sub_expMeasure_iff hr r a).mp (by simpa using hi))

/-- No positive-rate exponential law is sub-Gaussian. -/
theorem not_hasSubgaussianMGF_expMeasure {r : ℝ} (hr : 0 < r) (c : ℝ≥0) :
    ¬ HasSubgaussianMGF (fun x : ℝ => x) c (expMeasure r) := by
  simpa using not_hasSubgaussianMGF_sub_expMeasure hr 0 c

end TauCeti.Probability
