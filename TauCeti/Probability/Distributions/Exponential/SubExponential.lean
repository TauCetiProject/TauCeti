/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Moments.SubExponential
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Exponential variables are sub-exponential

The standard exponential law has centered MGF `exp (-t) / (1 - t)` for `t < 1`. Its
centered exponential moment is integrable exactly for `t < 1`; in particular it is not
sub-Gaussian. Nevertheless, it is sub-exponential with parameter `2`.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

/-- The centered standard exponential has an exponential moment exactly below the rate. -/
theorem integrable_exp_mul_centered_expMeasure_one_iff (t : ℝ) :
    Integrable (fun x : ℝ => exp (t * (x - 1))) (expMeasure 1) ↔ t < 1 := by
  have hfun : (fun x : ℝ => exp (t * (x - 1))) =
      fun x => exp (-t) * exp (t * x) := by
    funext x
    rw [← exp_add]
    congr 1
    ring
  rw [hfun, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (exp_ne_zero _)),
    integrable_exp_mul_expMeasure_iff one_pos]

/-- The centered standard exponential has no finite exponential moment at `t = 1`. -/
theorem not_integrable_exp_centered_expMeasure_one :
    ¬ Integrable (fun x : ℝ => exp (x - 1)) (expMeasure 1) := by
  simpa using (integrable_exp_mul_centered_expMeasure_one_iff 1).not.mpr (by norm_num)

/-- The centered MGF of the standard exponential law, on its integrability domain. -/
theorem mgf_centered_expMeasure_one {t : ℝ} (ht : t < 1) :
    mgf (fun x : ℝ => x - 1) (expMeasure 1) t = exp (-t) / (1 - t) := by
  calc
    mgf (fun x : ℝ => x - 1) (expMeasure 1) t =
        mgf id (expMeasure 1) t * exp (t * (-1)) := by
      simpa only [sub_eq_add_neg, id_eq] using
        (mgf_add_const (X := id) (μ := expMeasure 1) (t := t) (-1))
    _ = exp (-t) / (1 - t) := by
      rw [mgf_id_expMeasure one_pos ht]
      simp only [one_div, mul_neg, mul_one]
      ring

private theorem centered_exp_bound {t : ℝ} (ht : |t| ≤ 1 / 2) :
    exp (-t) / (1 - t) ≤ exp (2 * t ^ 2) := by
  have hpos : 0 < 1 - t := by
    have := (abs_le.mp ht).2
    linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hbound : -t - log (1 - t) ≤ 2 * t ^ 2 := by
    have hfrac : (1 - t)⁻¹ - 1 - t = t ^ 2 / (1 - t) := by
      field_simp
      ring
    have hdiv : t ^ 2 / (1 - t) ≤ 2 * t ^ 2 := by
      rw [div_le_iff₀ hpos]
      have := (abs_le.mp ht).2
      nlinarith [sq_nonneg t]
    linarith
  calc
    exp (-t) / (1 - t) = exp (-t - log (1 - t)) := by
      rw [exp_sub, exp_log hpos]
    _ ≤ exp (2 * t ^ 2) := exp_le_exp.mpr hbound

/-- A quadratic MGF bound on the symmetric interval `[-1/2, 1/2]`. -/
theorem mgf_centered_expMeasure_one_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    mgf (fun x : ℝ => x - 1) (expMeasure 1) t ≤ exp (2 * t ^ 2) := by
  have ht1 : t < 1 := by linarith [(abs_le.mp ht).2]
  rw [mgf_centered_expMeasure_one ht1]
  exact centered_exp_bound ht

local instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- The standard exponential law is sub-exponential with parameter `2`. -/
theorem hasSubexponentialMGF_expMeasure_one :
    HasSubexponentialMGF (fun x : ℝ => x) 2 (expMeasure 1) := by
  have hmean : ∫ x : ℝ, x ∂expMeasure 1 = 1 := by
    simp [integral_id_expMeasure one_pos]
  refine ⟨by norm_num, (memLp_id_expMeasure (r := 1) one_pos).integrable (by norm_num), ?_, ?_⟩
  · intro t ht
    rw [hmean]
    apply (integrable_exp_mul_centered_expMeasure_one_iff t).2
    have ht' : |t| ≤ (1 : ℝ) / 2 := by simpa using ht
    linarith [(abs_le.mp ht').2]
  · intro t ht
    rw [hmean]
    have ht' : |t| ≤ (1 : ℝ) / 2 := by simpa using ht
    exact (mgf_centered_expMeasure_one_le ht').trans
      (exp_le_exp.mpr (by nlinarith [sq_nonneg t]))

/-- The standard exponential law is not sub-Gaussian for any variance proxy. -/
theorem not_hasSubgaussianMGF_expMeasure_one (c : ℝ≥0) :
    ¬ HasSubgaussianMGF (fun x : ℝ => x) c (expMeasure 1) := by
  intro h
  have hi := h.integrable_exp_mul 1
  have : (1 : ℝ) < 1 :=
    (integrable_exp_mul_expMeasure_iff (r := 1) (t := 1) one_pos).mp (by simpa using hi)
  exact lt_irrefl _ this

/-- Centering the standard exponential law does not make it sub-Gaussian. -/
theorem not_hasSubgaussianMGF_centered_expMeasure_one (c : ℝ≥0) :
    ¬ HasSubgaussianMGF (fun x : ℝ => x - 1) c (expMeasure 1) := by
  intro h
  have hi := h.integrable_exp_mul 1
  have : (1 : ℝ) < 1 :=
    (integrable_exp_mul_centered_expMeasure_one_iff 1).mp (by simpa using hi)
  exact lt_irrefl _ this

end TauCeti.Probability
