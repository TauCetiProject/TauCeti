/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Logistic.Basic

import TauCeti.Probability.Distributions.Logistic.Transforms
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Moments of the logistic distribution

Every natural moment of a logistic law is integrable. For positive scale `s`, its mean is
the location `m`, its second raw moment is `m ^ 2 + π ^ 2 * s ^ 2 / 3`, and its variance is
`π ^ 2 * s ^ 2 / 3`.

Moment integrability justifies integrating polynomials term by term. The mean and second raw
moment formulas evaluate expectations of affine and quadratic functions, while the variance
formula describes dispersion in terms of the scale.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), ch. 23.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology

namespace TauCeti.Probability

variable {m s : ℝ}

private lemma zero_mem_interior_integrableExpSet_logisticMeasure (hs : 0 < s) :
    0 ∈ interior (integrableExpSet id (logisticMeasure m s)) := by
  rw [integrableExpSet_id_logisticMeasure hs, interior_Ioo]
  exact ⟨div_neg_of_neg_of_pos (by norm_num) hs, one_div_pos.mpr hs⟩

/-- Every natural raw moment of a logistic law is absolutely integrable. This also holds
for the zero measure at a nonpositive scale. -/
theorem integrable_pow_logisticMeasure (m s : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (logisticMeasure m s) := by
  by_cases hs : 0 < s
  · exact integrable_pow_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet_logisticMeasure hs) n
  · simp [logisticMeasure_of_nonpos (le_of_not_gt hs)]

/-- The identity is integrable under a logistic law at every parameter. -/
theorem integrable_id_logisticMeasure (m s : ℝ) : Integrable id (logisticMeasure m s) := by
  simpa [Function.id_def] using integrable_pow_logisticMeasure m s 1

/- The computation uses the established Gamma-product moment-generating function and Mathlib's
Euler reflection formula `Real.Gamma_mul_Gamma_one_sub`. Multiplying the MGF by
`sin (π * s * t)` removes the singularity in the quotient formula at zero. The second and
third derivatives of this identity give the first two moments without differentiating Gamma
twice. -/
private lemma mgf_mul_sin_logisticMeasure (hs : 0 < s) :
    (fun t => mgf id (logisticMeasure m s) t * sin (π * s * t)) =ᶠ[𝓝 0]
      (fun t => exp (m * t) * (π * s * t)) := by
  have hzero : (0 : ℝ) ∈ Ioo (-1 / s) (1 / s) := by
    simpa [integrableExpSet_id_logisticMeasure hs] using
      zero_mem_interior_integrableExpSet_logisticMeasure (m := m) hs
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have hst : s * t ≠ 0 := mul_ne_zero hs.ne' ht0
  have hlo : -1 < s * t := by
    have := (div_lt_iff₀ hs).mp ht.1
    nlinarith
  have hhi : s * t < 1 := by simpa [mul_comm] using (lt_div_iff₀ hs).mp ht.2
  have hsin : sin (π * (s * t)) ≠ 0 := by
    apply mt (sin_eq_zero_iff_of_lt_of_lt (by nlinarith [pi_pos])
      (by nlinarith [pi_pos])).mp
    exact mul_ne_zero pi_ne_zero hst
  rw [mgf_id_logisticMeasure hs ht, add_comm 1 (s * t), Gamma_add_one hst]
  calc
    exp (m * t) * Gamma (1 - s * t) * (s * t * Gamma (s * t)) * sin (π * s * t) =
        exp (m * t) * (s * t) * (Gamma (s * t) * Gamma (1 - s * t)) *
          sin (π * (s * t)) := by simp only [mul_assoc]; ring
    _ = exp (m * t) * (π * s * t) := by
      rw [Gamma_mul_Gamma_one_sub, mul_assoc (exp (m * t) * (s * t)),
        div_mul_cancel₀ _ hsin]
      ring

private lemma logistic_moment_identity (hs : 0 < s) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (∫ x : ℝ, x ^ i ∂logisticMeasure m s) *
        ((π * s) ^ (n - i) * iteratedDeriv (n - i) sin 0)) =
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * m ^ i *
      (π * s * iteratedDeriv (n - i) id 0)) := by
  have hzero := zero_mem_interior_integrableExpSet_logisticMeasure (m := m) hs
  have hlinear (k : ℕ) :
      iteratedDeriv k (fun t : ℝ => π * s * t) 0 = π * s * iteratedDeriv k id 0 :=
    iteratedDeriv_const_mul_field (π * s) id
  have h := (mgf_mul_sin_logisticMeasure (m := m) hs).iteratedDeriv_eq n
  rw [iteratedDeriv_fun_mul (analyticAt_mgf hzero).contDiffAt (by fun_prop),
    iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)] at h
  simpa only [iteratedDeriv_mgf_zero hzero, Pi.pow_apply, id_eq,
    iteratedDeriv_comp_const_mul contDiff_sin, iteratedDeriv_exp_const_mul,
    hlinear, mul_zero, exp_zero, mul_one, ← mul_assoc] using h

/-- The mean of a positive-scale logistic law is its location. -/
@[simp]
theorem integral_id_logisticMeasure (hs : 0 < s) (m : ℝ) :
    ∫ x, x ∂logisticMeasure m s = m := by
  have h := logistic_moment_identity (m := m) hs 2
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos,
    iteratedDeriv_zero] at h
  exact h.resolve_right hs.ne'

/-- The second raw moment of a positive-scale logistic law is its squared location
plus `π²s²/3`. -/
@[simp]
theorem integral_sq_logisticMeasure (hs : 0 < s) (m : ℝ) :
    ∫ x, x ^ 2 ∂logisticMeasure m s = m ^ 2 + π ^ 2 * s ^ 2 / 3 := by
  have := isProbabilityMeasure_logisticMeasure hs m
  have h := logistic_moment_identity (m := m) hs 3
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos,
    iteratedDeriv_zero] at h
  nlinarith [pi_pos, mul_pos pi_pos hs]

/-- The variance of a positive-scale logistic law is `π²s²/3`. -/
@[simp]
theorem variance_id_logisticMeasure (hs : 0 < s) (m : ℝ) :
    variance id (logisticMeasure m s) = π ^ 2 * s ^ 2 / 3 := by
  have := isProbabilityMeasure_logisticMeasure hs m
  have hmem := memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_logisticMeasure (m := m) hs) 2
  simp only [variance_eq_sub hmem, Pi.pow_apply, id_eq, integral_id_logisticMeasure hs,
    integral_sq_logisticMeasure hs]
  ring

end TauCeti.Probability
