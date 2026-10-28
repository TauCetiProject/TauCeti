/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Exponential moments of noncentral chi-squared laws

For nonnegative degree `k` and noncentrality `l`, the moment-generating function is
`(1 - 2 * t) ^ (-(k / 2)) * exp (l * t / (1 - 2 * t))` below `1 / 2`.
The exponential-integrability domain is exactly this half-line unless both parameters vanish,
when the law is the point mass at zero and every exponential moment exists.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {k t : ℝ} {l : ℝ≥0}

private theorem lintegral_exp_mul_noncentralChiSquaredMeasure (hk : 0 ≤ k)
    (l : ℝ≥0) (ht : t < 2⁻¹) :
    ∫⁻ x, ENNReal.ofReal (exp (t * x)) ∂noncentralChiSquaredMeasure k l =
      ENNReal.ofReal ((1 - 2 * t) ^ (-(k / 2)) * exp (l * t / (1 - 2 * t))) := by
  have hb : 0 < 1 - 2 * t := by linarith
  have hcomponent (n : ℕ) :
      ∫⁻ x, ENNReal.ofReal (exp (t * x)) ∂chiSquaredMeasure (k + 2 * n) =
        ENNReal.ofReal ((1 - 2 * t) ^ (-(k / 2)) * ((1 - 2 * t)⁻¹) ^ n) := by
    have hdeg : 0 ≤ k + 2 * (n : ℝ) := by positivity
    let := isProbabilityMeasure_chiSquaredMeasure hdeg
    have hmgf : (∫ x, exp (t * x) ∂chiSquaredMeasure (k + 2 * n)) =
        (1 - 2 * t) ^ (-((k + 2 * n) / 2)) := by
      simpa only [mgf, id_eq] using mgf_id_chiSquaredMeasure hdeg ht
    have hi : Integrable (fun x : ℝ ↦ exp (t * x)) (chiSquaredMeasure (k + 2 * n)) := by
      apply mgf_pos_iff.mp
      rw [mgf, hmgf]
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ (exp_pos _).le)]
    rw [hmgf]
    congr 1
    have hexponent : -((k + 2 * (n : ℝ)) / 2) = -(k / 2) + (-1) * n := by ring
    rw [hexponent,
      Real.rpow_add hb, Real.rpow_mul hb.le, Real.rpow_natCast, Real.rpow_neg_one]
  rw [noncentralChiSquaredMeasure_of_nonneg hk,
    Measure.lintegral_bind (.of_discrete) (by fun_prop)]
  simp_rw [hcomponent, ENNReal.ofReal_mul (Real.rpow_pos_of_pos hb _).le]
  have hparam : ((1 - 2 * t)⁻¹ - 1) * ((l / 2 : ℝ≥0) : ℝ) =
      l * t / (1 - 2 * t) := by
    push_cast
    field_simp
    ring
  rw [lintegral_const_mul _ (by fun_prop),
    lintegral_ofReal_poissonMeasure (by intro n; positivity) (l / 2)
      (hasSum_pow_poissonMeasure (l / 2) ((1 - 2 * t)⁻¹)), hparam]

/-- Every exponential moment below `1 / 2` exists, including at the double-zero Dirac boundary. -/
theorem integrable_exp_mul_noncentralChiSquaredMeasure (hk : 0 ≤ k)
    (l : ℝ≥0) (ht : t < 2⁻¹) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (noncentralChiSquaredMeasure k l) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (exp_pos _).le),
    lintegral_exp_mul_noncentralChiSquaredMeasure hk l ht]
  exact ENNReal.ofReal_lt_top

/-- The noncentral chi-squared mgf, valid below `1 / 2` even when the law is Dirac. -/
@[simp]
theorem mgf_id_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) (ht : t < 2⁻¹) :
    mgf id (noncentralChiSquaredMeasure k l) t =
      (1 - 2 * t) ^ (-(k / 2)) * exp (l * t / (1 - 2 * t)) := by
  have h := lintegral_exp_mul_noncentralChiSquaredMeasure hk l ht
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_noncentralChiSquaredMeasure hk l ht)
    (ae_of_all _ fun _ ↦ (exp_pos _).le)] at h
  have hreal := congrArg ENNReal.toReal h
  have hb : 0 < 1 - 2 * t := by linarith
  have hnonneg : 0 ≤ (1 - 2 * t) ^ (-(k / 2)) * exp (l * t / (1 - 2 * t)) :=
    mul_nonneg (Real.rpow_pos_of_pos hb _).le (exp_pos _).le
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ (exp_pos _).le),
    ENNReal.toReal_ofReal hnonneg, mgf, id_eq] using hreal

/-- The simplified noncentral chi-squared cumulant-generating function. -/
@[simp]
theorem cgf_id_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) (ht : t < 2⁻¹) :
    cgf id (noncentralChiSquaredMeasure k l) t =
      -(k / 2) * log (1 - 2 * t) + l * t / (1 - 2 * t) := by
  have hb : 0 < 1 - 2 * t := by linarith
  rw [cgf, mgf_id_noncentralChiSquaredMeasure hk l ht,
    log_mul (Real.rpow_pos_of_pos hb _).ne' (exp_pos _).ne', log_rpow hb, log_exp]

/-- At or above `1 / 2`, the exponential integrand is not integrable under any valid
noncentral chi-squared law other than the double-zero Dirac law. -/
theorem not_integrable_exp_mul_noncentralChiSquaredMeasure (hk : 0 ≤ k)
    (hne : k ≠ 0 ∨ l ≠ 0) (ht : 2⁻¹ ≤ t) :
    ¬ Integrable (fun x : ℝ ↦ exp (t * x)) (noncentralChiSquaredMeasure k l) := by
  obtain ⟨n, hdeg, hw, hle⟩ :=
    exists_smul_chiSquaredMeasure_le_noncentralChiSquaredMeasure hk hne
  intro hi
  have hc := (integrable_smul_measure hw (measure_ne_top _ _)).mp (hi.mono_measure hle)
  have hmem : t ∈ integrableExpSet id (chiSquaredMeasure (k + 2 * n)) := by
    simpa only [integrableExpSet, mem_ofPred_eq, id_eq] using hc
  rw [integrableExpSet_id_chiSquaredMeasure hdeg] at hmem
  exact (not_lt.mpr ht) (by simpa only [mem_Iio, one_div] using hmem)

/-- The exact exponential domain is all of `ℝ` at the double-zero boundary and `(-∞, 1/2)`
at every other valid degree and noncentrality. -/
@[simp]
theorem integrableExpSet_id_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) :
    integrableExpSet id (noncentralChiSquaredMeasure k l) =
      if k = 0 ∧ l = 0 then univ else Iio (1 / 2) := by
  split_ifs with hzero
  · rcases hzero with ⟨rfl, rfl⟩
    simp
  · ext t
    simp only [integrableExpSet, mem_ofPred_eq, id_eq, mem_Iio]
    constructor
    · intro ht
      exact lt_of_not_ge fun ht' ↦
        not_integrable_exp_mul_noncentralChiSquaredMeasure hk (not_and_or.mp hzero)
          (by simpa only [one_div] using ht') ht
    · intro ht
      exact integrable_exp_mul_noncentralChiSquaredMeasure hk l
        (by simpa only [mem_Iio, one_div] using ht)

end TauCeti.Probability
