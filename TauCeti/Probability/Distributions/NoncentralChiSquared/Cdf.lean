/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Cumulative probabilities of noncentral chi-squared laws

The cdf is an absolutely convergent Poisson-weighted series of central chi-squared cdfs.
At positive degree these are regularized incomplete Gamma functions. At degree zero the
zero-count component instead contributes the atom at the origin; it must not be replaced by
a Gamma cdf with zero shape.

Every valid law except the double-zero Dirac law has a strictly increasing cdf on `[0, ∞)`
and positive mass above every finite cutoff. These facts characterize the positive quantiles.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {k x : ℝ} {l : ℝ≥0}

/-- The Poisson-weighted central cdfs sum to the noncentral cdf. The nonnegative terms make
this an absolutely convergent series, also at degree zero. -/
theorem hasSum_cdf_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) (x : ℝ) :
    HasSum (fun n : ℕ ↦
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ n / n.factorial) *
        cdf (chiSquaredMeasure (k + 2 * n)) x)
      (cdf (noncentralChiSquaredMeasure k l) x) := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  have hsum := (ENNReal.summable.hasSum_iff.mpr
    (noncentralChiSquaredMeasure_apply hk l (Iic x)).symm).toReal (measure_ne_top _ _)
  rw [← measureReal_def, ← cdf_eq_real] at hsum
  convert hsum using 1
  funext n
  have := isProbabilityMeasure_chiSquaredMeasure (k := k + 2 * n) (by positivity)
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
    ← cdf_eq_real, poissonMeasure_real_singleton]
  simp [NNReal.coe_div, neg_div]

/-- At positive degree the cdf is the Poisson series of regularized Gamma functions, with
the functions already clamped below the support. -/
theorem cdf_noncentralChiSquaredMeasure_eq (hk : 0 < k) (l : ℝ≥0) (x : ℝ) :
    cdf (noncentralChiSquaredMeasure k l) x = ∑' n : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ n / n.factorial) *
        regularizedGamma ((k + 2 * n) / 2) (x / 2) := by
  rw [← (hasSum_cdf_noncentralChiSquaredMeasure hk.le l x).tsum_eq]
  exact tsum_congr fun n ↦ by rw [cdf_chiSquaredMeasure_eq (by positivity)]

/-- At degree zero and a nonnegative cutoff, split off the atom before summing the
positive-degree Gamma cdfs. This includes the double-zero Dirac law. -/
theorem cdf_noncentralChiSquaredMeasure_zero_degree (l : ℝ≥0) (hx : 0 ≤ x) :
    cdf (noncentralChiSquaredMeasure 0 l) x = exp (-(l : ℝ) / 2) + ∑' n : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ (n + 1) / (n + 1).factorial) *
        regularizedGamma ((n : ℝ) + 1) (x / 2) := by
  rw [← (hasSum_cdf_noncentralChiSquaredMeasure (k := 0) (by norm_num) l x).tsum_eq,
    (hasSum_cdf_noncentralChiSquaredMeasure (k := 0) (by norm_num) l x).summable.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
    div_one, cdf_chiSquaredMeasure_zero, ite_eq_left hx]
  congr 1
  apply tsum_congr
  intro n
  rw [cdf_chiSquaredMeasure_eq (by positivity)]
  congr 2
  push_cast
  ring

/-- No noncentral chi-squared law of nonnegative degree has mass below zero. -/
@[simp]
theorem cdf_noncentralChiSquaredMeasure_of_neg (hk : 0 ≤ k) (l : ℝ≥0) (hx : x < 0) :
    cdf (noncentralChiSquaredMeasure k l) x = 0 := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  have hnull : noncentralChiSquaredMeasure k l (Iic x) = 0 :=
    measure_eq_zero_iff_ae_notMem.2
      ((ae_nonneg_noncentralChiSquaredMeasure k l).mono fun y hy ↦
        not_le.mpr (hx.trans_le hy))
  rw [cdf_eq_real, measureReal_def, hnull, ENNReal.toReal_zero]

/-- The cdf at zero is zero at positive degree and is the Poisson zero-count mass at
degree zero. -/
@[simp]
theorem cdf_noncentralChiSquaredMeasure_zero (hk : 0 ≤ k) (l : ℝ≥0) :
    cdf (noncentralChiSquaredMeasure k l) 0 = if k = 0 then exp (-(l : ℝ) / 2) else 0 := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  have heq : (Iic 0 : Set ℝ) =ᵐ[noncentralChiSquaredMeasure k l] {0} := by
    filter_upwards [ae_nonneg_noncentralChiSquaredMeasure k l] with y hy
    simp only [mem_Iic, mem_singleton_iff]
    exact propext ⟨fun h ↦ le_antisymm h hy, fun h ↦ h.le⟩
  rw [cdf_eq_real, measureReal_congr heq, measureReal_def]
  by_cases hk0 : k = 0
  · simp [hk0, noncentralChiSquaredMeasure_zero_degree_mass, le_of_lt (exp_pos _)]
  · have := nullSingletonClass_noncentralChiSquaredMeasure (lt_of_le_of_ne hk (Ne.symm hk0)) l
    simp [hk0]

/-- Away from the double-zero Dirac boundary, the cdf is strictly increasing on the
nonnegative half-line, including from its possible atom at zero. -/
theorem strictMonoOn_cdf_noncentralChiSquaredMeasure (hk : 0 ≤ k)
    (h : k ≠ 0 ∨ l ≠ 0) :
    StrictMonoOn (cdf (noncentralChiSquaredMeasure k l)) (Ici 0) := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  intro a ha b _ hab
  rw [← Measure.measure_Ioc_pos_iff_cdf_lt]
  have hsupport : (a + b) / 2 ∈ (noncentralChiSquaredMeasure k l).support := by
    rw [support_noncentralChiSquaredMeasure, ite_eq_right (not_lt.mpr hk),
      ite_eq_right (not_and_or.mpr h)]
    simp only [mem_Ici] at ha ⊢
    linarith
  exact lt_of_lt_of_le
    ((Measure.mem_support_iff_forall _).mp hsupport (Ioo a b)
      (Ioo_mem_nhds (by linarith) (by linarith))) (measure_mono Ioo_subset_Ioc_self)

/-- Every finite cutoff leaves positive upper-tail probability, except at the double-zero
Dirac boundary. -/
theorem cdf_noncentralChiSquaredMeasure_lt_one (hk : 0 ≤ k) (h : k ≠ 0 ∨ l ≠ 0) (x : ℝ) :
    cdf (noncentralChiSquaredMeasure k l) x < 1 := by
  have hm := strictMonoOn_cdf_noncentralChiSquaredMeasure hk h
    (a := max x 0) (b := max x 0 + 1) (le_max_right _ _)
    (add_nonneg (le_max_right _ _) zero_le_one) (by linarith)
  exact ((monotone_cdf _ (le_max_left x 0)).trans_lt hm).trans_le (cdf_le_one _ _)

/-- A positive cutoff has positive cumulative probability, including for the Dirac law. -/
theorem cdf_noncentralChiSquaredMeasure_pos (hk : 0 ≤ k) (l : ℝ≥0) (hx : 0 < x) :
    0 < cdf (noncentralChiSquaredMeasure k l) x := by
  by_cases h : k = 0 ∧ l = 0
  · rcases h with ⟨rfl, rfl⟩
    simp [noncentralChiSquaredMeasure_zero_noncentrality, chiSquaredMeasure_zero,
      cdf_dirac, hx.le]
  · exact (cdf_nonneg _ 0).trans_lt
      (strictMonoOn_cdf_noncentralChiSquaredMeasure hk (not_and_or.mp h) (by simp) hx.le hx)

/-- The cdf is continuous away from zero, also for the mixed degree-zero law. -/
theorem continuousOn_cdf_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) :
    ContinuousOn (cdf (noncentralChiSquaredMeasure k l)) {0}ᶜ := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rw [(cdf _).mono.continuousAt_iff_leftLim_eq_rightLim,
    ((cdf _).right_continuous x).rightLim_eq, Measure.leftLim_cdf,
    measureReal_congr (Iio_ae_eq_Iic'
      (noncentralChiSquaredMeasure_singleton_of_ne_zero hx k l)), ← cdf_eq_real]

/-- At positive degree there is no atom at zero, so the cdf is continuous everywhere. -/
theorem continuous_cdf_noncentralChiSquaredMeasure (hk : 0 < k) (l : ℝ≥0) :
    Continuous (cdf (noncentralChiSquaredMeasure k l)) := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk.le l
  have := nullSingletonClass_noncentralChiSquaredMeasure hk l
  exact Measure.continuous_cdf_of_noAtoms _

end TauCeti.Probability
