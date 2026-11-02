/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralF.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Cdf
import TauCeti.Probability.Distributions.Affine
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Cumulative probabilities of noncentral F laws

For positive numerator and denominator degrees, the noncentral F cdf is an absolutely
convergent Poisson series of regularized incomplete Beta functions. The argument
`m * x / (n + m * x)` is shared by every component, while the first Beta shape increases
with the Poisson count. The cdf is zero at nonpositive cutoffs, continuous everywhere,
and strictly increasing on the nonnegative half-line. These properties characterize
interior quantiles as unique positive roots of the series.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {m n x : ℝ} {l : ℝ≥0}

private theorem cdf_scaled_fisherSnedecorMeasure (hm : 0 < m) (hn : 0 < n)
    (j : ℕ) (hx : 0 < x) :
    cdf ((fisherSnedecorMeasure (m + 2 * j) n).map
      (fun y ↦ (m + 2 * j) / m * y)) x =
        regularizedIncompleteBeta ((m + 2 * j) / 2) (n / 2) (m * x / (n + m * x)) := by
  have hj : 0 < m + 2 * j := by positivity
  have hs : 0 < (m + 2 * j) / m := div_pos hj hm
  let _ := isProbabilityMeasure_fisherSnedecorMeasure hj hn
  have hmap := cdf_map_affine_of_pos
    (μ := fisherSnedecorMeasure (m + 2 * j) n) (a := 0) hs x
  simp only [zero_add, sub_zero] at hmap
  rw [hmap, cdf_fisherSnedecorMeasure_eq hj hn, ite_eq_right (not_le_of_gt (div_pos hx hs))]
  congr 1
  have hcancel : (m + 2 * j) * (x / ((m + 2 * j) / m)) = m * x := by
    field_simp
  rw [hcancel]

/-- At a nonpositive cutoff, a valid noncentral F law has cumulative probability zero. -/
@[simp]
theorem cdf_noncentralFMeasure_of_nonpos (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0)
    (hx : x ≤ 0) : cdf (noncentralFMeasure m n l) x = 0 := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  have hnull : noncentralFMeasure m n l (Iic x) = 0 :=
    measure_eq_zero_iff_ae_notMem.2
      ((ae_pos_noncentralFMeasure m n l).mono fun y hy ↦
        not_le.mpr (hx.trans_lt hy))
  rw [cdf_eq_real, measureReal_def, hnull, ENNReal.toReal_zero]

/-- At a positive cutoff the Poisson-weighted incomplete Beta functions sum to the cdf.
All terms are nonnegative, so this also asserts absolute convergence. -/
theorem hasSum_cdf_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0)
    (hx : 0 < x) :
    HasSum (fun j : ℕ ↦
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        regularizedIncompleteBeta ((m + 2 * j) / 2) (n / 2) (m * x / (n + m * x)))
      (cdf (noncentralFMeasure m n l) x) := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  have hsum := (ENNReal.summable.hasSum_iff.mpr
    (noncentralFMeasure_apply (n := n) hm l (Iic x)).symm).toReal (measure_ne_top _ _)
  rw [← measureReal_def, ← cdf_eq_real] at hsum
  convert hsum using 1
  funext j
  have hj : 0 < m + 2 * j := by positivity
  let _ := isProbabilityMeasure_fisherSnedecorMeasure hj hn
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
    ← cdf_eq_real, poissonMeasure_real_singleton, cdf_scaled_fisherSnedecorMeasure hm hn j hx]
  simp [NNReal.coe_div, neg_div]

/-- The noncentral F cdf is zero below its support and otherwise equals the convergent
Poisson series of regularized incomplete Beta functions. -/
theorem cdf_noncentralFMeasure_eq (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) (x : ℝ) :
    cdf (noncentralFMeasure m n l) x = if x ≤ 0 then 0 else ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        regularizedIncompleteBeta ((m + 2 * j) / 2) (n / 2) (m * x / (n + m * x)) := by
  split_ifs with hx
  · exact cdf_noncentralFMeasure_of_nonpos hm hn l hx
  · exact (hasSum_cdf_noncentralFMeasure hm hn l (lt_of_not_ge hx)).tsum_eq.symm

/-- The noncentral F cdf is continuous everywhere, including at zero. -/
theorem continuous_cdf_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    Continuous (cdf (noncentralFMeasure m n l)) := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  exact Measure.continuous_cdf_of_noAtoms _

/-- The noncentral F cdf increases strictly on the nonnegative half-line. -/
theorem strictMonoOn_cdf_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    StrictMonoOn (cdf (noncentralFMeasure m n l)) (Ici 0) := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Ici
    (by rw [support_noncentralFMeasure hm hn])

/-- A valid noncentral F law has positive cumulative probability exactly at positive cutoffs. -/
@[simp]
theorem cdf_noncentralFMeasure_pos_iff (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    0 < cdf (noncentralFMeasure m n l) x ↔ 0 < x := by
  constructor
  · intro hx
    by_contra h
    rw [cdf_noncentralFMeasure_of_nonpos hm hn l (le_of_not_gt h)] at hx
    exact (lt_irrefl _ hx)
  · intro hx
    exact (cdf_nonneg _ 0).trans_lt
      (strictMonoOn_cdf_noncentralFMeasure hm hn l (by simp) hx.le hx)

/-- Every finite cutoff leaves positive upper-tail probability. -/
theorem cdf_noncentralFMeasure_lt_one (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) (x : ℝ) :
    cdf (noncentralFMeasure m n l) x < 1 :=
  Measure.cdf_lt_one_of_strictMonoOn_Ici _ (strictMonoOn_cdf_noncentralFMeasure hm hn l) x

end TauCeti.Probability
