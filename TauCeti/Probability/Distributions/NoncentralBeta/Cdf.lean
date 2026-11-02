/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralBeta.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
import TauCeti.Probability.Cdf
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Dirac
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Cumulative distribution functions of noncentral Beta laws

The cdf of `noncentralBetaMeasure a b l` is the Poisson-weighted series, with weights of rate
`l / 2`, of the regularized incomplete Beta functions `regularizedIncompleteBeta (a + j) b`. The
same formula covers first shape zero: there the zero-count component is the point mass at zero,
and `regularizedIncompleteBeta 0 b` is exactly its unit-step cdf. Splitting off that term exhibits
the atom `exp (-l / 2)` at zero.

Away from the Dirac law at `a = l = 0`, the cdf is strictly increasing on `[0, 1]`, and it is
continuous away from zero. These facts characterize the quantiles of the family.

## Main results

* `TauCeti.Probability.hasSum_cdf_noncentralBetaMeasure` and
  `TauCeti.Probability.cdf_noncentralBetaMeasure_eq` — the Poisson series of incomplete Beta
  functions.
* `TauCeti.Probability.cdf_noncentralBetaMeasure_zero_shape` — the atom plus the continuous part
  at first shape zero.
* `TauCeti.Probability.cdf_noncentralBetaMeasure_of_neg`,
  `TauCeti.Probability.cdf_noncentralBetaMeasure_zero` and
  `TauCeti.Probability.cdf_noncentralBetaMeasure_of_one_le` — the values below, at and above the
  support.
* `TauCeti.Probability.strictMonoOn_cdf_noncentralBetaMeasure` — strict increase on `[0, 1]`.
* `TauCeti.Probability.continuousOn_cdf_noncentralBetaMeasure` and
  `TauCeti.Probability.continuous_cdf_noncentralBetaMeasure` — continuity.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
* The formal cdf architecture is adapted from
  `TauCeti.Probability.Distributions.NoncentralChiSquared.Cdf`, notably
  `hasSum_cdf_noncentralChiSquaredMeasure`,
  `cdf_noncentralChiSquaredMeasure_zero_degree`, and
  `continuousOn_cdf_noncentralChiSquaredMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {a b c x : ℝ} {l : ℝ≥0}

/-- The cdf of a mixture component is the regularized incomplete Beta function. This includes
first shape zero, where the component is the point mass at zero and the incomplete Beta function
is the unit step. -/
theorem cdf_noncentralBetaComponent (hc : 0 ≤ c) (hb : 0 < b) (x : ℝ) :
    cdf (noncentralBetaComponent c b) x = regularizedIncompleteBeta c b x := by
  rcases hc.eq_or_lt' with rfl | hc
  · rw [noncentralBetaComponent_zero, cdf_dirac]
    by_cases hx : 0 ≤ x
    · rw [ite_eq_left hx, regularizedIncompleteBeta_zero_left hb hx]
    · rw [ite_eq_right hx, regularizedIncompleteBeta_eq_zero_of_neg _ _ (not_le.mp hx)]
  · rw [noncentralBetaComponent_of_pos hc, cdf_betaMeasure_eq hc hb]

/-- The Poisson-weighted incomplete Beta functions sum to the noncentral Beta cdf. The terms are
nonnegative, so the series converges absolutely; this includes first shape zero. -/
theorem hasSum_cdf_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (x : ℝ) :
    HasSum (fun j : ℕ ↦ (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
      regularizedIncompleteBeta (a + j) b x) (cdf (noncentralBetaMeasure a b l) x) := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  have hsum := (ENNReal.summable.hasSum_iff.mpr
    (noncentralBetaMeasure_apply ha hb l (Iic x)).symm).toReal (measure_ne_top _ _)
  rw [← measureReal_def, ← cdf_eq_real] at hsum
  convert hsum using 1
  funext j
  have := isProbabilityMeasure_noncentralBetaComponent (a := a + j) (by positivity) hb
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ← cdf_eq_real,
    cdf_noncentralBetaComponent (by positivity) hb, poissonMeasure_real_singleton]
  simp [NNReal.coe_div, neg_div]

/-- The noncentral Beta cdf as a Poisson series of regularized incomplete Beta functions, at every
argument and for every valid first shape, including zero. -/
theorem cdf_noncentralBetaMeasure_eq (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (x : ℝ) :
    cdf (noncentralBetaMeasure a b l) x = ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        regularizedIncompleteBeta (a + j) b x :=
  (hasSum_cdf_noncentralBetaMeasure ha hb l x).tsum_eq.symm

/-- At first shape zero and a nonnegative argument, the cdf is the atom `exp (-l / 2)` plus the
Poisson-weighted Beta cdfs of positive first shape. This includes the Dirac law at `l = 0`. -/
theorem cdf_noncentralBetaMeasure_zero_shape (hb : 0 < b) (l : ℝ≥0) (hx : 0 ≤ x) :
    cdf (noncentralBetaMeasure 0 b l) x = exp (-(l : ℝ) / 2) + ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ (j + 1) / (j + 1).factorial) *
        regularizedIncompleteBeta ((j : ℝ) + 1) b x := by
  have hsum := hasSum_cdf_noncentralBetaMeasure le_rfl hb l x
  rw [← hsum.tsum_eq, hsum.summable.tsum_eq_zero_add]
  simp [regularizedIncompleteBeta_zero_left hb hx]

/-- A valid noncentral Beta law has no mass below zero. -/
@[simp]
theorem cdf_noncentralBetaMeasure_of_neg (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (hx : x < 0) :
    cdf (noncentralBetaMeasure a b l) x = 0 := by
  rw [← (hasSum_cdf_noncentralBetaMeasure ha hb l x).tsum_eq]
  simp [regularizedIncompleteBeta_eq_zero_of_neg _ _ hx]

/-- A valid noncentral Beta law has all its mass at or below one. -/
@[simp]
theorem cdf_noncentralBetaMeasure_of_one_le (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (hx : 1 ≤ x) :
    cdf (noncentralBetaMeasure a b l) x = 1 := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  have hnull : noncentralBetaMeasure a b l (Iic x)ᶜ = 0 :=
    measure_eq_zero_iff_ae_notMem.2 ((ae_mem_Icc_noncentralBetaMeasure a b l).mono
      fun y hy hy' ↦ hy' (hy.2.trans hx))
  rw [cdf_eq_real, measureReal_def, (prob_compl_eq_zero_iff measurableSet_Iic).mp hnull,
    ENNReal.toReal_one]

/-- The cdf at zero is the atom `exp (-l / 2)` at first shape zero, and zero at positive first
shape. -/
@[simp]
theorem cdf_noncentralBetaMeasure_zero (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    cdf (noncentralBetaMeasure a b l) 0 = if a = 0 then exp (-(l : ℝ) / 2) else 0 := by
  split_ifs with ha0
  · subst ha0
    rw [cdf_noncentralBetaMeasure_zero_shape hb l le_rfl, add_eq_left]
    refine (tsum_congr fun j ↦ ?_).trans tsum_zero
    rw [regularizedIncompleteBeta_eq_zero_of_nonpos (by positivity) b le_rfl, mul_zero]
  · rw [← (hasSum_cdf_noncentralBetaMeasure ha hb l 0).tsum_eq]
    refine (tsum_congr fun j ↦ ?_).trans tsum_zero
    rw [regularizedIncompleteBeta_eq_zero_of_nonpos (by positivity) b le_rfl, mul_zero]

/-- Away from the Dirac law at `a = l = 0`, the cdf is strictly increasing on the closed unit
interval, including from its possible atom at zero. -/
theorem strictMonoOn_cdf_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b)
    (hne : a ≠ 0 ∨ l ≠ 0) : StrictMonoOn (cdf (noncentralBetaMeasure a b l)) (Icc 0 1) := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Icc
    (support_noncentralBetaMeasure ha hb hne).ge

/-- Away from the Dirac law at `a = l = 0`, every cutoff below one leaves positive upper-tail
probability. -/
theorem cdf_noncentralBetaMeasure_lt_one (ha : 0 ≤ a) (hb : 0 < b) (hne : a ≠ 0 ∨ l ≠ 0)
    (hx : x < 1) : cdf (noncentralBetaMeasure a b l) x < 1 := by
  rcases lt_or_ge x 0 with hx₀ | hx₀
  · rw [cdf_noncentralBetaMeasure_of_neg ha hb l hx₀]
    exact one_pos
  · calc cdf (noncentralBetaMeasure a b l) x
        < cdf (noncentralBetaMeasure a b l) 1 :=
          strictMonoOn_cdf_noncentralBetaMeasure ha hb hne ⟨hx₀, hx.le⟩ ⟨zero_le_one, le_rfl⟩ hx
      _ = 1 := cdf_noncentralBetaMeasure_of_one_le ha hb l le_rfl

/-- Every positive cutoff has positive cumulative probability, including for the Dirac law. -/
theorem cdf_noncentralBetaMeasure_pos (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (hx : 0 < x) :
    0 < cdf (noncentralBetaMeasure a b l) x := by
  by_cases h : a = 0 ∧ l = 0
  · rcases h with ⟨rfl, rfl⟩
    rw [noncentralBetaMeasure_zero_noncentrality 0 hb, noncentralBetaComponent_zero, cdf_dirac,
      ite_eq_left hx.le]
    exact one_pos
  · rcases lt_or_ge x 1 with hx₁ | hx₁
    · exact (cdf_nonneg _ 0).trans_lt (strictMonoOn_cdf_noncentralBetaMeasure ha hb
        (not_and_or.mp h) ⟨le_rfl, zero_le_one⟩ ⟨hx.le, hx₁.le⟩ hx)
    · rw [cdf_noncentralBetaMeasure_of_one_le ha hb l hx₁]
      exact one_pos

/-- The cdf is continuous away from zero, also at first shape zero, where zero carries the atom. -/
theorem continuousOn_cdf_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    ContinuousOn (cdf (noncentralBetaMeasure a b l)) {0}ᶜ := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rw [(cdf _).mono.continuousAt_iff_leftLim_eq_rightLim,
    ((cdf _).right_continuous x).rightLim_eq, Measure.leftLim_cdf,
    measureReal_congr (Iio_ae_eq_Iic' (noncentralBetaMeasure_singleton_of_ne_zero hx a b l)),
    ← cdf_eq_real]

/-- At positive first shape there is no atom, so the cdf is continuous everywhere. -/
theorem continuous_cdf_noncentralBetaMeasure (ha : 0 < a) (hb : 0 < b) (l : ℝ≥0) :
    Continuous (cdf (noncentralBetaMeasure a b l)) := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha.le hb l
  have := nullSingletonClass_noncentralBetaMeasure ha b l
  exact Measure.continuous_cdf_of_noAtoms _

end TauCeti.Probability
