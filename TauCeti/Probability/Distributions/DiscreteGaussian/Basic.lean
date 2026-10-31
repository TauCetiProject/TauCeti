/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The discrete Gaussian distribution

For a real center `c` and width `s > 0`, the discrete Gaussian law on `ℤ` has mass proportional
to `exp (-((k : ℝ) - c) ^ 2 / (2 * s ^ 2))` at `k`. Its normalizing constant is the Gaussian
lattice sum `Real.gaussianLatticeSum c s`. At nonpositive widths the law is the zero measure.

This file supplies the normalized measure, its singleton masses and full support, its translation
and reflection symmetries, and parameter measurability. Moments, transforms, cumulative masses and
quantiles are developed separately.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_discreteGaussianMeasure_iff` characterizes exactly
  when the totalized law is a probability measure;
* `TauCeti.Probability.discreteGaussianMeasure_singleton` computes every native mass;
* `TauCeti.Probability.support_discreteGaussianMeasure` gives full integer support at positive
  width;
* `TauCeti.Probability.map_add_const_discreteGaussianMeasure` and
  `TauCeti.Probability.map_neg_discreteGaussianMeasure` give translation and reflection;
* `TauCeti.Probability.measurable_discreteGaussianMeasure` proves joint parameter measurability.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  Advances in Cryptology -- EUROCRYPT 2020, 552--578.
* `SampCert` verifies samplers for integer Gaussian laws. The measure-theoretic development here is
  independent of its programming and privacy interfaces.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-! ### Definition and normalization -/

/-- The normalized real discrete Gaussian weight at an integer.

At positive width this is the law's singleton mass. At negative width it remains a positive
normalized weight although the totalized law is zero; at zero width it is zero. -/
def discreteGaussianWeightReal (c s : ℝ) (k : ℤ) : ℝ :=
  Real.exp (-((k : ℝ) - c) ^ 2 / (2 * s ^ 2)) / Real.gaussianLatticeSum c s

/-- The defining formula for the real discrete Gaussian weight. -/
theorem discreteGaussianWeightReal_def (c s : ℝ) (k : ℤ) :
    discreteGaussianWeightReal c s k =
      Real.exp (-((k : ℝ) - c) ^ 2 / (2 * s ^ 2)) / Real.gaussianLatticeSum c s := (rfl)

/-- The `ℝ≥0∞`-valued discrete Gaussian weight.

At positive width this is the law's singleton mass. At negative width it remains a positive
normalized weight although the totalized law is zero; at zero width it is zero. -/
def discreteGaussianWeight (c s : ℝ) (k : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (discreteGaussianWeightReal c s k)

/-- The `ℝ≥0∞`-valued weight is obtained from the real weight by `ENNReal.ofReal`. -/
theorem discreteGaussianWeight_def (c s : ℝ) (k : ℤ) :
    discreteGaussianWeight c s k = ENNReal.ofReal (discreteGaussianWeightReal c s k) := (rfl)

/-- The discrete Gaussian law on `ℤ` with real center `c` and width `s`.

At positive width it is the weighted Dirac sum normalized by `Real.gaussianLatticeSum c s`.
At nonpositive width it is the zero measure. -/
def discreteGaussianMeasure (c s : ℝ) : Measure ℤ :=
  if 0 < s then Measure.sum fun k => discreteGaussianWeight c s k • Measure.dirac k else 0

/-- At positive width, the discrete Gaussian law is its weighted Dirac sum. -/
theorem discreteGaussianMeasure_eq_sum_dirac (c : ℝ) {s : ℝ} (hs : 0 < s) :
    discreteGaussianMeasure c s =
      Measure.sum fun k => discreteGaussianWeight c s k • Measure.dirac k := by
  simp [discreteGaussianMeasure, hs]

/-- At nonpositive width, the discrete Gaussian law is the zero measure. -/
@[simp]
theorem discreteGaussianMeasure_of_nonpos (c : ℝ) {s : ℝ} (hs : s ≤ 0) :
    discreteGaussianMeasure c s = 0 := by
  simp [discreteGaussianMeasure, hs.not_gt]

/-- At nonzero width, every normalized real discrete Gaussian weight is positive. -/
theorem discreteGaussianWeightReal_pos (c : ℝ) {s : ℝ} (hs : s ≠ 0) (k : ℤ) :
    0 < discreteGaussianWeightReal c s k := by
  rw [discreteGaussianWeightReal_def]
  exact div_pos (Real.exp_pos _) (Real.gaussianLatticeSum_pos c hs)

/-- Every normalized real discrete Gaussian weight is nonnegative. -/
theorem discreteGaussianWeightReal_nonneg (c s : ℝ) (k : ℤ) :
    0 ≤ discreteGaussianWeightReal c s k := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [discreteGaussianWeightReal, Real.gaussianLatticeSum_zero_right]
  · exact (discreteGaussianWeightReal_pos c hs k).le

/-- At nonzero width, the normalized real discrete Gaussian weights sum to one. -/
theorem hasSum_discreteGaussianWeightReal (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasSum (discreteGaussianWeightReal c s) 1 := by
  have hsum := (Real.hasSum_gaussianLatticeSum c hs).div_const
    (Real.gaussianLatticeSum c s)
  rw [div_self (Real.gaussianLatticeSum_pos c hs).ne'] at hsum
  exact hsum.congr_fun fun k => by rw [discreteGaussianWeightReal_def]

/-- The `ℝ≥0∞` weight coerces back to the normalized real weight. -/
@[simp]
theorem discreteGaussianWeight_toReal (c s : ℝ) (k : ℤ) :
    (discreteGaussianWeight c s k).toReal = discreteGaussianWeightReal c s k := by
  rw [discreteGaussianWeight, ENNReal.toReal_ofReal (discreteGaussianWeightReal_nonneg c s k)]

/-- A discrete Gaussian law with positive width is a probability measure. -/
theorem isProbabilityMeasure_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (discreteGaussianMeasure c s) := by
  rw [discreteGaussianMeasure_eq_sum_dirac c hs]
  exact (hasSum_discreteGaussianWeightReal c hs.ne').isProbabilityMeasure_sum_dirac
    fun k => (discreteGaussianWeightReal_pos c hs.ne' k).le

/-- The totalized discrete Gaussian law is a probability measure exactly at positive widths. -/
theorem isProbabilityMeasure_discreteGaussianMeasure_iff (c s : ℝ) :
    IsProbabilityMeasure (discreteGaussianMeasure c s) ↔ 0 < s := by
  refine ⟨fun h => ?_, isProbabilityMeasure_discreteGaussianMeasure c⟩
  by_contra hs
  rw [discreteGaussianMeasure_of_nonpos c (not_lt.mp hs)] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure ℤ) rfl

/-! ### Masses and support -/

/-- The singleton mass of a discrete Gaussian law with positive width. -/
@[simp]
theorem discreteGaussianMeasure_singleton (c : ℝ) {s : ℝ} (hs : 0 < s) (k : ℤ) :
    discreteGaussianMeasure c s {k} = discreteGaussianWeight c s k := by
  rw [discreteGaussianMeasure_eq_sum_dirac c hs]
  exact Measure.sum_smul_dirac_singleton

/-- The real singleton mass of a discrete Gaussian law with positive width. -/
@[simp]
theorem discreteGaussianMeasure_real_singleton (c : ℝ) {s : ℝ} (hs : 0 < s) (k : ℤ) :
    (discreteGaussianMeasure c s).real {k} = discreteGaussianWeightReal c s k := by
  rw [measureReal_def, discreteGaussianMeasure_singleton c hs,
    discreteGaussianWeight_toReal]

/-- At positive width, every integer has positive discrete Gaussian mass. -/
theorem discreteGaussianMeasure_singleton_pos (c : ℝ) {s : ℝ} (hs : 0 < s) (k : ℤ) :
    0 < discreteGaussianMeasure c s {k} := by
  rw [discreteGaussianMeasure_singleton c hs, discreteGaussianWeight, ENNReal.ofReal_pos]
  exact discreteGaussianWeightReal_pos c hs.ne' k

/-- At positive width, the discrete Gaussian law has full topological support on `ℤ`. -/
theorem support_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) :
    (discreteGaussianMeasure c s).support = univ := by
  ext k
  simp only [mem_univ, iff_true, Measure.mem_support_iff_forall]
  intro U hU
  exact (discreteGaussianMeasure_singleton_pos c hs k).trans_le
    (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-! ### Translation and reflection -/

/-- Translating an integer-valued discrete Gaussian translates its real center. -/
@[simp]
theorem map_add_const_discreteGaussianMeasure (c s : ℝ) (n : ℤ) :
    (discreteGaussianMeasure c s).map (· + n) = discreteGaussianMeasure (c + n) s := by
  by_cases hs : 0 < s
  · refine Measure.ext_of_singleton fun k => ?_
    have hpre : (· + n) ⁻¹' {k} = {k - n} := by
      ext j
      simp [eq_sub_iff_add_eq, ← sub_eq_add_neg]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton k), hpre,
      discreteGaussianMeasure_singleton c hs, discreteGaussianMeasure_singleton (c + n) hs,
      discreteGaussianWeight, discreteGaussianWeight, discreteGaussianWeightReal_def,
      discreteGaussianWeightReal_def, Real.gaussianLatticeSum_add_intCast]
    congr 2
    norm_num
    ring
  · simp [discreteGaussianMeasure_of_nonpos _ (not_lt.mp hs)]

/-- Reflecting a discrete Gaussian negates its center. -/
@[simp]
theorem map_neg_discreteGaussianMeasure (c s : ℝ) :
    (discreteGaussianMeasure c s).map Neg.neg = discreteGaussianMeasure (-c) s := by
  by_cases hs : 0 < s
  · refine Measure.ext_of_singleton fun k => ?_
    have hpre : Neg.neg ⁻¹' {k} = {-k} := by ext; simp
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton k), hpre,
      discreteGaussianMeasure_singleton c hs, discreteGaussianMeasure_singleton (-c) hs,
      discreteGaussianWeight, discreteGaussianWeight, discreteGaussianWeightReal_def,
      discreteGaussianWeightReal_def, Real.gaussianLatticeSum_neg_left]
    congr 2
    push_cast
    ring_nf
  · simp [discreteGaussianMeasure_of_nonpos _ (not_lt.mp hs)]

/-! ### Parameter measurability -/

/-- The discrete Gaussian family is jointly measurable in its center and width, including the
zero measure at nonpositive widths. -/
@[fun_prop]
theorem measurable_discreteGaussianMeasure :
    Measurable fun p : ℝ × ℝ => discreteGaussianMeasure p.1 p.2 := by
  have hweight (k : ℤ) :
      Measurable fun p : ℝ × ℝ => discreteGaussianWeight p.1 p.2 k := by
    apply ENNReal.measurable_ofReal.comp
    exact (by fun_prop : Measurable fun p : ℝ × ℝ =>
      Real.exp (-((k : ℝ) - p.1) ^ 2 / (2 * p.2 ^ 2))).div
        Real.measurable_gaussianLatticeSum
  unfold discreteGaussianMeasure
  exact Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    (TauCeti.MeasureTheory.measurable_sum_smul_dirac hweight) measurable_const

end TauCeti.Probability
