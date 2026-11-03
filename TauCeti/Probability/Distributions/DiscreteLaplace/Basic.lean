/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The discrete Laplace distribution

For an integer center `m` and a parameter `0 ≤ q < 1`, the discrete Laplace law is the
probability measure on `ℤ` with mass `(1 - q) q ^ |k - m| / (1 + q)` at every integer `k`. The
parameter `q = 0` gives the point mass at `m`; every parameter outside `[0, 1)` gives the zero
measure.

The law is the integer counterpart of the Laplace law: the difference of two independent geometric
counts with common success probability `p ≠ 0` is discrete Laplace with center zero and parameter
`1 - p` (see `TauCeti.Probability.map_sub_prod_geometricMeasure`), just as the difference of two
independent exponential variables is Laplace.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_discreteLaplaceMeasure` proves normalization, and
  `TauCeti.Probability.discreteLaplaceMeasure_singleton` computes the native masses;
* `TauCeti.Probability.discreteLaplaceMeasure_zero_right` identifies the `q = 0` boundary as a
  point mass, and `TauCeti.Probability.support_discreteLaplaceMeasure` gives full integer support
  for `0 < q < 1`;
* `TauCeti.Probability.map_add_const_discreteLaplaceMeasure` and
  `TauCeti.Probability.map_neg_discreteLaplaceMeasure` give translation and reflection;
* `TauCeti.Probability.measurable_discreteLaplaceMeasure` proves joint parameter measurability of
  the totalized family.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090–1102.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-! ### Definition and masses -/

/-- The real discrete Laplace mass `(1 - q) q ^ |k - m| / (1 + q)` at the integer `k`. -/
def discreteLaplaceWeightReal (m : ℤ) (q : ℝ) (k : ℤ) : ℝ :=
  (1 - q) * q ^ (k - m).natAbs / (1 + q)

/-- The defining formula of the real discrete Laplace mass. -/
theorem discreteLaplaceWeightReal_def (m : ℤ) (q : ℝ) (k : ℤ) :
    discreteLaplaceWeightReal m q k = (1 - q) * q ^ (k - m).natAbs / (1 + q) := (rfl)

/-- The discrete Laplace law on `ℤ` with center `m` and parameter `q`.

For `0 ≤ q < 1` this is the weighted Dirac sum with masses `(1 - q) q ^ |k - m| / (1 + q)`; the
parameter `q = 0` gives the point mass at `m`. Every other parameter value gives the zero
measure. -/
def discreteLaplaceMeasure (m : ℤ) (q : ℝ) : Measure ℤ :=
  if 0 ≤ q ∧ q < 1 then
    Measure.sum fun k => ENNReal.ofReal (discreteLaplaceWeightReal m q k) • Measure.dirac k
  else 0

/-- In the valid parameter range, the discrete Laplace law is its weighted Dirac sum. -/
theorem discreteLaplaceMeasure_eq_sum_dirac (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    discreteLaplaceMeasure m q =
      Measure.sum fun k => ENNReal.ofReal (discreteLaplaceWeightReal m q k) • Measure.dirac k := by
  simp [discreteLaplaceMeasure, hq0, hq1]

/-- Outside the parameter range `0 ≤ q < 1`, the discrete Laplace law is totalized to zero. -/
@[simp]
theorem discreteLaplaceMeasure_eq_zero_of_invalid (m : ℤ) {q : ℝ} (h : ¬(0 ≤ q ∧ q < 1)) :
    discreteLaplaceMeasure m q = 0 := by
  simp [discreteLaplaceMeasure, h]

/-- The real discrete Laplace masses are nonnegative for `0 ≤ q ≤ 1`. -/
theorem discreteLaplaceWeightReal_nonneg (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℤ) :
    0 ≤ discreteLaplaceWeightReal m q k := by
  have : 0 ≤ 1 - q := by linarith
  rw [discreteLaplaceWeightReal_def]
  positivity

/-- The real discrete Laplace masses are positive for `0 < q < 1`. -/
theorem discreteLaplaceWeightReal_pos (m : ℤ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℤ) :
    0 < discreteLaplaceWeightReal m q k := by
  have : 0 < 1 - q := by linarith
  rw [discreteLaplaceWeightReal_def]
  positivity

/-- The real discrete Laplace masses sum to one whenever `|q| < 1`; only `0 ≤ q < 1` gives
nonnegative masses. -/
theorem hasSum_discreteLaplaceWeightReal (m : ℤ) {q : ℝ} (hq : |q| < 1) :
    HasSum (discreteLaplaceWeightReal m q) 1 := by
  obtain ⟨hq0, hq1⟩ := abs_lt.mp hq
  have hq1' : 1 - q ≠ 0 := by linarith
  have hq1'' : 1 + q ≠ 0 := by linarith
  -- The two-sided geometric series `∑ q ^ |j|` splits into its nonnegative and negative halves.
  have hgeom := hasSum_geometric_of_abs_lt_one hq
  have hcenter : HasSum (fun j : ℤ => q ^ j.natAbs) ((1 - q)⁻¹ + q * (1 - q)⁻¹) := by
    refine HasSum.of_nat_of_neg_add_one (by simpa using hgeom) ?_
    refine (hgeom.mul_left q).congr_fun fun n => ?_
    have habs : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [habs, pow_succ']
  have h := (((Equiv.subRight m).hasSum_iff.mpr hcenter).mul_left (1 - q)).div_const (1 + q)
  have hone : (1 - q) * ((1 - q)⁻¹ + q * (1 - q)⁻¹) / (1 + q) = 1 := by field_simp
  rw [hone] at h
  exact h.congr_fun fun k => by simp [discreteLaplaceWeightReal_def]

/-- The discrete Laplace law is a probability measure for `0 ≤ q < 1`. -/
theorem isProbabilityMeasure_discreteLaplaceMeasure (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) : IsProbabilityMeasure (discreteLaplaceMeasure m q) := by
  rw [discreteLaplaceMeasure_eq_sum_dirac m hq0 hq1]
  have hq : |q| < 1 := abs_lt.mpr ⟨by linarith, hq1⟩
  exact (hasSum_discreteLaplaceWeightReal m hq).isProbabilityMeasure_sum_dirac
    (discreteLaplaceWeightReal_nonneg m hq0 hq1.le)

/-- The singleton mass of the discrete Laplace law in its valid parameter range. -/
@[simp]
theorem discreteLaplaceMeasure_singleton (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℤ) :
    discreteLaplaceMeasure m q {k} = ENNReal.ofReal (discreteLaplaceWeightReal m q k) := by
  rw [discreteLaplaceMeasure_eq_sum_dirac m hq0 hq1]
  exact Measure.sum_smul_dirac_singleton

/-- The real singleton mass of the discrete Laplace law in its valid parameter range. -/
theorem discreteLaplaceMeasure_real_singleton (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (k : ℤ) : (discreteLaplaceMeasure m q).real {k} = discreteLaplaceWeightReal m q k := by
  rw [measureReal_def, discreteLaplaceMeasure_singleton m hq0 hq1,
    ENNReal.toReal_ofReal (discreteLaplaceWeightReal_nonneg m hq0 hq1.le k)]

/-! ### Boundary and support -/

/-- The parameter `q = 0` gives the point mass at the center. -/
@[simp]
theorem discreteLaplaceMeasure_zero_right (m : ℤ) :
    discreteLaplaceMeasure m 0 = Measure.dirac m := by
  refine Measure.ext_of_singleton fun k => ?_
  rw [discreteLaplaceMeasure_singleton m le_rfl zero_lt_one, Measure.dirac_apply,
    discreteLaplaceWeightReal_def]
  by_cases hk : k = m
  · simp [hk]
  · have hk' : (k - m).natAbs ≠ 0 := by omega
    simp [hk', Ne.symm hk]

/-- For `0 < q < 1`, every integer has positive discrete Laplace mass. -/
theorem discreteLaplaceMeasure_singleton_pos (m : ℤ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (k : ℤ) : 0 < discreteLaplaceMeasure m q {k} := by
  rw [discreteLaplaceMeasure_singleton m hq0.le hq1, ENNReal.ofReal_pos]
  exact discreteLaplaceWeightReal_pos m hq0 hq1 k

/-- For `0 < q < 1`, the discrete Laplace law has full topological support on `ℤ`. -/
theorem support_discreteLaplaceMeasure (m : ℤ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (discreteLaplaceMeasure m q).support = univ := by
  ext k
  simp only [mem_univ, iff_true, Measure.mem_support_iff_forall]
  intro U hU
  exact (discreteLaplaceMeasure_singleton_pos m hq0 hq1 k).trans_le
    (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-! ### Translation and reflection -/

/-- Translating a discrete Laplace law by an integer translates its center. -/
@[simp]
theorem map_add_const_discreteLaplaceMeasure (m n : ℤ) (q : ℝ) :
    (discreteLaplaceMeasure m q).map (· + n) = discreteLaplaceMeasure (m + n) q := by
  by_cases hq : 0 ≤ q ∧ q < 1
  · refine Measure.ext_of_singleton fun k => ?_
    have hpre : (· + n) ⁻¹' {k} = {k - n} := by
      ext; simp [eq_sub_iff_add_eq, ← sub_eq_add_neg]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton k), hpre,
      discreteLaplaceMeasure_singleton _ hq.1 hq.2, discreteLaplaceMeasure_singleton _ hq.1 hq.2,
      discreteLaplaceWeightReal_def, discreteLaplaceWeightReal_def, sub_sub, add_comm n m]
  · simp [hq]

/-- Reflecting a discrete Laplace law reflects its center. -/
@[simp]
theorem map_neg_discreteLaplaceMeasure (m : ℤ) (q : ℝ) :
    (discreteLaplaceMeasure m q).map Neg.neg = discreteLaplaceMeasure (-m) q := by
  by_cases hq : 0 ≤ q ∧ q < 1
  · refine Measure.ext_of_singleton fun k => ?_
    have hpre : Neg.neg ⁻¹' {k} = {-k} := by ext; simp
    have habs : (k - -m).natAbs = (-k - m).natAbs := by omega
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton k), hpre,
      discreteLaplaceMeasure_singleton _ hq.1 hq.2, discreteLaplaceMeasure_singleton _ hq.1 hq.2,
      discreteLaplaceWeightReal_def, discreteLaplaceWeightReal_def, habs]
  · simp [hq]

/-! ### Parameter measurability -/

/-- The discrete Laplace family is jointly measurable in its center and parameter, including the
totalized zero measure outside `0 ≤ q < 1`. -/
@[fun_prop]
theorem measurable_discreteLaplaceMeasure :
    Measurable fun p : ℤ × ℝ => discreteLaplaceMeasure p.1 p.2 := by
  have hweight (k : ℤ) :
      Measurable fun p : ℤ × ℝ => ENNReal.ofReal (discreteLaplaceWeightReal p.1 p.2 k) := by
    have hexp : Measurable fun p : ℤ × ℝ => (k - p.1).natAbs :=
      (measurable_from_top (f := fun j : ℤ => (k - j).natAbs)).comp measurable_fst
    simp only [discreteLaplaceWeightReal_def]
    fun_prop
  have hvalid : MeasurableSet {p : ℤ × ℝ | 0 ≤ p.2 ∧ p.2 < 1} :=
    (measurableSet_Ici.preimage measurable_snd).inter (measurableSet_Iio.preimage measurable_snd)
  unfold discreteLaplaceMeasure
  exact Measurable.ite hvalid (TauCeti.MeasureTheory.measurable_sum_smul_dirac hweight)
    measurable_const

end TauCeti.Probability
