/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Support
public import TauCeti.Probability.Distributions.Poisson.Measurability

/-!
# Noncentral chi-squared laws as Poisson mixtures

The noncentral chi-squared law of degree `k ≥ 0` and noncentrality `l ≥ 0` mixes the central
chi-squared laws of degrees `k + 2 * n` against Poisson weights of rate `l / 2`. Negative
degrees give the zero measure. This construction includes the mixed degree-zero law: its
atom at zero has mass `exp (-l / 2)`, and the remaining components have positive degrees.

This file proves normalization, joint parameter measurability, the central specialization,
the atomic decomposition at degree zero, and exact topological support. The Poisson series
also supplies set-evaluation and nonnegative-integration formulas for subsequent calculations.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {k x : ℝ} {l : ℝ≥0}

/-- The noncentral chi-squared measure with real degree `k` and nonnegative noncentrality `l`.
For nonnegative degree it is a Poisson mixture of central chi-squared laws; negative degree
gives the zero measure. -/
def noncentralChiSquaredMeasure (k : ℝ) (l : ℝ≥0) : Measure ℝ :=
  if 0 ≤ k then
    (poissonMeasure (l / 2)).bind (fun n ↦ chiSquaredMeasure (k + 2 * n))
  else 0

/-- The defining Poisson mixture at nonnegative degree. -/
theorem noncentralChiSquaredMeasure_of_nonneg (hk : 0 ≤ k) (l : ℝ≥0) :
    noncentralChiSquaredMeasure k l =
      (poissonMeasure (l / 2)).bind (fun n ↦ chiSquaredMeasure (k + 2 * n)) := by
  rw [noncentralChiSquaredMeasure, ite_eq_left hk]

/-- Negative degrees give the zero measure, even at zero noncentrality. -/
@[simp]
theorem noncentralChiSquaredMeasure_of_neg (hk : k < 0) (l : ℝ≥0) :
    noncentralChiSquaredMeasure k l = 0 := by
  rw [noncentralChiSquaredMeasure, ite_eq_right (not_le.mpr hk)]

/-- Every nonnegative degree and noncentrality gives a probability law, including degree zero. -/
theorem isProbabilityMeasure_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) :
    IsProbabilityMeasure (noncentralChiSquaredMeasure k l) := by
  rw [noncentralChiSquaredMeasure_of_nonneg hk]
  exact isProbabilityMeasure_bind (.of_discrete)
    (ae_of_all _ fun n ↦ isProbabilityMeasure_chiSquaredMeasure (by positivity))

/-- The Poisson-weighted sum presentation of a noncentral chi-squared law. -/
theorem noncentralChiSquaredMeasure_eq_sum (hk : 0 ≤ k) (l : ℝ≥0) :
    noncentralChiSquaredMeasure k l = Measure.sum fun n : ℕ ↦
      poissonMeasure (l / 2) {n} • chiSquaredMeasure (k + 2 * n) := by
  ext s hs
  rw [noncentralChiSquaredMeasure_of_nonneg hk, Measure.bind_apply hs (.of_discrete),
    lintegral_countable', Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul, mul_comm]

/-- Set evaluation as an extended-real Poisson series; the formula holds for every set. -/
theorem noncentralChiSquaredMeasure_apply (hk : 0 ≤ k) (l : ℝ≥0) (s : Set ℝ) :
    noncentralChiSquaredMeasure k l s = ∑' n : ℕ,
      poissonMeasure (l / 2) {n} * chiSquaredMeasure (k + 2 * n) s := by
  rw [noncentralChiSquaredMeasure_eq_sum hk, Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Nonnegative integration can be performed component by component, without finiteness or
integrability assumptions on the observable. -/
theorem lintegral_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂noncentralChiSquaredMeasure k l = ∑' n : ℕ,
      poissonMeasure (l / 2) {n} * ∫⁻ x, f x ∂chiSquaredMeasure (k + 2 * n) := by
  rw [noncentralChiSquaredMeasure_eq_sum hk, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

/-- At zero noncentrality, the law is the central chi-squared law, including invalid degrees. -/
@[simp]
theorem noncentralChiSquaredMeasure_zero_noncentrality (k : ℝ) :
    noncentralChiSquaredMeasure k 0 = chiSquaredMeasure k := by
  by_cases hk : 0 ≤ k
  · ext s hs
    rw [noncentralChiSquaredMeasure_apply hk, tsum_eq_single 0]
    · simp [poissonMeasure_singleton]
    · intro n hn
      simp [poissonMeasure_singleton, hn]
  · simp [noncentralChiSquaredMeasure_of_neg (lt_of_not_ge hk),
      chiSquaredMeasure_of_neg (lt_of_not_ge hk)]

/-- The full totalized family is jointly measurable in degree and noncentrality. -/
@[fun_prop]
theorem measurable_noncentralChiSquaredMeasure :
    Measurable fun p : ℝ × ℝ≥0 ↦ noncentralChiSquaredMeasure p.1 p.2 := by
  classical
  have hseries : Measurable fun p : ℝ × ℝ≥0 ↦ Measure.sum fun n : ℕ ↦
      poissonMeasure (p.2 / 2) {n} • chiSquaredMeasure (p.1 + 2 * n) := by
    apply Measure.measurable_measure.2
    intro s hs
    simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    exact Measurable.tsum fun n ↦
      ((Measure.measurable_coe (measurableSet_singleton n)).comp
        (measurable_poissonMeasure.comp (measurable_snd.div_const 2))).mul
        ((Measure.measurable_coe hs).comp
          (measurable_chiSquaredMeasure.comp (measurable_fst.add_const (2 * (n : ℝ)))))
  have h : Measurable fun p : ℝ × ℝ≥0 ↦ if 0 ≤ p.1 then
      Measure.sum (fun n : ℕ ↦ poissonMeasure (p.2 / 2) {n} •
        chiSquaredMeasure (p.1 + 2 * n)) else 0 :=
    Measurable.ite (measurableSet_le measurable_const measurable_fst) hseries measurable_const
  convert h using 1
  funext p
  by_cases hk : 0 ≤ p.1
  · simp [hk, noncentralChiSquaredMeasure_eq_sum hk]
  · simp [hk, noncentralChiSquaredMeasure_of_neg (lt_of_not_ge hk)]

/-- A noncentral chi-squared variable is nonnegative almost surely. -/
theorem ae_nonneg_noncentralChiSquaredMeasure (k : ℝ) (l : ℝ≥0) :
    ∀ᵐ x ∂noncentralChiSquaredMeasure k l, 0 ≤ x := by
  by_cases hk : 0 ≤ k
  · rw [noncentralChiSquaredMeasure_eq_sum hk]
    exact Measure.ae_sum_iff.2 fun n ↦ Measure.ae_smul_measure (ae_nonneg_chiSquaredMeasure _) _
  · simp [noncentralChiSquaredMeasure_of_neg (lt_of_not_ge hk)]

/-- Positive degree makes a noncentral chi-squared variable strictly positive almost surely. -/
theorem ae_pos_noncentralChiSquaredMeasure (hk : 0 < k) (l : ℝ≥0) :
    ∀ᵐ x ∂noncentralChiSquaredMeasure k l, 0 < x := by
  rw [noncentralChiSquaredMeasure_eq_sum hk.le]
  exact Measure.ae_sum_iff.2 fun n ↦
    Measure.ae_smul_measure (ae_pos_chiSquaredMeasure (by positivity)) _

/-- At positive degree the noncentral law has no atoms. -/
theorem nullSingletonClass_noncentralChiSquaredMeasure (hk : 0 < k) (l : ℝ≥0) :
    NullSingletonClass (noncentralChiSquaredMeasure k l) := by
  constructor
  intro x
  rw [noncentralChiSquaredMeasure_apply hk.le]
  apply ENNReal.tsum_eq_zero.2
  intro n
  rw [chiSquaredMeasure_singleton (by positivity), mul_zero]

/-- At degree zero, the Poisson count zero contributes the atom and every positive count
contributes a positive-degree central law. -/
theorem noncentralChiSquaredMeasure_zero_degree (l : ℝ≥0) :
    noncentralChiSquaredMeasure 0 l =
      ENNReal.ofReal (exp (-(l : ℝ) / 2)) • Measure.dirac 0 +
        Measure.sum (fun n : ℕ ↦ poissonMeasure (l / 2) {n + 1} •
          chiSquaredMeasure (2 * (n + 1))) := by
  ext s hs
  rw [noncentralChiSquaredMeasure_apply (by norm_num), Measure.add_apply,
    Measure.sum_apply _ hs, tsum_eq_zero_add' ENNReal.summable]
  simp only [Measure.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero, zero_add,
    chiSquaredMeasure_zero, Nat.cast_add, Nat.cast_one]
  congr 1
  simp [poissonMeasure_singleton, NNReal.coe_div, neg_div]

/-- The atom of the degree-zero law has mass `exp (-l / 2)`, including mass one at `l = 0`. -/
@[simp]
theorem noncentralChiSquaredMeasure_zero_degree_mass (l : ℝ≥0) :
    noncentralChiSquaredMeasure 0 l {0} = ENNReal.ofReal (exp (-(l : ℝ) / 2)) := by
  rw [noncentralChiSquaredMeasure_zero_degree, Measure.add_apply,
    Measure.sum_apply _ (measurableSet_singleton 0)]
  have hzero (n : ℕ) : chiSquaredMeasure (2 * ((n : ℝ) + 1)) {0} = 0 :=
    chiSquaredMeasure_singleton (by positivity) 0
  simp [Measure.smul_apply, hzero]

/-- Zero is the only possible atom, for every degree and noncentrality. -/
@[simp]
theorem noncentralChiSquaredMeasure_singleton_of_ne_zero (hx : x ≠ 0) (k : ℝ) (l : ℝ≥0) :
    noncentralChiSquaredMeasure k l {x} = 0 := by
  by_cases hk : 0 ≤ k
  · rw [noncentralChiSquaredMeasure_apply hk]
    apply ENNReal.tsum_eq_zero.2
    intro n
    by_cases hdeg : k + 2 * n = 0
    · simp [hdeg, chiSquaredMeasure_zero, hx]
    · rw [chiSquaredMeasure_singleton (lt_of_le_of_ne (by positivity) (Ne.symm hdeg)),
        mul_zero]
  · simp [noncentralChiSquaredMeasure_of_neg (lt_of_not_ge hk)]

/-- Every valid law other than the double-zero Dirac law dominates a positive-weight
central chi-squared component of positive degree. -/
theorem exists_smul_chiSquaredMeasure_le_noncentralChiSquaredMeasure (hk : 0 ≤ k)
    (hne : k ≠ 0 ∨ l ≠ 0) :
    ∃ n : ℕ, 0 < k + 2 * n ∧ poissonMeasure (l / 2) {n} ≠ 0 ∧
      poissonMeasure (l / 2) {n} • chiSquaredMeasure (k + 2 * n) ≤
        noncentralChiSquaredMeasure k l := by
  have hle (n : ℕ) : poissonMeasure (l / 2) {n} • chiSquaredMeasure (k + 2 * n) ≤
      noncentralChiSquaredMeasure k l := by
    rw [noncentralChiSquaredMeasure_eq_sum hk]
    exact Measure.le_sum (fun j : ℕ ↦
      poissonMeasure (l / 2) {j} • chiSquaredMeasure (k + 2 * j)) n
  rcases hne with hk' | hl
  · refine ⟨0, by simpa using lt_of_le_of_ne hk hk'.symm, ?_, hle 0⟩
    simp [poissonMeasure_singleton, exp_pos]
  · refine ⟨1, by positivity, ?_, hle 1⟩
    rw [poissonMeasure_singleton, ENNReal.ofReal_ne_zero_iff]
    have : 0 < (l : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hl)
    positivity

/-- The support is empty for negative degree, the singleton zero at zero degree and
noncentrality, and `[0, ∞)` in every other valid case. -/
@[simp]
theorem support_noncentralChiSquaredMeasure (k : ℝ) (l : ℝ≥0) :
    (noncentralChiSquaredMeasure k l).support =
      if k < 0 then ∅ else if k = 0 ∧ l = 0 then {0} else Ici 0 := by
  by_cases hkneg : k < 0
  · simp [hkneg]
  rw [ite_eq_right hkneg]
  by_cases hzero : k = 0 ∧ l = 0
  · rcases hzero with ⟨rfl, rfl⟩
    rw [noncentralChiSquaredMeasure_zero_noncentrality, support_chiSquaredMeasure]
    simp
  rw [ite_eq_right hzero]
  have hk : 0 ≤ k := le_of_not_gt hkneg
  have hne : k ≠ 0 ∨ l ≠ 0 := not_and_or.mp hzero
  apply Set.Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici
      (ae_nonneg_noncentralChiSquaredMeasure k l)
  · obtain ⟨n, hdeg, hw, hle⟩ :=
      exists_smul_chiSquaredMeasure_le_noncentralChiSquaredMeasure hk hne
    have hac := (Measure.absolutelyContinuous_smul hw).trans hle.absolutelyContinuous
    simpa only [support_chiSquaredMeasure, ite_eq_right hdeg.ne', ite_eq_left hdeg] using
      hac.support_mono

end TauCeti.Probability
