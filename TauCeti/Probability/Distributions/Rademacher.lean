/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.Distributions.Bernoulli.Basic
public import TauCeti.Probability.Quantile

/-!
# The Rademacher distribution

The Rademacher law is the probability measure on `ℝ` assigning equal mass to `-1` and `1`.
This file gives its masses and support, cumulative distribution and quantile, natural moments,
and moment- and characteristic-function formulas.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace TauCeti.Probability

/-- The Rademacher law, assigning probability `1 / 2` to each of `-1` and `1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  Ber((-1 : ℝ), 1, ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩)

/-- The Rademacher law is the equally weighted sum of the Dirac masses at `-1` and `1`. -/
theorem rademacherMeasure_eq :
    rademacherMeasure =
      (1 / 2 : ℝ≥0) • Measure.dirac (-1 : ℝ) + (1 / 2 : ℝ≥0) • Measure.dirac 1 := by
  rw [rademacherMeasure, bernoulliMeasure_def]
  congr 2
  · ext
    norm_num

/-- The Rademacher law is a probability measure. -/
instance : IsProbabilityMeasure rademacherMeasure := by
  rw [rademacherMeasure]
  infer_instance

/-- The Rademacher law is invariant under reflection in the origin. -/
theorem rademacherMeasure_map_neg :
    rademacherMeasure.map (fun x : ℝ ↦ -x) = rademacherMeasure := by
  rw [rademacherMeasure_eq, Measure.map_add _ _ measurable_neg]
  rw [Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_smul _ measurable_neg.aemeasurable]
  simp [add_comm]

/-- The Rademacher law is invariant under negation. -/
instance : rademacherMeasure.IsNegInvariant :=
  ⟨by simpa [Measure.neg_def] using rademacherMeasure_map_neg⟩

/-- Integration against the Rademacher law is the average of evaluation at `-1` and `1`. -/
theorem integral_rademacherMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    ∫ x, f x ∂rademacherMeasure = (1 / 2 : ℝ) • f (-1) + (1 / 2 : ℝ) • f 1 := by
  rw [rademacherMeasure, integral_bernoulliMeasure]
  norm_num

/-- Every function is integrable with respect to the finitely supported Rademacher law. -/
@[simp]
theorem integrable_rademacherMeasure {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    Integrable f rademacherMeasure := by
  rw [rademacherMeasure]
  exact integrable_bernoulliMeasure _ _ _ _

/-- Each of the two atoms of the Rademacher law has mass `1 / 2`, and every other singleton has
mass zero. -/
theorem rademacherMeasure_singleton (x : ℝ) :
    rademacherMeasure {x} = if x = -1 ∨ x = 1 then (1 / 2 : ℝ≥0∞) else 0 := by
  rw [rademacherMeasure_eq]
  simp only [Measure.add_apply, Measure.smul_apply, MeasurableSet.singleton, Measure.dirac_apply']
  by_cases hxneg : x = -1
  · subst x
    norm_num
  · by_cases hxpos : x = 1
    · subst x
      norm_num
    · simp [hxneg, hxpos]

attribute [simp] rademacherMeasure_singleton

/-- The topological support of the Rademacher law consists exactly of its two atoms. -/
@[simp]
theorem support_rademacherMeasure :
    rademacherMeasure.support = {(-1 : ℝ), 1} := by
  ext x
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro hx
    by_contra hmem
    have hopen : IsOpen ({(-1 : ℝ), 1} : Set ℝ)ᶜ :=
      (Set.Finite.isClosed (Set.finite_insert.mpr (Set.finite_singleton 1))).isOpen_compl
    have hxcompl : x ∈ ({(-1 : ℝ), 1} : Set ℝ)ᶜ := hmem
    have hpos := hx _ (hopen.mem_nhds hxcompl)
    rw [rademacherMeasure_eq] at hpos
    simp at hpos
  · intro hx U hU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hatom : 0 < rademacherMeasure {(-1 : ℝ)} := by
        rw [rademacherMeasure_singleton]
        norm_num
      exact hatom.trans_le (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))
    · have hatom : 0 < rademacherMeasure {(1 : ℝ)} := by
        rw [rademacherMeasure_singleton]
        norm_num
      exact hatom.trans_le (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- The cumulative distribution function of the Rademacher law. -/
@[simp]
theorem cdf_rademacherMeasure (x : ℝ) :
    cdf rademacherMeasure x =
      if x < -1 then 0 else if x < 1 then 1 / 2 else 1 := by
  rw [cdf_eq_real, rademacherMeasure,
    bernoulliMeasure_real_apply _ (measurableSet_Iic : MeasurableSet (Iic x))]
  by_cases hxneg : x < -1
  · have hneg : ¬ -1 ≤ x := by linarith
    have hpos : ¬ 1 ≤ x := by linarith
    simp [hxneg, hneg, hpos]
  · have hneg : -1 ≤ x := le_of_not_gt hxneg
    by_cases hxpos : x < 1
    · have hpos : ¬ 1 ≤ x := by linarith
      simp [hxneg, hxpos, hneg, hpos]
    · have hpos : 1 ≤ x := le_of_not_gt hxpos
      simp [hxneg, hxpos, hneg, hpos]

/-- The interior lower quantile of the Rademacher law is `-1` on the lower half of the unit
interval and `1` on the upper half. -/
@[simp]
theorem quantile_rademacherMeasure {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rademacherMeasure.quantile u = if u ≤ 1 / 2 then -1 else 1 := by
  split_ifs with hu_half
  · apply le_antisymm
    · rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_rademacherMeasure]
      norm_num
      exact hu_half
    · by_contra hlt
      have hlevel := Measure.le_cdf_quantile rademacherMeasure hu.2
      rw [cdf_rademacherMeasure] at hlevel
      simp only [ite_eq_left (lt_of_not_ge hlt)] at hlevel
      exact (not_le_of_gt hu.1) hlevel
  · apply le_antisymm
    · rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_rademacherMeasure]
      norm_num
      exact hu.2.le
    · by_contra hlt
      have hlevel := Measure.le_cdf_quantile rademacherMeasure hu.2
      rw [cdf_rademacherMeasure] at hlevel
      have hx : rademacherMeasure.quantile u < 1 := lt_of_not_ge hlt
      split_ifs at hlevel <;> linarith

/-- The lower quantile tends to the lower endpoint of the Rademacher support as the level tends to
zero from above. -/
theorem tendsto_quantile_rademacherMeasure_nhdsGT_zero :
    Tendsto rademacherMeasure.quantile (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
  rw [quantile_rademacherMeasure ⟨hu.1, hu.2.trans (by norm_num)⟩, ite_eq_left hu.2.le]

/-- The lower quantile tends to the upper endpoint of the Rademacher support as the level tends to
one from below. -/
theorem tendsto_quantile_rademacherMeasure_nhdsLT_one :
    Tendsto rademacherMeasure.quantile (nhdsWithin 1 (Iio 1)) (nhds 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with u hu
  rw [quantile_rademacherMeasure ⟨(half_pos zero_lt_one).trans hu.1, hu.2⟩,
    ite_eq_right (not_le_of_gt hu.1)]

/-- Every natural power is integrable under the Rademacher law. -/
theorem integrable_pow_rademacherMeasure (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) rademacherMeasure :=
  integrable_rademacherMeasure _

/-- The `n`th raw moment of the Rademacher law is one for even `n` and zero for odd `n`. -/
@[simp]
theorem integral_pow_rademacherMeasure (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂rademacherMeasure = if Even n then 1 else 0 := by
  rw [integral_rademacherMeasure]
  simp only [smul_eq_mul, one_div, one_pow, mul_one, neg_one_pow_eq_ite]
  split_ifs <;> norm_num

/-- The Rademacher law is centered. -/
@[simp]
theorem integral_id_rademacherMeasure : ∫ x, x ∂rademacherMeasure = 0 := by
  simpa using integral_pow_rademacherMeasure 1

/-- The variance of the Rademacher law is one. -/
@[simp]
theorem variance_id_rademacherMeasure : variance id rademacherMeasure = 1 := by
  rw [variance_eq_integral (by fun_prop)]
  simp only [id_eq, integral_id_rademacherMeasure, sub_zero]
  rw [integral_rademacherMeasure]
  norm_num

/-- Every exponential moment of the Rademacher law is integrable. -/
theorem integrable_exp_mul_id_rademacherMeasure (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) rademacherMeasure :=
  integrable_rademacherMeasure _

/-- The exponential-integrability domain of the Rademacher law is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_rademacherMeasure :
    integrableExpSet id rademacherMeasure = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true, id_eq]
  exact integrable_exp_mul_id_rademacherMeasure t

/-- The moment-generating function of the Rademacher law is the hyperbolic cosine. -/
@[simp]
theorem mgf_id_rademacherMeasure (t : ℝ) : mgf id rademacherMeasure t = cosh t := by
  rw [mgf, integral_rademacherMeasure, cosh_eq]
  simp only [id_eq, smul_eq_mul]
  ring_nf

/-- The cumulant-generating function of the Rademacher law is the logarithm of the hyperbolic
cosine. -/
@[simp]
theorem cgf_id_rademacherMeasure (t : ℝ) : cgf id rademacherMeasure t = log (cosh t) := by
  rw [cgf, mgf_id_rademacherMeasure]

/-- The characteristic function of the Rademacher law is the cosine. -/
@[simp]
theorem charFun_rademacherMeasure (t : ℝ) :
    charFun rademacherMeasure t = Real.cos t := by
  rw [charFun_apply_real, integral_rademacherMeasure, Complex.ofReal_cos, Complex.cos]
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one]
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring_nf

end TauCeti.Probability
