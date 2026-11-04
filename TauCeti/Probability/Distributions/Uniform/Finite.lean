/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.Quantile.Finite

/-!
# Uniform measures on finite types

This file develops uniform probability measures on finite discrete spaces.  It identifies the
conditional counting measure `ProbabilityTheory.uniformOn` with Mathlib's finite Dirac-sum
measure, computes its masses and Bochner integrals, and shows that embeddings transport finite
uniform measures to uniform measures on their images.

## Main results

* `Finset.uniformOn_coe_finset_eq_uniformOfFinset`: the conditional-counting and
  finite Dirac-sum constructions agree.
* `Finset.support_uniformOn_coe_finset`: in a T₁ space, the topological support of a finite
  uniform law is its finite set.
* `Finset.uniformOn_univ_real_finset`: the real mass of a finite set under the uniform law on a
  finite type is its normalized cardinality.
* `Finset.integral_uniformOn_finset`: integration against a finite uniform law is a
  normalized finite sum.
* `TauCeti.Probability.quantile_map_uniformOn_univ_eq_iff` characterizes quantiles after
  assigning arbitrary real labels to a finite uniform sample;
* `TauCeti.Probability.tendsto_quantile_map_uniformOn_univ_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_map_uniformOn_univ_nhdsLT_one` give its endpoint limits.
* `Set.BijOn.map_uniformOn`: a bijection between sets pushes a uniform law to
  the uniform law on its target, with no finiteness restriction.
* `TauCeti.Probability.uniformOfFinset_univ_fin_two_prod_offDiagonal`: two independent uniform
  samples from `Fin 2` differ with probability `1 / 2`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

namespace Finset

/-- On a finite set, conditional counting measure agrees with the corresponding normalized
finite sum of Dirac measures.  This includes the common zero-measure convention for the empty
set. -/
theorem uniformOn_coe_finset_eq_uniformOfFinset (s : Finset α) :
    uniformOn (s : Set α) = Measure.uniformOfFinset s := by
  ext t ht
  rw [uniformOn, cond_apply s.measurableSet, Measure.uniformOfFinset_apply]
  rw [Measure.count_apply_finset]
  rw [Measure.count_apply_finite _ (s.finite_toSet.inter_of_left t)]
  rw [ENNReal.div_eq_inv_mul]
  congr 1
  norm_cast
  apply congrArg Finset.card
  ext x
  simp

open scoped Classical in
/-- Every point of a finite set has mass the reciprocal of its cardinality, and points outside
the set have mass zero. -/
@[simp]
theorem uniformOn_coe_finset_apply_singleton (s : Finset α) (a : α) :
    uniformOn (s : Set α) {a} = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [uniformOn_coe_finset_eq_uniformOfFinset]
  exact Measure.uniformOfFinset_apply_singleton a

/-- In a T₁ space, the topological support of the uniform law on a finite set is that set. -/
@[simp]
theorem support_uniformOn_coe_finset [TopologicalSpace α] [T1Space α] (s : Finset α) :
    (uniformOn (s : Set α)).support = s := by
  classical
  ext x
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro h
    by_contra hx
    have hpos := h _ (s.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)
    rw [← uniformOn_inter_self s.finite_toSet, inter_compl_self, measure_empty] at hpos
    exact lt_irrefl 0 hpos
  · intro hx U hU
    have hatom : 0 < uniformOn (s : Set α) {x} := by
      rw [uniformOn_coe_finset_apply_singleton, ite_eq_left (mem_coe.mp hx)]
      exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
    exact hatom.trans_le (measure_mono (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- The real mass of a finite set under the uniform law on a finite type is its cardinality
divided by the cardinality of the type. -/
theorem uniformOn_univ_real_finset [Fintype α] (s : Finset α) :
    (uniformOn (Set.univ : Set α)).real s = (s.card : ℝ) / Fintype.card α := by
  classical
  rw [measureReal_def, ← Finset.coe_univ, uniformOn_apply_finset]
  simp [ENNReal.toReal_div]

end Finset

namespace TauCeti.Probability

/-- Every point of a nonempty finite type has mass the reciprocal of the cardinality under the
uniform law. -/
@[simp]
theorem uniformOn_univ_apply_singleton [Fintype α] (a : α) :
    uniformOn (Set.univ : Set α) {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simpa using Finset.uniformOn_coe_finset_apply_singleton (Finset.univ : Finset α) a

/-- The cdf after assigning real labels to a uniform sample from a nonempty finite type is the
proportion of labels no larger than the cutoff. Equal labels are counted with their full
multiplicity. -/
theorem cdf_map_uniformOn_univ [Fintype α] [Nonempty α] (label : α → ℝ) (x : ℝ) :
    cdf ((uniformOn (Set.univ : Set α)).map label) x =
      ((Finset.univ.filter fun i ↦ label i ≤ x).card : ℝ) / Fintype.card α := by
  rw [Measure.cdf_map _ label (measurable_of_finite label).aemeasurable]
  have hpreimage : label ⁻¹' Set.Iic x =
      (Finset.univ.filter fun i ↦ label i ≤ x : Finset α) := by
    ext i
    simp
  rw [hpreimage, Finset.uniformOn_univ_real_finset]

/-- A real number is the quantile of a uniformly sampled finite collection of supplied labels
exactly when the level strictly exceeds the proportion of smaller labels and is at most the
proportion of labels no larger than it. This is the cumulative-crossing description obtained by
sorting the distinct labels and aggregating equal ones. -/
theorem quantile_map_uniformOn_univ_eq_iff [Fintype α] [Nonempty α] (label : α → ℝ)
    {u x : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    ((uniformOn (Set.univ : Set α)).map label).quantile u = x ↔
      ((Finset.univ.filter fun i ↦ label i < x).card : ℝ) / Fintype.card α < u ∧
        u ≤ ((Finset.univ.filter fun i ↦ label i ≤ x).card : ℝ) / Fintype.card α := by
  rw [Measure.quantile_map_finite_eq_iff _ label hu]
  have hpreimage_lt : label ⁻¹' Set.Iio x =
      (Finset.univ.filter fun i ↦ label i < x : Finset α) := by
    ext i
    simp
  have hpreimage_le : label ⁻¹' Set.Iic x =
      (Finset.univ.filter fun i ↦ label i ≤ x : Finset α) := by
    ext i
    simp
  rw [hpreimage_lt, hpreimage_le, Finset.uniformOn_univ_real_finset,
    Finset.uniformOn_univ_real_finset]

/-- As the level tends to zero from above, labelled finite-uniform quantiles tend to a least
supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsGT_zero [Finite α] [Nonempty α]
    (label : α → ℝ) (i : α) (hmin : ∀ j, label i ≤ label j) :
    Tendsto ((uniformOn (Set.univ : Set α)).map label).quantile (𝓝[>] 0)
      (𝓝 (label i)) := by
  let _ := Fintype.ofFinite α
  apply Measure.tendsto_quantile_map_finite_nhdsGT_zero
    (uniformOn (Set.univ : Set α)) label i
  · rw [measureReal_def, uniformOn_univ_apply_singleton]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact fun j _ ↦ hmin j

/-- As the level tends to one from below, labelled finite-uniform quantiles tend to a greatest
supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsLT_one [Finite α] [Nonempty α]
    (label : α → ℝ) (i : α) (hmax : ∀ j, label j ≤ label i) :
    Tendsto ((uniformOn (Set.univ : Set α)).map label).quantile (𝓝[<] 1)
      (𝓝 (label i)) := by
  let _ := Fintype.ofFinite α
  apply Measure.tendsto_quantile_map_finite_nhdsLT_one
    (uniformOn (Set.univ : Set α)) label i
  · rw [measureReal_def, uniformOn_univ_apply_singleton]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact fun j _ ↦ hmax j

end TauCeti.Probability

namespace Finset

/-- A function is integrable against a uniform law on a finite set. -/
theorem integrable_uniformOn_finset [SeminormedAddGroup E] (s : Finset α) (f : α → E) :
    Integrable f (uniformOn (s : Set α)) := by
  rw [uniformOn_coe_finset_eq_uniformOfFinset, Measure.uniformOfFinset]
  exact integrable_finsetSum_measure.2 fun _ hx ↦
    (integrable_dirac (by simp)).smul_measure (by simp [s.ne_empty_of_mem hx])

/-- Integration against a uniform law on a finite set is the normalized finite sum. -/
theorem integral_uniformOn_finset [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : Finset α) (f : α → E) :
    ∫ x, f x ∂uniformOn (s : Set α) = (s.card : ℝ)⁻¹ • ∑ x ∈ s, f x := by
  rw [uniformOn_coe_finset_eq_uniformOfFinset, Measure.uniformOfFinset,
    integral_finsetSum_measure]
  · simp [Finset.smul_sum]
  exact fun _ hx ↦
    (integrable_dirac (by simp)).smul_measure (by simp [s.ne_empty_of_mem hx])

variable [MeasurableSpace β]

/-- Every function is almost everywhere measurable against a uniform law on a finite set. -/
theorem aemeasurable_uniformOn_finset (s : Finset α) (f : α → β) :
    AEMeasurable f (uniformOn (s : Set α)) := by
  rw [uniformOn_coe_finset_eq_uniformOfFinset, Measure.uniformOfFinset, ← Measure.sum_coe_finset]
  exact aemeasurable_sum_measure_iff.2 fun _ ↦ aemeasurable_dirac.smul_measure _

end Finset

namespace TauCeti.Probability

/-- Integration against the uniform law on a finite type is the average over the type. -/
theorem integral_uniformOn_univ [Fintype α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : α → E) :
    ∫ x, f x ∂uniformOn (Set.univ : Set α) =
      (Fintype.card α : ℝ)⁻¹ • ∑ x, f x := by
  simpa using Finset.integral_uniformOn_finset (Finset.univ : Finset α) f

end TauCeti.Probability

namespace Set.BijOn

variable [MeasurableSpace β]

variable [MeasurableSingletonClass β]

/-- A bijection between sets transports one uniform law to the other. -/
theorem map_uniformOn {f : α → β} {s : Set α} {t : Set β}
    (h : Set.BijOn f s t) : (uniformOn s).map f = uniformOn t := by
  by_cases hs : s.Finite
  · have ht : t.Finite := h.finite_iff_finite.mp hs
    have hf : AEMeasurable f (uniformOn s) := by
      simpa using Finset.aemeasurable_uniformOn_finset hs.toFinset f
    ext t' ht'
    have hinter : Set.BijOn f (s ∩ f ⁻¹' t') (t ∩ t') :=
      h.inter_mapsTo (fun _ hx ↦ hx) Set.inter_subset_right
    rw [Measure.map_apply_of_aemeasurable hf ht', uniformOn, cond_apply hs.measurableSet,
      uniformOn, cond_apply ht.measurableSet]
    rw [Measure.count_apply hs.measurableSet, Measure.count_apply ht.measurableSet,
      Measure.count_apply (hs.inter_of_left _).measurableSet,
      Measure.count_apply (ht.inter_of_left _).measurableSet]
    rw [Set.encard_congr h.equiv, Set.encard_congr hinter.equiv]
  · have ht : ¬ t.Finite := fun ht ↦ hs (h.finite_iff_finite.mpr ht)
    rw [(uniformOn_eq_zero).2 (Or.inl hs), (uniformOn_eq_zero).2 (Or.inl ht), Measure.map_zero]

end Set.BijOn

namespace Function.Embedding

variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-- An embedding transports the uniform law on a finite set to the uniform law on its image. -/
theorem map_uniformOn_finset (e : α ↪ β) (s : Finset α) :
    (uniformOn (s : Set α)).map e = uniformOn (s.map e : Finset β) := by
  simpa only [Finset.coe_map] using
    e.injective.injOn.bijOn_image.map_uniformOn

end Function.Embedding

namespace Equiv

variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-- A bijection transports the uniform law on a type to the uniform law on its codomain. -/
theorem map_uniformOn_univ (e : α ≃ β) :
    (uniformOn (_root_.Set.univ : Set α)).map e = uniformOn (_root_.Set.univ : Set β) := by
  exact e.bijective.bijOn_univ.map_uniformOn

end Equiv

namespace TauCeti.Probability

/-- The uniform measure on all of a nonempty finite type is a probability measure. -/
instance isProbabilityMeasure_uniformOfFinset_univ {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] :
    IsProbabilityMeasure (Measure.uniformOfFinset (Finset.univ : Finset α)) := by
  constructor
  simp [Measure.uniformOfFinset, _root_.sum_apply, Finset.sum_const, nsmul_eq_mul,
    ENNReal.mul_inv_cancel, Fintype.card_ne_zero]

/-- Two independent uniform samples from `Fin 2` differ with probability `1 / 2`. -/
@[simp]
theorem uniformOfFinset_univ_fin_two_prod_offDiagonal :
    ((Measure.uniformOfFinset (Finset.univ : Finset (Fin 2))).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin 2)))) {q | q.1 ≠ q.2} = (2 : ℝ≥0∞)⁻¹ := by
  have h : {q : Fin 2 × Fin 2 | q.1 ≠ q.2} = {(0, 1), (1, 0)} := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp
  rw [h, ← singleton_union, measure_union (by simp) (measurableSet_singleton _)]
  simp only [← singleton_prod_singleton, Measure.prod_prod,
    Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.cast_ofNat]
  rw [← mul_two, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

end TauCeti.Probability
