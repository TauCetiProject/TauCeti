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
public import TauCeti.Probability.Cdf

/-!
# Uniform measures on finite types

This file develops uniform probability measures on finite discrete spaces.  It identifies the
conditional counting measure `ProbabilityTheory.uniformOn` with Mathlib's finite Dirac-sum
measure, computes its masses and Bochner integrals, and shows that embeddings transport finite
uniform measures to uniform measures on their images, including uniform `n`-element subsets. For
labels in a measurable space, it computes masses by counting inputs, retaining multiplicities of
repeated labels; for real labels, it also computes the cdf. Quantile formulas and endpoint limits
are in `TauCeti.Probability.Distributions.Uniform.Quantile`.

## Main results

* `Finset.uniformOn_coe_finset_eq_uniformOfFinset`: the conditional-counting and
  finite Dirac-sum constructions agree.
* `Finset.support_uniformOn_coe_finset`: in a T₁ space, the topological support of a finite
  uniform law is its finite set.
* `Finset.uniformOn_univ_real_finset`: finite-type uniform masses are normalized cardinalities.
* `Finset.integral_uniformOn_finset`: integration against a finite uniform law is a
  normalized finite sum.
* `Finset.measureReal_map_uniformOn_finset_apply` and `Finset.cdf_map_uniformOn_finset`:
  label masses and cumulative masses are proportions of inputs.
* `Set.integrable_map_uniformOn` and `Finset.integral_map_uniformOn_finset`:
  every labelled observable is integrable, with expectation given by its average over inputs.
* `Set.BijOn.map_uniformOn`: a bijection between sets pushes a uniform law to
  the uniform law on its target, with no finiteness restriction.
* `Equiv.measurePreserving_uniformOn_univ`: a measurable bijection is measure preserving
  between the `uniformOn univ` measures on its domain and codomain (both are zero when the
  carriers are infinite or empty).
* `TauCeti.Probability.uniformOfFinset_univ_fin_two_prod_offDiagonal`: two independent uniform
  samples from `Fin 2` differ with probability `1 / 2`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

namespace Finset

/-- On a finite set, conditional counting measure agrees with the corresponding normalized
finite sum of Dirac measures.  This includes the common zero-measure convention for the empty
set. -/
theorem uniformOn_coe_finset_eq_uniformOfFinset (s : Finset α) :
    uniformOn (s : Set α) = Measure.uniformOfFinset s := by
  ext t _
  classical
  rw [uniformOn, cond_apply s.measurableSet, Measure.uniformOfFinset_apply, ENNReal.div_eq_inv_mul]
  -- Both sides count the points of `s` lying in `t`.
  simp [← Measure.count_apply_finset, Set.inter_def]

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
  refine (Measure.support_subset_of_isClosed s.finite_toSet.isClosed ?_).antisymm fun x hx ↦ ?_
  · rw [mem_ae_iff, ← uniformOn_inter_self s.finite_toSet, inter_compl_self, measure_empty]
  · refine (Measure.mem_support_iff_forall x).2 fun U hU ↦ ?_
    have hatom : 0 < uniformOn (s : Set α) {x} := by simp [mem_coe.mp hx]
    exact hatom.trans_le (measure_mono (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- The real mass of a finite set under the uniform law on a finite type is its cardinality
divided by the cardinality of the type. -/
theorem uniformOn_univ_real_finset [Fintype α] (s : Finset α) :
    (uniformOn (Set.univ : Set α)).real s = (s.card : ℝ) / Fintype.card α := by
  classical
  rw [measureReal_def, ← Finset.coe_univ, uniformOn_apply_finset]
  simp [ENNReal.toReal_div]

/-- Integration against a uniform law on a finite set is the normalized finite sum. -/
theorem integral_uniformOn_finset [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : Finset α) (f : α → E) :
    ∫ x, f x ∂uniformOn (s : Set α) = (s.card : ℝ)⁻¹ • ∑ x ∈ s, f x := by
  rw [uniformOn_coe_finset_eq_uniformOfFinset, Measure.uniformOfFinset,
    integral_finsetSum_measure]
  · simp [Finset.smul_sum]
  exact fun _ hx ↦
    (integrable_dirac (by simp)).smul_measure (by simp [s.ne_empty_of_mem hx])

end Finset

namespace Set

/-- Every function is integrable against `uniformOn`, which vanishes on infinite sets. -/
@[simp]
theorem integrable_uniformOn [SeminormedAddGroup E] (s : Set α) (f : α → E) :
    Integrable f (uniformOn s) := by
  by_cases hs : s.Finite
  · rw [← hs.coe_toFinset, Finset.uniformOn_coe_finset_eq_uniformOfFinset,
      Measure.uniformOfFinset]
    exact integrable_finsetSum_measure.2 fun _ hx ↦
      (integrable_dirac (by simp)).smul_measure (by simp [hs.toFinset.ne_empty_of_mem hx])
  · simp [(uniformOn_eq_zero).2 (Or.inl hs)]

/-- Every function is almost everywhere measurable against `uniformOn`, including on infinite
sets, where the measure is zero. -/
@[simp, fun_prop]
theorem aemeasurable_uniformOn [MeasurableSpace β] (s : Set α) (f : α → β) :
    AEMeasurable f (uniformOn s) := by
  by_cases hs : s.Finite
  · rw [← hs.coe_toFinset, Finset.uniformOn_coe_finset_eq_uniformOfFinset,
      Measure.uniformOfFinset, ← Measure.sum_coe_finset]
    exact aemeasurable_sum_measure_iff.2 fun _ ↦ aemeasurable_dirac.smul_measure _
  · simp [(uniformOn_eq_zero).2 (Or.inl hs)]

end Set

namespace TauCeti.Probability

/-- Integration against the uniform law on a finite type is the average over the type. -/
theorem integral_uniformOn_univ [Fintype α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : α → E) :
    ∫ x, f x ∂uniformOn (Set.univ : Set α) =
      (Fintype.card α : ℝ)⁻¹ • ∑ x, f x := by
  simpa using Finset.integral_uniformOn_finset (Finset.univ : Finset α) f

end TauCeti.Probability

namespace Set.BijOn

variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-- A bijection between sets transports one uniform law to the other. -/
theorem map_uniformOn {f : α → β} {s : Set α} {t : Set β}
    (h : Set.BijOn f s t) : (uniformOn s).map f = uniformOn t := by
  by_cases hs : s.Finite
  · have ht : t.Finite := h.finite_iff_finite.mp hs
    have hf := s.aemeasurable_uniformOn f
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

section PowersetCard

variable {γ δ : Type*}
    [MeasurableSpace (Finset γ)] [MeasurableSingletonClass (Finset γ)]
    [MeasurableSpace (Finset δ)] [MeasurableSingletonClass (Finset δ)]

/-- An embedding sends a uniform `n`-element subset of a finset `s` to a uniform `n`-element
subset of the image of `s`. For example, `Fin.valEmbedding` moves positions indexed by `Fin N`
into `ℕ`. -/
theorem map_finsetMap_uniformOn_powersetCard (f : γ ↪ δ) (s : Finset γ) (n : ℕ) :
    (uniformOn (s.powersetCard n : Set (Finset γ))).map (Finset.map f) =
      uniformOn ((s.map f).powersetCard n : Set (Finset δ)) := by
  rw [Finset.powersetCard_map]
  exact (Finset.mapEmbedding f).toEmbedding.map_uniformOn_finset _

end PowersetCard

end Function.Embedding

namespace Equiv

variable [MeasurableSpace β]

omit [MeasurableSingletonClass α] in
/-- A measurable bijection is measure preserving from the `uniformOn univ` measure on its domain
to the `uniformOn univ` measure on its codomain, for arbitrary measurable-space structures on
both types. When the carriers are infinite or empty, both measures are zero. -/
theorem measurePreserving_uniformOn_univ (e : α ≃ β) (he : Measurable e) :
    MeasurePreserving e (uniformOn (_root_.Set.univ : Set α))
      (uniformOn (_root_.Set.univ : Set β)) := by
  refine ⟨he, ?_⟩
  by_cases hα : Finite α
  · ext t ht
    rw [Measure.map_apply he ht]
    simp only [uniformOn, cond_apply .univ, _root_.Set.univ_inter, Measure.count_apply .univ,
      Measure.count_apply ht, Measure.count_apply (he ht)]
    rw [Set.encard_univ, Set.encard_univ, ENat.card_congr e,
      Set.encard_preimage_of_injective_subset_range e.injective (by simp)]
  · have hα' : Infinite α := not_finite_iff_infinite.mp hα
    have hβ : Infinite β := Infinite.of_injective e e.injective
    rw [(uniformOn_eq_zero' .univ).2 (Or.inl Set.infinite_univ),
      (uniformOn_eq_zero' .univ).2 (Or.inl Set.infinite_univ), Measure.map_zero]

/-- A bijection transports the uniform law on a type to the uniform law on its codomain. -/
theorem map_uniformOn_univ (e : α ≃ β) :
    (uniformOn (_root_.Set.univ : Set α)).map e = uniformOn (_root_.Set.univ : Set β) := by
  by_cases hα : Finite α
  · exact (e.measurePreserving_uniformOn_univ .of_discrete).map_eq
  · have hα' : Infinite α := not_finite_iff_infinite.mp hα
    have hβ : Infinite β := Infinite.of_injective e e.injective
    rw [(uniformOn_eq_zero' .univ).2 (Or.inl Set.infinite_univ),
      (uniformOn_eq_zero' .univ).2 (Or.inl Set.infinite_univ), Measure.map_zero]

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
  -- Sum the masses `2⁻¹ * 2⁻¹` of the two off-diagonal points `(0, 1)` and `(1, 0)`.
  rw [← Finset.coe_filter_univ, ← sum_measure_singleton]
  simp [← singleton_prod_singleton, Measure.prod_prod, Finset.sum_filter, Fintype.sum_prod_type,
    ← mul_add, ENNReal.inv_two_add_inv_two]

end TauCeti.Probability

namespace Finset

variable [MeasurableSpace β]

open Classical in
/-- The real mass of a set of labels under finite uniform sampling is the proportion of inputs
with labels in that set. Repeated labels are counted with their multiplicities. -/
theorem measureReal_map_uniformOn_finset_apply (s : Finset α) (f : α → β)
    {t : Set β} (ht : MeasurableSet t) :
    ((uniformOn (s : Set α)).map f).real t =
      ((s.filter fun i ↦ f i ∈ t).card : ℝ) / s.card := by
  rw [← integral_indicator_one ht,
    integral_map (Set.aemeasurable_uniformOn (s : Set α) f) (by fun_prop),
    integral_uniformOn_finset]
  simp [Set.indicator, sum_boole, div_eq_mul_inv, mul_comm]

open Classical in
/-- The cdf of a finitely labeled uniform sample counts inputs with label at most the argument. -/
theorem cdf_map_uniformOn_finset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) (x : ℝ) :
    cdf ((uniformOn (s : Set α)).map f) x =
      ((s.filter fun i ↦ f i ≤ x).card : ℝ) / s.card := by
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  rw [cdf_eq_real, measureReal_map_uniformOn_finset_apply s f measurableSet_Iic]
  simp only [Set.mem_Iic]

open Classical in
/-- A labeled finite uniform sample lies in the finite image of its sampling set almost surely.
The labeling function need not be globally measurable. -/
theorem ae_mem_image_map_uniformOn_finset [MeasurableSingletonClass β] (s : Finset α) (f : α → β) :
    ∀ᵐ x ∂(uniformOn (s : Set α)).map f, x ∈ s.image f := by
  apply (ae_map_iff (Set.aemeasurable_uniformOn (s : Set α) f) (s.image f).measurableSet).2
  rw [s.uniformOn_coe_finset_eq_uniformOfFinset, Measure.uniformOfFinset,
    ae_finsetSum_measure_iff]
  intro i hi
  apply Measure.ae_smul_measure
  simpa using s.mem_image_of_mem f hi

end Finset

namespace Set

/-- Every observable of a labelled uniform law is integrable, including on infinite sampling
sets, where the law is zero. No global measurability assumptions are needed. -/
@[simp]
theorem integrable_map_uniformOn [MeasurableSpace β] [MeasurableSingletonClass β]
    [SeminormedAddGroup E] (s : Set α) (f : α → β) (g : β → E) :
    Integrable g ((uniformOn s).map f) := by
  classical
  by_cases hs : s.Finite
  · have h : IntegrableOn g (hs.toFinset.image f : Set β) ((uniformOn s).map f) := by
      rw [← (hs.toFinset.image f : Set β).biUnion_of_singleton]
      simp only [Finset.mem_coe, integrableOn_finset_iUnion]
      exact fun _ _ ↦ integrableOn_singleton
    have hmem := hs.toFinset.ae_mem_image_map_uniformOn_finset f
    rw [hs.coe_toFinset] at hmem
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hmem] at h
  · simp [(uniformOn_eq_zero).2 (Or.inl hs)]

end Set

namespace Finset

variable [MeasurableSpace β]

/-- The expectation of an observable of a finite uniform sample is its average over inputs.
Repeated labels retain their multiplicities. -/
theorem integral_map_uniformOn_finset [MeasurableSingletonClass β]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : Finset α) (f : α → β) (g : β → E) :
    ∫ x, g x ∂(uniformOn (s : Set α)).map f =
      (s.card : ℝ)⁻¹ • ∑ i ∈ s, g (f i) := by
  rw [integral_map (Set.aemeasurable_uniformOn (s : Set α) f)
    (Set.integrable_map_uniformOn (s : Set α) f g).aestronglyMeasurable,
    integral_uniformOn_finset]

open Classical in
/-- Every label attained by a finite uniform sample has nonzero mass. -/
theorem map_uniformOn_finset_singleton_ne_zero (s : Finset α) (f : α → β)
    {x : β} (hx : x ∈ s.image f) : (uniformOn (s : Set α)).map f {x} ≠ 0 := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  apply ne_of_gt
  calc
    0 < uniformOn (s : Set α) {i} := by simp [hi]
    _ ≤ uniformOn (s : Set α) (f ⁻¹' {f i}) := measure_mono (by simp)
    _ ≤ (uniformOn (s : Set α)).map f {f i} :=
      Measure.le_map_apply (Set.aemeasurable_uniformOn (s : Set α) f) _

end Finset

namespace TauCeti.Probability

/-- The cdf after assigning real labels to a uniform sample from a nonempty finite type is the
proportion of labels no larger than the cutoff. Equal labels are counted with their full
multiplicity. -/
theorem cdf_map_uniformOn_univ [Fintype α] [Nonempty α] (label : α → ℝ) (x : ℝ) :
    cdf ((uniformOn (Set.univ : Set α)).map label) x =
      ((Finset.univ.filter fun i ↦ label i ≤ x).card : ℝ) / Fintype.card α := by
  simpa using Finset.univ.cdf_map_uniformOn_finset Finset.univ_nonempty label x

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The expectation of any observable of a native finite uniform sample is its average over
the sampling set, without a global measurability assumption on the observable. -/
theorem integral_comp_uniformOn_finset {s : Finset α} {X : Ω → α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hX : HasLaw X (uniformOn (s : Set α)) P) (g : α → E) :
    ∫ ω, g (X ω) ∂P = (s.card : ℝ)⁻¹ • ∑ i ∈ s, g i :=
  (hX.integral_comp (Set.integrable_uniformOn (s : Set α) g).aestronglyMeasurable).trans
    (s.integral_uniformOn_finset g)

/-- Assigning arbitrary labels to a native uniform random variable gives the mapped uniform
law, without requiring the labels to be globally measurable. -/
theorem fun_comp_uniformOn {s : Set α} [MeasurableSpace β] {X : Ω → α}
    (hX : HasLaw X (uniformOn s) P) (f : α → β) :
    HasLaw (fun ω ↦ f (X ω)) ((uniformOn s).map f) P :=
  (hasLaw_map (s.aemeasurable_uniformOn f)).fun_comp hX

/-- The expectation of any observable of a finitely labelled uniform random variable is its
average over the sampling inputs, without global measurability assumptions. -/
theorem integral_comp_map_uniformOn_finset {s : Finset α} [MeasurableSpace β]
    [MeasurableSingletonClass β] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : Ω → β} {f : α → β}
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) (g : β → E) :
    ∫ ω, g (X ω) ∂P = (s.card : ℝ)⁻¹ • ∑ i ∈ s, g (f i) :=
  (hX.integral_comp (Set.integrable_map_uniformOn (s : Set α) f g).aestronglyMeasurable).trans
    (s.integral_map_uniformOn_finset f g)

end ProbabilityTheory.HasLaw
