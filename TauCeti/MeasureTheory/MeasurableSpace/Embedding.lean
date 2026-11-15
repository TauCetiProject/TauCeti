/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable embeddings

An injective measurable map out of a countable type into a type with measurable singletons is a
measurable embedding: every subset of the domain is countable, hence so is its image, hence
measurable.

The two inclusions into a disjoint union are measurable embeddings, so pushing a measure forward
along them preserves the measure of every set, measurable or not. Coordinatewise application of
measurable embeddings across a countable product is likewise a measurable embedding.

## Main results

* `MeasurableEmbedding.of_injective_of_countable`
* `MeasurableEmbedding.inl` and `MeasurableEmbedding.inr`
* `MeasurableEmbedding.piMap`
-/

public section

open MeasureTheory Set

/-- An injective measurable map out of a countable type into a type with measurable singletons
is a measurable embedding. -/
theorem MeasurableEmbedding.of_injective_of_countable {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass γ] {f : β → γ}
    (hf : Measurable f) (hinj : Function.Injective f) : MeasurableEmbedding f where
  injective := hinj
  measurable := hf
  measurableSet_image' s _ := ((Set.to_countable s).image f).measurableSet

/-- The left inclusion into a disjoint union is a measurable embedding. -/
theorem MeasurableEmbedding.inl {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inl : α → α ⊕ β) where
  injective := Sum.inl_injective
  measurable := measurable_inl
  measurableSet_image' _ hs := hs.inl_image

/-- The right inclusion into a disjoint union is a measurable embedding. -/
theorem MeasurableEmbedding.inr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableEmbedding (Sum.inr : β → α ⊕ β) where
  injective := Sum.inr_injective
  measurable := measurable_inr
  measurableSet_image' _ hs := hs.inr_image

/-- Coordinatewise application of measurable embeddings over a countable index type is a measurable
embedding. -/
theorem MeasurableEmbedding.piMap {ι : Type*} [Countable ι] {α β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)] {f : ∀ i, α i → β i}
    (hf : ∀ i, MeasurableEmbedding (f i)) :
    MeasurableEmbedding (Pi.map f) := by
  have hf₁ : Measurable (Pi.map f) :=
    measurable_pi_iff.2 fun i => (hf i).measurable.comp (measurable_pi_apply i)
  have hrange : range (Pi.map f) = ⋂ i, (fun y : ∀ j, β j => y i) ⁻¹' range (f i) := by
    ext y
    simp only [mem_range, mem_iInter, mem_preimage]
    exact ⟨fun ⟨x, hx⟩ i => ⟨x i, congrFun hx i⟩,
      fun h => ⟨fun i => (h i).choose, funext fun i => (h i).choose_spec⟩⟩
  have hf₂ : MeasurableSet (range (Pi.map f)) :=
    hrange ▸ MeasurableSet.iInter fun i =>
      (hf i).measurableSet_range.preimage (measurable_pi_apply i)
  have hmem : ∀ y : range (Pi.map f), ∀ i, y.val i ∈ range (f i) :=
    fun ⟨_, x, hx⟩ i => ⟨x i, congrFun hx i⟩
  have hinv : ∀ i, Measurable (Equiv.ofInjective (f i) (hf i).injective).symm := fun i t ht => by
    have hpre : (Equiv.ofInjective (f i) (hf i).injective).symm ⁻¹' t =
        Subtype.val ⁻¹' (f i '' t) := by
      ext z
      simp only [mem_preimage, mem_image]
      exact ⟨fun hz => ⟨_, hz, Equiv.apply_ofInjective_symm (hf i).injective z⟩,
        fun ⟨a, ha, hfa⟩ => by
          have hz : z = Equiv.ofInjective (f i) (hf i).injective a := Subtype.ext hfa.symm
          simpa [hz] using ha⟩
    rw [hpre]
    exact ((hf i).measurableSet_image' ht).preimage measurable_subtype_coe
  refine MeasurableEmbedding.of_measurable_inverse_on_range hf₁ hf₂
    (g := fun y i => (Equiv.ofInjective (f i) (hf i).injective).symm ⟨y.val i, hmem y i⟩)
    ?_ fun x => ?_
  · exact measurable_pi_iff.2 fun i =>
      (hinv i).comp (((measurable_pi_apply i).comp measurable_subtype_coe).subtype_mk)
  · funext i
    exact Equiv.ofInjective_symm_apply (hf i).injective (x i)
