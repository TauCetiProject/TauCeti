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
* `MeasurableEmbedding.piMap` and `MeasurableEmbedding.comp_left`
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
  have hf₂ : MeasurableSet (range (Pi.map f)) := by
    rw [range_piMap]
    exact MeasurableSet.univ_pi fun i => (hf i).measurableSet_range
  have hmem : ∀ y : range (Pi.map f), ∀ i, y.val i ∈ range (f i) :=
    fun ⟨_, x, hx⟩ i => ⟨x i, congrFun hx i⟩
  refine MeasurableEmbedding.of_measurable_inverse_on_range hf₁ hf₂
    (g := fun y i => (hf i).equivRange.symm ⟨y.val i, hmem y i⟩) ?_ fun x => ?_
  · exact measurable_pi_iff.2 fun i =>
      (hf i).equivRange.symm.measurable.comp
        (((measurable_pi_apply i).comp measurable_subtype_coe).subtype_mk)
  · funext i
    exact (hf i).equivRange_symm_apply_mk (x i)

/-- Postcomposition with a measurable embedding on functions out of a countable index type is a
measurable embedding. -/
theorem MeasurableEmbedding.comp_left {ι α β : Type*} [Countable ι] [MeasurableSpace α]
    [MeasurableSpace β] {f : α → β} (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (f ∘ · : (ι → α) → ι → β) := by
  have heq : (f ∘ · : (ι → α) → ι → β) = Pi.map fun _ : ι => f :=
    funext fun w => funext fun i => (Pi.map_apply (fun _ : ι => f) w i).symm
  rw [heq]
  exact MeasurableEmbedding.piMap fun _ => hf
