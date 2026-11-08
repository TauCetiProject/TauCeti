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
along them preserves the measure of every set, measurable or not.

The measurable equivalence `MeasurableEquiv.piFinsetUnion` has `Equiv.piFinsetUnion` as its
underlying function, so Mathlib's componentwise lemmas for the bare equivalence apply to it.

## Main results

* `MeasurableEmbedding.of_injective_of_countable`
* `MeasurableEmbedding.inl` and `MeasurableEmbedding.inr`
* `MeasurableEquiv.coe_piFinsetUnion`
-/

public section

open MeasureTheory

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

/-- The measurable equivalence `MeasurableEquiv.piFinsetUnion` has the same underlying function as
`Equiv.piFinsetUnion`; both glue a pair of assignments on disjoint finsets into one on their
union. -/
@[simp]
theorem MeasurableEquiv.coe_piFinsetUnion {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {s t : Finset ι} (h : Disjoint s t) :
    ⇑(MeasurableEquiv.piFinsetUnion α h) = Equiv.piFinsetUnion α h := rfl
