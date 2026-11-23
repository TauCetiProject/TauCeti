/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The Borel σ-algebra of a disjoint union

The σ-algebra of a disjoint union `α ⊕ β` of measurable spaces consists of the sets whose
preimages under both inclusions are measurable. When `α` and `β` carry their Borel σ-algebras,
this is the Borel σ-algebra of the disjoint union topology: open sets have open preimages, and the
inclusions are open embeddings, so they map Borel sets to Borel sets.

Adapted from Giada Franz's formalization in the `ForTauCeti` module.

## Main results

* `Sum.borelSpace`: a disjoint union of Borel spaces is a Borel space.
-/

public section

open MeasureTheory Set Topology

variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]

/-- A disjoint union of Borel spaces is a Borel space. -/
instance Sum.borelSpace : BorelSpace (α ⊕ β) := by
  refine ⟨le_antisymm (fun s hs ↦ ?_) (MeasurableSpace.generateFrom_le fun s hs ↦
    ⟨(hs.preimage continuous_inl).measurableSet, (hs.preimage continuous_inr).measurableSet⟩)⟩
  let _ : MeasurableSpace (α ⊕ β) := borel (α ⊕ β)
  have : BorelSpace (α ⊕ β) := ⟨rfl⟩
  rw [← Set.image_preimage_inl_union_image_preimage_inr s]
  exact ((IsOpenEmbedding.inl (X := α) (Y := β)).measurableEmbedding.measurableSet_image.2
    hs.1).union ((IsOpenEmbedding.inr (X := α) (Y := β)).measurableEmbedding.measurableSet_image.2
      hs.2)
