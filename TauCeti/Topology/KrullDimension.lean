/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Krull dimension of topological spaces: open covers and closed points

This file records two facts about the topological Krull dimension and the codimension of points.

The Krull dimension of a space is the supremum of the Krull dimensions of the members of an open
cover: an irreducible closed subset meeting an open subset `U` is the closure of its trace on `U`,
so every chain of irreducible closed subsets of the whole space restricts to a chain of the same
length in any open subset containing a point of its smallest member. For schemes this is what
reduces dimension computations to affine opens.

On a T₀ topological space the specialization order is a partial order, so the codimension
`Order.coheight x` of a point is defined: it is the supremum of the lengths of the chains of
proper specializations of `x`. On a space all of whose points have codimension at most one, a
point of codimension exactly one is closed, since a proper specialization of such a point would
have codimension at least two.

## Main declarations

* `TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding`: the Krull dimension of a space
  covered by the ranges of open embeddings is the supremum of the Krull dimensions of their
  domains.
* `TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one`: on a T₀ space all
  of whose points have codimension at most one for the specialization order, a point of
  codimension one is closed.
-/

public section

open Order Topology TopologicalSpace

namespace TauCeti

/-- The Krull dimension of a space covered by the ranges of a family of open embeddings is the
supremum of the Krull dimensions of their domains. -/
theorem topologicalKrullDim_eq_iSup_of_isOpenEmbedding {X ι : Type*} [TopologicalSpace X]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcover : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  refine le_antisymm (iSup_le fun p ↦ ?_) (iSup_le fun i ↦ (hf i).isInducing.topologicalKrullDim_le)
  -- A point `f i y` of the smallest member of the chain `p` lies in every member, so `p` is a
  -- chain of irreducible closed sets meeting the range of `f i`, hence comes from `Y i`.
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨i, y, rfl⟩ := hcover x
  let q : LTSeries {V : IrreducibleCloseds X | ((f i) ⁻¹' V).Nonempty} :=
    ⟨p.length, fun j ↦ ⟨p j, y, p.monotone (Fin.zero_le j) hx⟩, fun j ↦ p.step j⟩
  exact le_iSup_of_le i (q.map _
    (IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)).symm.strictMono).length_le_krullDim

attribute [local instance] specializationOrder in
/-- On a T₀ topological space all of whose points have codimension at most one for the
specialization order, a point of codimension one is closed. -/
theorem isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one {α : Type*}
    [TopologicalSpace α] [T0Space α]
    (hdim : ∀ y : α, coheight y ≤ 1) {x : α} (hx : coheight x = 1) :
    IsClosed ({x} : Set α) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) subset_closure
  -- `y ∈ closure {x}` says `x ⤳ y`, which is exactly `y ≤ x` in the specialization order; a
  -- strict such `y` would be a proper specialization of `x`, hence of codimension at least two.
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  rcases eq_or_ne y x with rfl | hne
  · exact Set.mem_singleton _
  refine absurd (hdim y) (not_le.mpr ?_)
  simpa [hx] using Order.coheight_strictAnti (lt_of_le_of_ne hyx hne) (by simp [hx])

end TauCeti
