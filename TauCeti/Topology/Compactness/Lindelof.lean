/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof

/-!
# Products of Lindelöf sets and compact sets

The product of a Lindelöf set and a compact set is Lindelöf (`IsLindelof.prod_of_isCompact`,
`IsCompact.prod_isLindelof`), with no separation assumptions, via the generalized tube lemma
(`generalized_tube_lemma`), giving `LindelofSpace.prod_compactSpace` and
`TauCeti.instLindelofSpaceProdOfCompactSpaceLeft`.

Products of two Lindelöf spaces need not be Lindelöf (the Sorgenfrey plane), so some
compactness assumption on one factor is needed. This is used for the levels `Xₙ × Δⁿ` of
geometric realizations, where `Δⁿ` is a topological simplex.

## References

* R. Engelking, *General Topology*, Heldermann Verlag, 1989, Theorem 3.8.9.
-/

public section

open Set Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The product of a Lindelöf set and a compact set is Lindelöf.** -/
theorem IsLindelof.prod_of_isCompact {s : Set X} {t : Set Y} (hs : IsLindelof s)
    (ht : IsCompact t) : IsLindelof (s ×ˢ t) := by
  refine isLindelof_of_countable_subcover fun {ι} U hUo hcov ↦ ?_
  have hslice (x : s) : ∃ F : Finset ι, ∃ V : Set X,
      IsOpen V ∧ (x : X) ∈ V ∧ V ×ˢ t ⊆ ⋃ i ∈ F, U i := by
    obtain ⟨F, hF⟩ := (isCompact_singleton (x := (x : X)).prod ht).elim_finite_subcover U hUo
      ((prod_mono (singleton_subset_iff.2 x.property) Subset.rfl).trans hcov)
    obtain ⟨V, _, hVo, -, hxV, hWt, hsub⟩ :=
      generalized_tube_lemma isCompact_singleton ht (isOpen_biUnion fun i _ ↦ hUo i) hF
    exact ⟨F, V, hVo, singleton_subset_iff.1 hxV, (prod_mono Subset.rfl hWt).trans hsub⟩
  choose F V hVo hxV hFV using hslice
  obtain ⟨C, hCc, hCs⟩ := hs.elim_countable_subcover V hVo
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  refine ⟨⋃ x ∈ C, (F x : Set ι), hCc.biUnion fun x _ ↦ (F x).countable_toSet, ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨z, hzC, hxz⟩ := mem_iUnion₂.1 (hCs hx)
  obtain ⟨i, hiF, hxy⟩ := mem_iUnion₂.1 (hFV z ⟨hxz, hy⟩)
  exact mem_iUnion₂.2 ⟨i, mem_iUnion₂.2 ⟨z, hzC, hiF⟩, hxy⟩

/-- **The product of a compact set and a Lindelöf set is Lindelöf.** -/
theorem IsCompact.prod_isLindelof {s : Set X} {t : Set Y} (hs : IsCompact s)
    (ht : IsLindelof t) : IsLindelof (s ×ˢ t) :=
  image_swap_prod (s := t) (t := s) ▸ (ht.prod_of_isCompact hs).image continuous_swap

/-- The product of a Lindelöf space and a compact space is Lindelöf. -/
instance LindelofSpace.prod_compactSpace [LindelofSpace X] [CompactSpace Y] :
    LindelofSpace (X × Y) where
  isLindelof_univ := univ_prod_univ ▸ isLindelof_univ.prod_of_isCompact isCompact_univ

namespace TauCeti

/-- The product of a compact space and a Lindelöf space is Lindelöf. -/
instance (priority := 100) instLindelofSpaceProdOfCompactSpaceLeft [CompactSpace X]
    [LindelofSpace Y] : LindelofSpace (X × Y) where
  isLindelof_univ := univ_prod_univ ▸ isCompact_univ.prod_isLindelof isLindelof_univ

end TauCeti
