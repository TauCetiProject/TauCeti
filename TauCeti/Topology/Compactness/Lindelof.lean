/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof

/-!
# Products of Lindelöf spaces with compact spaces

The product `s ×ˢ t` of a Lindelöf set `s : Set X` and a compact set `t : Set Y` is Lindelöf
(`IsLindelof.prod_isCompact`, and symmetrically `IsCompact.prod_isLindelof`). Each vertical slice
`{x} ×ˢ t` is compact, so it is covered by finitely many members of an open cover, and by the
tube lemma (`generalized_tube_lemma_left`) so is a whole tube `u ×ˢ t` around it. Countably many
of these tubes cover `s ×ˢ t`, since `s` is Lindelöf. Specializing to `univ` yields the
whole-space instances `LindelofSpace.prod_compactSpace` and
`TauCeti.lindelofSpace_prod_of_compactSpace_left`.

Products of two Lindelöf spaces need not be Lindelöf (the Sorgenfrey plane), so some
compactness assumption on one factor is needed. This is used for the levels `Xₙ × Δⁿ` of
geometric realizations, where `Δⁿ` is a topological simplex.

## References

* R. Engelking, *General Topology*, Revised and completed edition, Heldermann Verlag, 1989,
  Theorem 3.8.10.
-/

public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product of a Lindelöf set and a compact set is Lindelöf. -/
theorem IsLindelof.prod_isCompact {s : Set X} {t : Set Y} (hs : IsLindelof s) (ht : IsCompact t) :
    IsLindelof (s ×ˢ t) := by
  rw [isLindelof_iff_countable_subcover]
  intro ι U hUo hU
  -- For each `x ∈ s`, cover `{x} ×ˢ t` by finitely many members of `U`, then thicken `{x}` to
  -- a neighbourhood `u x hx` using `generalized_tube_lemma_left`.
  have hslice (x : X) (hx : x ∈ s) :
      ∃ (u : Set X) (f : Finset ι), u ∈ 𝓝 x ∧ u ×ˢ t ⊆ ⋃ i ∈ f, U i := by
    obtain ⟨f, hf⟩ :=
      (isCompact_singleton (x := x) |>.prod ht).elim_finite_subcover U hUo <|
        (prod_mono_left (singleton_subset_iff.2 hx)).trans hU
    obtain ⟨u, hu, huf⟩ := generalized_tube_lemma_left isCompact_singleton ht (s' := univ) <|
      Filter.mem_inf_of_left ((isOpen_biUnion fun i _ ↦ hUo i).mem_nhdsSet.2 hf)
    rw [nhdsSetWithin_univ, nhdsSet_singleton] at hu
    exact ⟨u, f, hu, huf⟩
  choose u f hu huf using hslice
  obtain ⟨c, hc, hsc⟩ := hs.elim_nhds_subcover' u hu
  refine ⟨⋃ x ∈ c, (f x.val x.property : Set ι),
    hc.biUnion fun x _ ↦ (f x.val x.property).countable_toSet, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  obtain ⟨x, hxc, hax⟩ := mem_iUnion₂.1 (hsc ha)
  obtain ⟨i, hif, hi⟩ := mem_iUnion₂.1 (huf x.val x.property ⟨hax, hb⟩)
  exact mem_iUnion₂.2 ⟨i, mem_iUnion₂.2 ⟨x, hxc, hif⟩, hi⟩

/-- The product of a compact set and a Lindelöf set is Lindelöf. -/
theorem IsCompact.prod_isLindelof {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsLindelof t) :
    IsLindelof (s ×ˢ t) := by
  rw [← Set.image_swap_prod t s]
  exact (ht.prod_isCompact hs).image continuous_swap

/-- The product of a Lindelöf space and a compact space is Lindelöf. -/
instance LindelofSpace.prod_compactSpace [LindelofSpace X] [CompactSpace Y] :
    LindelofSpace (X × Y) where
  isLindelof_univ := by
    rw [← univ_prod_univ]
    exact isLindelof_univ.prod_isCompact isCompact_univ

/-- The product of a compact space and a Lindelöf space is Lindelöf. -/
instance TauCeti.lindelofSpace_prod_of_compactSpace_left [CompactSpace X] [LindelofSpace Y] :
    LindelofSpace (X × Y) where
  isLindelof_univ := by
    rw [← univ_prod_univ]
    exact isCompact_univ.prod_isLindelof isLindelof_univ
