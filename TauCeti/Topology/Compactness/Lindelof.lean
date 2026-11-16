/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof

/-!
# Products of Lindelöf and compact spaces

While the product of two Lindelöf spaces need not be Lindelöf (for example the Sorgenfrey plane),
the product of a Lindelöf space with a compact space is always Lindelöf. This file proves the
subset version `IsLindelof.prod_isCompact` (and its symmetric form `IsCompact.prod_isLindelof`)
using the generalized tube lemma, together with the whole-space versions
`TauCeti.lindelofSpace_prod_of_compactSpace_right` and
`TauCeti.lindelofSpace_prod_of_compactSpace_left`.

In particular, multiplying a regular Lindelöf space by a compact Hausdorff space such as a
topological simplex yields a regular Lindelöf space, hence a normal space by Mathlib's
`NormalSpace.of_regularSpace_lindelofSpace`.

## References

* R. Engelking, *General Topology*, Revised and completed edition, Heldermann Verlag, 1989,
  Theorem 3.8.10.
-/

public section

open Set Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product of a Lindelöf set and a compact set is Lindelöf. -/
theorem IsLindelof.prod_isCompact {s : Set X} {t : Set Y} (hs : IsLindelof s) (ht : IsCompact t) :
    IsLindelof (s ×ˢ t) := by
  rw [isLindelof_iff_countable_subcover]
  intro ι U hUo hU
  -- For each `x ∈ s`, cover the compact slice `{x} × t` by finitely many members of `U`, then
  -- apply the tube lemma to thicken `{x}` to an open neighbourhood `u x`.
  have hslice (x : s) :
      ∃ (u : Set X) (v : Set Y) (f : Finset ι),
        IsOpen u ∧ x.1 ∈ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ ⋃ i ∈ f, U i := by
    obtain ⟨f, hf⟩ := (isCompact_singleton (x := x.1) |>.prod ht).elim_finite_subcover U hUo <|
      (prod_mono_left (singleton_subset_iff.2 x.2)).trans hU
    obtain ⟨u, v, huo, -, hxu, htv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton ht (isOpen_biUnion fun i _ ↦ hUo i) hf
    exact ⟨u, v, f, huo, hxu rfl, htv, huv⟩
  choose u v f huo hxu htv huv using hslice
  obtain ⟨c, hc, hsc⟩ := hs.elim_countable_subcover u huo fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxu _⟩
  refine ⟨⋃ x ∈ c, (f x : Set ι), hc.biUnion fun x _ ↦ (f x).countable_toSet, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  obtain ⟨x, hxc, hax⟩ := mem_iUnion₂.1 (hsc ha)
  obtain ⟨i, hif, hi⟩ := mem_iUnion₂.1 (huv x ⟨hax, htv x hb⟩)
  exact mem_iUnion₂.2 ⟨i, mem_iUnion₂.2 ⟨x, hxc, hif⟩, hi⟩

/-- The product of a compact set and a Lindelöf set is Lindelöf. -/
theorem IsCompact.prod_isLindelof {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsLindelof t) :
    IsLindelof (s ×ˢ t) := by
  have h : s ×ˢ t = Prod.swap '' (t ×ˢ s) := by
    ext ⟨a, b⟩
    simp
  rw [h]
  exact (ht.prod_isCompact hs).image continuous_swap

namespace TauCeti

/-- The product of a Lindelöf space with a compact space is Lindelöf. -/
theorem lindelofSpace_prod_of_compactSpace_right [LindelofSpace X] [CompactSpace Y] :
    LindelofSpace (X × Y) where
  isLindelof_univ := by
    rw [← univ_prod_univ]
    exact isLindelof_univ.prod_isCompact isCompact_univ

/-- The product of a compact space with a Lindelöf space is Lindelöf. -/
theorem lindelofSpace_prod_of_compactSpace_left [CompactSpace X] [LindelofSpace Y] :
    LindelofSpace (X × Y) where
  isLindelof_univ := by
    rw [← univ_prod_univ]
    exact isCompact_univ.prod_isLindelof isLindelof_univ

end TauCeti
