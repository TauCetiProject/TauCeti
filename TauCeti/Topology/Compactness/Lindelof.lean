/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof

/-!
# Products of Lindelöf spaces with compact spaces

The product of a Lindelöf space `X` and a compact space `Y` is Lindelöf. Each vertical slice
`{x} × Y` is compact, so it is covered by finitely many members of an open cover, and by the
tube lemma (`generalized_tube_lemma`) so is a whole tube `U × Y` around it. Countably many of
these tubes cover `X × Y`, since `X` is Lindelöf.

Products of two Lindelöf spaces need not be Lindelöf (the Sorgenfrey plane), so some
compactness assumption on one factor is needed. This is used for the levels `Xₙ × Δⁿ` of
geometric realizations, where `Δⁿ` is a topological simplex.
-/

public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product of a Lindelöf space and a compact space is Lindelöf. -/
instance LindelofSpace.prod_compactSpace [LindelofSpace X] [CompactSpace Y] :
    LindelofSpace (X × Y) where
  isLindelof_univ := isLindelof_iff_countable_subcover.2 fun U hU hcover ↦ by
    -- Each slice `{x} × Y` lies in a finite union of members of the cover, and then so does a
    -- tube `V x × Y`.
    have hslice (x : X) : ∃ (t : Finset _) (V : Set X), IsOpen V ∧ x ∈ V ∧
        V ×ˢ (univ : Set Y) ⊆ ⋃ i ∈ t, U i := by
      obtain ⟨t, ht⟩ := (isCompact_singleton.prod isCompact_univ).elim_finite_subcover U hU
        ((subset_univ _).trans hcover)
      obtain ⟨V, W, hV, -, hxV, hYW, hVW⟩ := generalized_tube_lemma isCompact_singleton
        isCompact_univ (isOpen_biUnion fun i _ ↦ hU i) ht
      exact ⟨t, V, hV, singleton_subset_iff.1 hxV, (prod_mono le_rfl hYW).trans hVW⟩
    choose t V hV hxV hVU using hslice
    obtain ⟨s, hs, hsV⟩ := LindelofSpace.elim_nhds_subcover V fun x ↦ (hV x).mem_nhds (hxV x)
    refine ⟨⋃ x ∈ s, (t x : Set _), ?_, ?_⟩
    · exact hs.biUnion fun x _ ↦ (t x).countable_toSet
    rintro ⟨x, y⟩ -
    obtain ⟨x', hx', hxV'⟩ := mem_iUnion₂.1 (hsV.symm ▸ mem_univ x)
    obtain ⟨i, hi, hiU⟩ := mem_iUnion₂.1 (hVU x' (mk_mem_prod hxV' (mem_univ y)))
    exact mem_iUnion₂.2 ⟨i, mem_iUnion₂.2 ⟨x', hx', hi⟩, hiU⟩
