/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof

/-!
# Products of Lindelöf spaces with compact spaces

The product of a Lindelöf set with a compact set is Lindelöf (`IsLindelof.prod_isCompact`), and
in particular the product of a Lindelöf space `X` and a compact space `Y` is Lindelöf
(`LindelofSpace.prod_compactSpace`). Each vertical slice `{x} × t` is compact, so it is covered
by finitely many members of an open cover, and by the tube lemma (`generalized_tube_lemma`) so is
a whole tube `V × t` around it. Countably many of these tubes cover `s × t`, since `s` is
Lindelöf.

Products of two Lindelöf spaces need not be Lindelöf (the Sorgenfrey plane), so some
compactness assumption on one factor is needed. This is used for the levels `Xₙ × Δⁿ` of
geometric realizations, where `Δⁿ` is a topological simplex.
-/

public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product of a Lindelöf set with a compact set is Lindelöf. -/
theorem IsLindelof.prod_isCompact {s : Set X} {t : Set Y} (hs : IsLindelof s) (ht : IsCompact t) :
    IsLindelof (s ×ˢ t) := by
  refine isLindelof_of_countable_subcover fun {ι} U hUo hU ↦ ?_
  have htube (x : X) (hx : x ∈ s) :
      ∃ (F : Finset ι) (V : Set X), IsOpen V ∧ x ∈ V ∧ V ×ˢ t ⊆ ⋃ i ∈ F, U i := by
    have hK : IsCompact ({x} ×ˢ t) := isCompact_singleton.prod ht
    have hKsub : {x} ×ˢ t ⊆ ⋃ i, U i :=
      subset_trans (prod_mono (singleton_subset_iff.2 hx) Subset.rfl) hU
    obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hUo hKsub
    obtain ⟨V, W, hVo, _, hxV, hW, hVW⟩ := generalized_tube_lemma isCompact_singleton ht
      (isOpen_biUnion fun i _ ↦ hUo i) hF
    exact ⟨F, V, hVo, hxV rfl, fun p hp ↦ hVW ⟨hp.1, hW hp.2⟩⟩
  choose! F V hVo hxV hFV using htube
  obtain ⟨c, hcs, hc, hcover⟩ := hs.elim_countable_subcover_image (fun x hx ↦ hVo x hx)
    (fun x hx ↦ mem_biUnion hx (hxV x hx))
  refine ⟨⋃ x ∈ c, (F x : Set ι), hc.biUnion fun x _ ↦ (F x).countable_toSet, ?_⟩
  rintro ⟨x, y⟩ ⟨hxs, hyt⟩
  obtain ⟨x₀, hx₀c, hxV₀⟩ := mem_iUnion₂.1 (hcover hxs)
  obtain ⟨i, hiF, hiU⟩ := mem_iUnion₂.1 (hFV x₀ (hcs hx₀c) (a := (x, y)) ⟨hxV₀, hyt⟩)
  exact mem_iUnion₂.2 ⟨i, mem_iUnion₂.2 ⟨x₀, hx₀c, hiF⟩, hiU⟩

/-- The product of a Lindelöf space and a compact space is Lindelöf. -/
instance LindelofSpace.prod_compactSpace [LindelofSpace X] [CompactSpace Y] :
    LindelofSpace (X × Y) :=
  ⟨by simpa only [univ_prod_univ] using isLindelof_univ.prod_isCompact isCompact_univ⟩
