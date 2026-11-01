/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Compactness.Compact

/-!
# Locally finite projected families

Pairwise intersections of two locally finite families form a locally finite family indexed by
all pairs, including diagonal pairs. Projection from a product preserves local finiteness when
all members lie over one compact set in the second factor. No separation or local compactness
assumption on either space is needed.

These facts justify projecting a locally finite family of pairwise intersections after clipping
in a bounded vertical strip: enclose the strip in a compact interval first. Projection without
such a fibre bound need not preserve local finiteness. This is the projected-family argument in
S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
Pisa (3) 18 (1964), 449–474, §4, step II.
-/

public section

open Set Filter Topology

namespace LocallyFinite

variable {ι κ X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The pairwise intersections of two locally finite families form a locally finite family.
The index set includes all pairs, whether or not the two families are the same. -/
protected theorem inter {s : ι → Set X} {t : κ → Set X}
    (hs : LocallyFinite s) (ht : LocallyFinite t) :
    LocallyFinite fun p : ι × κ ↦ s p.1 ∩ t p.2 := by
  intro x
  obtain ⟨U, hU, hsU⟩ := hs x
  obtain ⟨V, hV, htV⟩ := ht x
  refine ⟨U ∩ V, inter_mem hU hV, (hsU.prod htV).subset ?_⟩
  rintro ⟨i, j⟩ ⟨y, ⟨hys, hyt⟩, hyU, hyV⟩
  exact ⟨⟨y, hys, hyU⟩, ⟨y, hyt, hyV⟩⟩

/-- Projection to the first factor preserves local finiteness for a family contained in a
cylinder with compact second factor. The members themselves need not be closed or compact;
in particular, they may be clipped to an open subset of the compact fibre bound. -/
theorem image_fst_of_subset {s : ι → Set (X × Y)} (hs : LocallyFinite s) {K : Set Y}
    (hK : IsCompact K) (hsub : ∀ i, s i ⊆ Prod.snd ⁻¹' K) :
    LocallyFinite fun i ↦ Prod.fst '' s i := by
  classical
  choose U hU hfin using hs
  intro x
  -- Cover the whole compact fibre by finitely many local finiteness neighbourhoods.
  obtain ⟨a, -, ha⟩ := ((isCompact_singleton (x := x)).prod hK).elim_nhds_subcover_nhdsSet
    (fun p _ ↦ hU p)
  rw [isCompact_singleton.nhdsSet_prod_eq hK, nhdsSet_singleton] at ha
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_prod_iff.mp ha
  refine ⟨V, hV, ((a.finite_toSet).biUnion fun p _ ↦ hfin p).subset ?_⟩
  rintro i ⟨y, ⟨p, hp, rfl⟩, hy⟩
  have hpW : p.2 ∈ W := subset_of_mem_nhdsSet hW (hsub i hp)
  obtain ⟨q, hqa, hpq⟩ := mem_iUnion₂.mp (hVW ⟨hy, hpW⟩)
  exact mem_biUnion hqa ⟨p, hp, hpq⟩

end LocallyFinite
