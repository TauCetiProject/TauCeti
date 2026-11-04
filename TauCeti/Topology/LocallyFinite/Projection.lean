/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyFinite.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Locally finite projected families

Projection from a product preserves local finiteness when all members lie over one compact set
in the second factor. No separation or local compactness assumption on either space is needed.

Combined with `LocallyFinite.inter` from `TauCeti.Topology.LocallyFinite.Basic`, this justifies
projecting a locally finite family of pairwise intersections after clipping
in a bounded vertical strip: enclose the strip in a compact interval first. Projection without
such a fibre bound need not preserve local finiteness. This is the projected-family argument in
S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
Pisa (3) 18 (1964), 449–474, §4, step II.
-/

public section

open Set Filter Topology

namespace LocallyFinite

variable {ι κ X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Projection to the first factor preserves local finiteness for a family contained in a
cylinder with compact second factor. The members themselves need not be closed or compact;
in particular, they may be clipped to an open subset of the compact fibre bound. -/
theorem image_fst_of_subset {s : ι → Set (X × Y)} (hs : LocallyFinite s) {K : Set Y}
    (hK : IsCompact K) (hsub : ∀ i, s i ⊆ Prod.snd ⁻¹' K) :
    LocallyFinite fun i ↦ Prod.fst '' s i := by
  intro x
  obtain ⟨W, hW, hfin⟩ := hs.exists_mem_nhdsSet_finite ((isCompact_singleton (x := x)).prod hK)
  rw [isCompact_singleton.nhdsSet_prod_eq hK, nhdsSet_singleton] at hW
  obtain ⟨V, hV, W', hW', hVW⟩ := mem_prod_iff.mp hW
  refine ⟨V, hV, hfin.subset ?_⟩
  rintro i ⟨y, ⟨p, hp, rfl⟩, hy⟩
  exact ⟨p, hp, hVW ⟨hy, subset_of_mem_nhdsSet hW' (hsub i hp)⟩⟩

end LocallyFinite
