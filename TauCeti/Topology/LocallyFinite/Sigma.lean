/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite

/-!
# Locally finite families on disjoint unions

Locally finite families on the summands of a topological disjoint union combine into one locally
finite family, even when neither the set of summands nor the individual families are finite.
-/

public section

open Set Topology

/-- The union of locally finite families in the summands of a disjoint union is locally finite,
with the family indexed by the disjoint union of the original index types. -/
theorem LocallyFinite.sigmaMk_image {ι : Type*} {X I : ι → Type*}
    [∀ i, TopologicalSpace (X i)] {s : ∀ i, I i → Set (X i)}
    (hs : ∀ i, LocallyFinite (s i)) :
    LocallyFinite fun j : Σ i, I i ↦ Sigma.mk j.1 '' s j.1 j.2 := by
  rintro ⟨i, x⟩
  obtain ⟨U, hU, hfin⟩ := hs i x
  refine ⟨Sigma.mk i '' U, IsOpenEmbedding.sigmaMk.image_mem_nhds.mpr hU,
    (hfin.image (Sigma.mk i)).subset ?_⟩
  rintro ⟨j, a⟩ ⟨_, ⟨y, hy, rfl⟩, z, hz, he⟩
  obtain rfl : i = j := congrArg Sigma.fst he
  have hzy : z = y := sigma_mk_injective he
  exact ⟨a, ⟨y, hy, hzy ▸ hz⟩, rfl⟩
