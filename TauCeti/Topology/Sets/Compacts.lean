/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Images and preimages of compact sets

The preimage of a compact set under a proper map is compact
(`IsProperMap.isCompact_preimage`). This file packages that as the map
`TopologicalSpace.Compacts.comap f hf : Compacts β → Compacts α` for a proper map `f : α → β`,
monotone and functorial in `f`. It is the operation through which the cohomology with compact
supports of a space, a colimit over its compact subsets, is contravariant in proper maps. It also
records that Mathlib's image `TopologicalSpace.Compacts.map` is monotone, which makes cohomology
with compact supports covariant in open embeddings. Finally, a compact set lies in one member of a
directed open cover (`TopologicalSpace.Compacts.exists_subset_of_iSup_eq_top`).
-/

public section

open Set

namespace TopologicalSpace.Compacts

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- The preimage of a compact set under a proper map, as a compact set. -/
protected def comap (f : α → β) (hf : IsProperMap f) (K : Compacts β) : Compacts α :=
  ⟨f ⁻¹' K, hf.isCompact_preimage K.isCompact⟩

@[simp, norm_cast]
lemma coe_comap (f : α → β) (hf : IsProperMap f) (K : Compacts β) :
    (Compacts.comap f hf K : Set α) = f ⁻¹' K :=
  (rfl)

@[simp]
lemma mem_comap {f : α → β} {hf : IsProperMap f} {K : Compacts β} {x : α} :
    x ∈ Compacts.comap f hf K ↔ f x ∈ K :=
  Iff.rfl

lemma comap_mono (f : α → β) (hf : IsProperMap f) : Monotone (Compacts.comap f hf) :=
  fun _ _ h ↦ preimage_mono h

@[simp]
lemma comap_id (K : Compacts α) : Compacts.comap id isProperMap_id K = K :=
  (rfl)

lemma comap_comp (f : α → β) (g : β → γ) (hf : IsProperMap f) (hg : IsProperMap g)
    (K : Compacts γ) :
    Compacts.comap (g ∘ f) (hg.comp hf) K = Compacts.comap f hf (Compacts.comap g hg K) :=
  (rfl)

/-- The image of compact sets under a continuous map is monotone. -/
lemma map_mono (f : α → β) (hf : Continuous f) : Monotone (Compacts.map f hf) :=
  fun _ _ h ↦ image_mono h

/-- A compact set lies in one member of a directed family of open sets covering the space. -/
lemma exists_subset_of_iSup_eq_top {ι : Type*} [Nonempty ι] {U : ι → Opens α}
    (hU : Directed (· ≤ ·) U) (hcover : ⨆ i, U i = ⊤) (K : Compacts α) :
    ∃ i, (K : Set α) ⊆ U i :=
  K.isCompact.elim_directed_cover (fun i ↦ (U i : Set α)) (fun i ↦ (U i).isOpen)
    (fun x _ ↦ by simp [← Opens.coe_iSup, hcover]) (hU.mono_comp _ fun _ _ h ↦ h)

end TopologicalSpace.Compacts
