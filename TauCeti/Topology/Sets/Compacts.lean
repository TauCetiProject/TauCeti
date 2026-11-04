/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Preimages of compact sets under proper maps

The preimage of a compact set under a proper map is compact
(`IsProperMap.isCompact_preimage`). This file packages that as the map
`TopologicalSpace.Compacts.comap f hf : Compacts β → Compacts α` for a proper map `f : α → β`,
monotone and functorial in `f`. It is the operation through which the cohomology with compact
supports of a space, a colimit over its compact subsets, is contravariant in proper maps.
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

end TopologicalSpace.Compacts
