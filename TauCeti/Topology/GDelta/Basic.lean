/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# `Gδ` sets under topological embeddings

Under a topological embedding `f : X → Y` whose range is a `Gδ` set in `Y`—in particular under any
open embedding—a subset `s ⊆ X` is a `Gδ` set if and only if its image `f '' s` is a `Gδ` set in
`Y`.

## Main results

* `Topology.IsEmbedding.isGδ_iff_image_isGδ`: under an embedding with `Gδ` range, `s` is `Gδ` if and
  only if `f '' s` is `Gδ`.
* `Topology.IsOpenEmbedding.isGδ_iff_image_isGδ` and `Topology.IsOpenEmbedding.isGδ_image`:
  specialization to open embeddings, complementing
  `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`.
-/

public section

open Set

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- Under an embedding whose range is a `Gδ` set, a set is `Gδ` if and only if its image is `Gδ`. -/
theorem IsEmbedding.isGδ_iff_image_isGδ (hf : IsEmbedding f) (hr : IsGδ (range f)) {s : Set X} :
    IsGδ s ↔ IsGδ (f '' s) where
  mp hs := by
    obtain ⟨U, hUo, rfl⟩ := hs.eq_iInter_nat
    choose V hVo hVU using fun n => hf.isInducing.image_eq_isOpen_inter_range (hUo n)
    rw [hf.injective.injOn.image_iInter_eq]
    simp_rw [hVU]
    exact IsGδ.iInter fun n => (hVo n).isGδ.inter hr
  mpr hs := by
    simpa only [preimage_image_eq _ hf.injective] using hs.preimage hf.continuous

/-- Under an open embedding, a set is `Gδ` if and only if its image is `Gδ`. -/
theorem IsOpenEmbedding.isGδ_iff_image_isGδ (hf : IsOpenEmbedding f) {s : Set X} :
    IsGδ s ↔ IsGδ (f '' s) :=
  hf.isEmbedding.isGδ_iff_image_isGδ hf.isOpen_range.isGδ

/-- An open embedding maps `Gδ` sets to `Gδ` sets. -/
theorem IsOpenEmbedding.isGδ_image (hf : IsOpenEmbedding f) {s : Set X} (hs : IsGδ s) :
    IsGδ (f '' s) :=
  hf.isGδ_iff_image_isGδ.1 hs

end Topology
