/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# `Gδ` sets under inducing maps and topological embeddings

An inducing map `f : X → Y` whose range is a `Gδ` set in `Y` maps `Gδ` sets in `X` to `Gδ` sets in
`Y`. When `f` is a topological embedding with `Gδ` range—in particular when `f` is an open
embedding—a subset `s ⊆ X` is a `Gδ` set if and only if its image `f '' s` is a `Gδ` set in `Y`.

## Main results

* `Topology.IsInducing.isGδ_image`: an inducing map with `Gδ` range maps `Gδ` sets to `Gδ` sets.
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

/-- An inducing map whose range is a `Gδ` set maps `Gδ` sets to `Gδ` sets. -/
theorem IsInducing.isGδ_image (hf : IsInducing f) (hr : IsGδ (range f)) {s : Set X} (hs : IsGδ s) :
    IsGδ (f '' s) := by
  obtain ⟨U, hUo, rfl⟩ := hs.eq_iInter_nat
  choose V hVo hVU using fun n => hf.isOpen_iff.1 (hUo n)
  simp_rw [← hVU, ← preimage_iInter, image_preimage_eq_inter_range]
  exact (IsGδ.iInter_of_isOpen hVo).inter hr

/-- Under an embedding whose range is a `Gδ` set, a set is `Gδ` if and only if its image is `Gδ`. -/
theorem IsEmbedding.isGδ_iff_image_isGδ (hf : IsEmbedding f) (hr : IsGδ (range f)) {s : Set X} :
    IsGδ s ↔ IsGδ (f '' s) where
  mp := hf.isInducing.isGδ_image hr
  mpr hs := by
    simpa only [preimage_image_eq _ hf.injective] using hs.preimage hf.continuous

/-- Under an open embedding, a set is `Gδ` if and only if its image is `Gδ`. -/
theorem IsOpenEmbedding.isGδ_iff_image_isGδ (hf : IsOpenEmbedding f) {s : Set X} :
    IsGδ s ↔ IsGδ (f '' s) :=
  hf.isEmbedding.isGδ_iff_image_isGδ hf.isOpen_range.isGδ

/-- An open embedding maps `Gδ` sets to `Gδ` sets. -/
theorem IsOpenEmbedding.isGδ_image (hf : IsOpenEmbedding f) {s : Set X} (hs : IsGδ s) :
    IsGδ (f '' s) :=
  hf.isInducing.isGδ_image hf.isOpen_range.isGδ hs

end Topology
