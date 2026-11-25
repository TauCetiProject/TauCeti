/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocalAtTarget

/-!
# Properness is local on the target

A continuous map is proper if and only if its restrictions over an open cover of the target
are proper. This allows properness of maps into spaces assembled from open pieces to be checked
piecewise. The cover need not be finite, and neither space needs a separation axiom.

We use Mathlib's characterization of proper maps as continuous closed maps with compact fibres.
Closedness is already local on the target; each fibre is homeomorphic to the corresponding
fibre of a restriction. In particular, this argument does not require local compactness or a
compactly generated target, as a characterization using compact preimages alone would.

The pieces of the target are often given as embeddings `j : Y' → Y` rather than as subsets, with a
map `f' : X' → Y'` identified with the pullback of `f` along `j`. If `f'` is proper, so is the
restriction of `f` over the range of `j` (`IsProperMap.restrictPreimage_range_of_isEmbedding`).

The continuity hypothesis is essential: continuity of restrictions over an open cover of the
*target* does not, by itself, imply continuity of the original map.

## References

* N. Bourbaki, *General Topology*, Chapter I, §10 (proper mappings).
-/

public section

open Set Topology TopologicalSpace

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {U : ι → Opens Y}

/-- **The restriction of a map over the range of an embedding is proper when its pullback is.**
If `f ∘ i = j ∘ f'`, where `i` and `j` are embeddings and the range of `i` is the preimage under
`f` of the range of `j`, and `f'` is proper, then the restriction of `f` over the range of `j` is
proper. This is a converse of `IsProperMap.of_isEmbedding_of_range_eq`. -/
theorem IsProperMap.restrictPreimage_range_of_isEmbedding {X' Y' : Type*} [TopologicalSpace X']
    [TopologicalSpace Y'] {f' : X' → Y'} {i : X' → X} {j : Y' → Y} (hf' : IsProperMap f')
    (hi : IsEmbedding i) (hj : IsEmbedding j) (hcomm : f ∘ i = j ∘ f')
    (hrange : range i = f ⁻¹' range j) : IsProperMap ((range j).restrictPreimage f) := by
  let ei : X' ≃ₜ f ⁻¹' range j := hi.toHomeomorph.trans (.setCongr hrange)
  have h : (range j).restrictPreimage f = hj.toHomeomorph ∘ f' ∘ ei.symm := by
    funext x
    obtain ⟨x', rfl⟩ := ei.surjective x
    apply Subtype.ext
    simpa [ei, Homeomorph.setCongr] using congrFun hcomm x'
  rw [h]
  exact hj.toHomeomorph.isProperMap.comp (hf'.comp ei.symm.isProperMap)

/-- Properness of a continuous map can be checked over any open cover of its target.
No finiteness or separation hypothesis is needed. -/
theorem TopologicalSpace.IsOpenCover.isProperMap_iff_restrictPreimage
    (hU : IsOpenCover U) (hf : Continuous f) :
    IsProperMap f ↔ ∀ i, IsProperMap ((U i : Set Y).restrictPreimage f) := by
  refine ⟨fun h i ↦ h.restrictPreimage _, fun h ↦ ?_⟩
  refine isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, hU.isClosedMap_iff_restrictPreimage.2 (fun i ↦ (h i).isClosedMap), fun y ↦ ?_⟩
  obtain ⟨i, hy⟩ := hU.exists_mem y
  have hK := (h i).isCompact_preimage (isCompact_singleton (x := (⟨y, hy⟩ : U i)))
  rw [IsEmbedding.subtypeVal.isCompact_iff, image_val_preimage_restrictPreimage,
    image_singleton] at hK
  exact hK

/-- A continuous map is proper if, around each target point, its restriction over some open
neighbourhood is proper. The neighbourhoods need not form a locally finite family. -/
theorem Continuous.isProperMap_of_locally (hf : Continuous f)
    (h : ∀ y : Y, ∃ V : Opens Y, y ∈ V ∧ IsProperMap ((V : Set Y).restrictPreimage f)) :
    IsProperMap f := by
  choose V hy hV using h
  have hcover : IsOpenCover V := IsOpenCover.of_sets (fun y ↦ (V y).isOpen)
    (iUnion_eq_univ_iff.2 fun y ↦ ⟨y, hy y⟩)
  exact (hcover.isProperMap_iff_restrictPreimage hf).2 hV
