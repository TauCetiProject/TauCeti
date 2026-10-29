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

The continuity hypothesis is essential: continuity of restrictions over an open cover of the
*target* does not, by itself, imply continuity of the original map.

## References

* N. Bourbaki, *General Topology*, Chapter I, §10 (proper mappings).
-/

public section

open Set Topology TopologicalSpace

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {U : ι → Opens Y}

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

/-- The domain of a proper map to a compact space is compact. No separation axiom is needed. -/
theorem IsProperMap.compactSpace [CompactSpace Y] (hf : IsProperMap f) : CompactSpace X := by
  refine ⟨?_⟩
  simpa only [preimage_univ] using hf.isCompact_preimage (isCompact_univ : IsCompact (univ : Set Y))
