/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Spectral.Prespectral

/-!
# Compact open sets between a compact set and an open set

A space is *prespectral* when its compact open sets form a basis of the topology. In such a space
every compact set `K` inside an open set `V` lies in a compact open set between them (Mathlib's
`PrespectralSpace.exists_isCompact_and_isOpen_between`), and so every compact open subset of a
subspace `Z` is cut out of `Z` by a compact open subset of the whole space.

## Main results

* `TopologicalSpace.CompactOpens.exists_preimage_subtypeVal_eq`: every compact open subset of a
  subspace is cut out by a compact open subset of the whole space.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [PrespectralSpace X]

/-- In a prespectral space, every compact open subset `K` of a subspace `Z` is cut out of `Z` by a
compact open subset of the whole space. -/
theorem TopologicalSpace.CompactOpens.exists_preimage_subtypeVal_eq {Z : Set X}
    (K : CompactOpens Z) : ∃ W : CompactOpens X, Subtype.val ⁻¹' (W : Set X) = (K : Set Z) := by
  obtain ⟨V, hV, hVK⟩ := isOpen_induced_iff.1 K.isOpen
  have hKV : Subtype.val '' (K : Set Z) ⊆ V := image_subset_iff.2 (by rw [hVK])
  obtain ⟨W, hWc, hWo, hKW, hWV⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    (K.isCompact.image continuous_subtypeVal) hV hKV
  refine ⟨⟨⟨W, hWc⟩, hWo⟩, Subset.antisymm ?_ (image_subset_iff.1 hKW)⟩
  rw [← hVK]
  exact preimage_mono hWV
