/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Spectral.Prespectral
public import Mathlib.Topology.InductiveDimension.Classes

/-!
# Compact open sets between a compact set and an open set

A space is *prespectral* when its compact open sets form a basis of the topology. In such a space
every compact set `K` inside an open set `V` lies in a compact open set between them (Mathlib's
`PrespectralSpace.exists_isCompact_and_isOpen_between`), and so every compact open subset of a
subspace `Z` is cut out of `Z` by a compact open subset of the whole space.

A locally compact zero-dimensional space is prespectral: inside a compact neighbourhood of a point,
the point has a clopen neighbourhood, which is compact as a closed subset of a compact set. In
particular this applies to *l-spaces* (Hausdorff, locally compact and totally disconnected), the
spaces of `p`-adic representation theory.

## Main results

* `PrespectralSpace.of_locallyCompactSpace_of_zeroDimensionalSpace`: locally compact
  zero-dimensional spaces are prespectral.
* `IsCompact.exists_compactOpens_between`: a compact set inside an open set lies in a compact open
  set between them.
* `TopologicalSpace.CompactOpens.exists_preimage_subtypeVal_eq`: every compact open subset of a
  subspace is cut out by a compact open subset of the whole space.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- A locally compact zero-dimensional space is prespectral: its compact open sets form a basis. -/
theorem PrespectralSpace.of_locallyCompactSpace_of_zeroDimensionalSpace [LocallyCompactSpace X]
    [ZeroDimensionalSpace X] : PrespectralSpace X := by
  refine PrespectralSpace.of_isTopologicalBasis (B := {s : Set X | IsClopen s ∧ IsCompact s})
    (isTopologicalBasis_of_isOpen_of_nhds (fun _ hs => hs.1.isOpen) fun x U hx hU => ?_)
    fun _ hs => hs.2
  obtain ⟨L, hL, hxL, hLU⟩ := exists_compact_subset hU hx
  obtain ⟨s, hs, hxs, hsL⟩ := exists_isClopen_mem_of_isOpen isOpen_interior hxL
  exact ⟨s, ⟨hs, hL.of_isClosed_subset hs.isClosed (hsL.trans interior_subset)⟩, hxs,
    hsL.trans (interior_subset.trans hLU)⟩

variable [PrespectralSpace X]

/-- In a prespectral space, a compact set `K` inside an open set `V` lies in a compact open set
between them. -/
theorem IsCompact.exists_compactOpens_between {K V : Set X} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) : ∃ W : CompactOpens X, K ⊆ W ∧ (W : Set X) ⊆ V := by
  obtain ⟨W, hWc, hWo, hKW, hWV⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between hK hV hKV
  exact ⟨⟨⟨W, hWc⟩, hWo⟩, hKW, hWV⟩

/-- In a prespectral space, every compact open subset `K` of a subspace `Z` is cut out of `Z` by a
compact open subset of the whole space. -/
theorem TopologicalSpace.CompactOpens.exists_preimage_subtypeVal_eq {Z : Set X}
    (K : CompactOpens Z) : ∃ W : CompactOpens X, Subtype.val ⁻¹' (W : Set X) = (K : Set Z) := by
  obtain ⟨V, hV, hVK⟩ := isOpen_induced_iff.1 K.isOpen
  have hKV : Subtype.val '' (K : Set Z) ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hVK] at hz
    exact hz
  obtain ⟨W, hKW, hWV⟩ :=
    (K.isCompact.image continuous_subtypeVal).exists_compactOpens_between hV hKV
  refine ⟨W, Subset.antisymm ?_ fun z hz => hKW ⟨z, hz, rfl⟩⟩
  rw [← hVK]
  exact preimage_mono hWV
