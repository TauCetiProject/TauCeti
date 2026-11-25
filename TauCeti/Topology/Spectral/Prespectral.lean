/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Spectral.Prespectral
public import Mathlib.Topology.InductiveDimension.Classes

/-!
# Locally compact zero-dimensional spaces are prespectral

A space is *prespectral* when its compact open sets form a basis of the topology. A locally compact
zero-dimensional space is prespectral: inside a compact neighbourhood of a point, the point has a
clopen neighbourhood, which is compact as a closed subset of a compact set. In particular this
applies to *l-spaces* (Hausdorff, locally compact and totally disconnected), the spaces of `p`-adic
representation theory.

## Main results

* `PrespectralSpace.of_locallyCompactSpace_of_zeroDimensionalSpace`: locally compact
  zero-dimensional spaces are prespectral.
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
