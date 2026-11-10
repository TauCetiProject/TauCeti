/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Convex sets are locally path-connected

A convex subset `s` of a real topological vector space is locally path-connected
(`Convex.locallyPathConnectedSpace'`). The neighbourhoods in `s` of a point `x ∈ s` of the form
`s ∩ (x + W)`, with `W` a balanced neighbourhood of zero, form a basis, and each of them is
star-convex about `x`, hence path-connected.

Mathlib's `Convex.locallyPathConnectedSpace` proves this for locally convex spaces only; balanced
neighbourhoods of zero exist in every real topological vector space, so local convexity is not
needed. This covers, for instance, convex subsets of the spaces `Lᵖ` with `0 < p < 1`, which are
not locally convex.
-/

public section

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E}

/-- A convex subset of a real topological vector space is locally path-connected. -/
theorem Convex.locallyPathConnectedSpace' (hs : Convex ℝ s) : LocallyPathConnectedSpace s := by
  refine .of_bases (fun x : s ↦ nhds_subtype s x ▸ map_add_left_nhds_zero x.1 ▸
    ((nhds_basis_balanced ℝ E).map (x.1 + ·)).comap ((↑) : s → E)) fun x W hW ↦ ?_
  rw [← Subtype.preimage_coe_self_inter]
  refine IsPathConnected.preimage_coe ?_ inter_subset_left
  have hW' : StarConvex ℝ x.1 ((x.1 + ·) '' W) := by
    simpa only [add_zero] using hW.2.starConvex.add_left x.1
  exact ((hs.starConvex x.2).inter hW').isPathConnected ⟨x.2, 0, mem_of_mem_nhds hW.1, add_zero _⟩
