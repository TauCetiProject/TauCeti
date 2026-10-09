/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# The standard simplex on a finite type is locally path connected

For a finite type `M`, the weights embed `StdSimplex ℝ M` onto the convex set
`stdSimplex ℝ M ⊆ M → ℝ`, and convex subsets of locally convex spaces are locally path connected.
Together with simple connectedness, this is the hypothesis under which maps out of a standard
simplex lift uniquely through covering maps (`IsCoveringMap.existsUnique_continuousMap_lifts`).
-/

public section

namespace Convexity.StdSimplex

/-- The standard simplex on a finite type is locally path connected, being homeomorphic to a
convex subset of `M → ℝ`. -/
instance locallyPathConnectedSpace (M : Type*) [Finite M] :
    LocallyPathConnectedSpace (StdSimplex ℝ M) := by
  have := Fintype.ofFinite M
  have hconv : Convex ℝ (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) := by
    rw [range_toFun_comp_weights]
    exact (convex_iInter fun i ↦ convex_halfSpace_ge (LinearMap.proj i).isLinear 0).inter
      (by simpa using
        convex_hyperplane (∑ i, LinearMap.proj (R := ℝ) (φ := fun _ : M ↦ ℝ) i).isLinear 1)
  have := hconv.locallyPathConnectedSpace
  exact (isEmbedding_toFun_comp_weights ℝ M).toHomeomorph.symm.locallyPathConnectedSpace

end Convexity.StdSimplex
