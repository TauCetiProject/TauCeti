/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Cover.Basic
public import TauCeti.Geometry.Manifold.Topology
public import TauCeti.Topology.VectorBundle.Orientation.Cover.FundamentalGroup

/-!
# Orientability from the fundamental group

A connected manifold is orientable if its fundamental group has no subgroup of index two.
This is the tangent-bundle case of
`TauCeti.VectorBundleOrientation.nonempty_of_forall_index_ne_two`.
In particular, simply connected manifolds are orientable, including manifolds with boundary or
corners. No separation assumption on the manifold is needed.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218, Springer, 2013,
  Chapter 15, The Orientation Covering.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.32
  (the number of sheets is the index of the induced subgroup).
-/

public section

noncomputable section

namespace TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A connected manifold whose fundamental group has no subgroup of index two is orientable.
No separation assumption on the manifold is needed. -/
theorem orientable_of_forall_index_ne_two [ConnectedSpace M] (x : M)
    (hπ : ∀ G : Subgroup (FundamentalGroup M x), G.index ≠ 2) : Orientable I M := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  exact orientable_iff_nonempty_vectorBundleOrientation.mpr
    (VectorBundleOrientation.nonempty_of_forall_index_ne_two (Fintype.card_fin _) x hπ)

/-- A simply connected manifold, including one with boundary or corners, is orientable. -/
instance orientable_of_simplyConnectedSpace [SimplyConnectedSpace M] : Orientable I M := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  exact orientable_iff_nonempty_vectorBundleOrientation.mpr
    (VectorBundleOrientation.nonempty_of_simplyConnectedSpace (Fintype.card_fin _))

end TauCeti.Manifold
