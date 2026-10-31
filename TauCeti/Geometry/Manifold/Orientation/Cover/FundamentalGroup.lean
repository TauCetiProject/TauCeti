/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Cover.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Orientability from the fundamental group

A connected, locally path-connected manifold is orientable if its fundamental group has no
subgroup of index two. Indeed, otherwise its orientation cover is connected, and the image of
the fundamental group of that cover has index equal to its number of sheets, namely two.
In particular, simply connected, locally path-connected manifolds are orientable.

Local path connectedness is explicit so that the result applies to arbitrary models with
corners without imposing a boundaryless or Hausdorff hypothesis. The usual Euclidean,
half-space and quadrant models are locally path connected.

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
  [LocallyPathConnectedSpace M]

/-- A connected manifold whose fundamental group has no subgroup of index two is orientable.
No separation assumption on the manifold is needed. -/
theorem orientable_of_forall_index_ne_two [ConnectedSpace M] (x : M)
    (hπ : ∀ G : Subgroup (FundamentalGroup M x), G.index ≠ 2) : Orientable I M := by
  apply OrientationCover.orientable_iff_not_connectedSpace.mpr
  intro hc
  have : ConnectedSpace (OrientationCover I M) := hc
  have hp := OrientationCover.isCoveringMap_proj I M
  have : LocallyPathConnectedSpace (OrientationCover I M) :=
    hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace (OrientationCover I M) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨p, hp₀⟩ := VectorBundleOrientationCover.surjective_proj
    (F := E) (E := TangentSpace I (M := M)) (Fintype.card_fin _) x
  have hcard := hp.card_fiber_eq_index ⟨p, hp₀⟩
  rw [Nat.card_coe_set_eq,
    VectorBundleOrientationCover.ncard_fiber (Fintype.card_fin _)] at hcard
  exact hπ _ hcard.symm

/-- A simply connected, locally path-connected manifold is orientable, including manifolds
with boundary or corners. -/
theorem orientable_of_simplyConnectedSpace [SimplyConnectedSpace M] : Orientable I M := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  apply orientable_of_forall_index_ne_two x
  intro G hG
  have hindex : G.index = 1 := by
    rw [Subsingleton.elim G ⊤, Subgroup.index_top]
  omega

end TauCeti.Manifold
