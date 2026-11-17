/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
public import TauCeti.Topology.Homotopy.LocallyEquiconnected.Basic

/-!
# Compact manifolds are locally equiconnected

A compact Hausdorff boundaryless smooth manifold `M` embeds in a Euclidean space `ℝⁿ` (Whitney),
and the embedding has a smooth retraction `r` on an open neighbourhood of its image (tubular
neighbourhood theorem). So `M` is a neighbourhood retract of `ℝⁿ`, and nearby points `x, y ∈ M`
are joined by the projection `t ↦ r ((1 - t) x + t y)` of the straight segment between them:
`M` is locally equiconnected (`Manifold.locallyEquiconnectedSpace`).

Consequently every mapping space `C(K, M)` out of a compact, locally compact space `K` (which
supplies the `LocallyCompactPair K M` hypothesis), for instance the free loop space of a closed
manifold (`K = S¹`) and its subspace of contractible loops, is locally equiconnected,
hence locally path-connected and semilocally simply connected
(`TauCeti.Topology.Homotopy.LocallyEquiconnected.MappingSpace`).

## References

* J. Dugundji, *Locally equiconnected spaces and absolute neighborhood retracts*, Fund. Math. 57
  (1965), 187–193.
-/

public section

open Set
open scoped ContDiff Manifold

/-- A compact Hausdorff boundaryless smooth manifold is locally equiconnected: it is a
neighbourhood retract of a Euclidean space. -/
theorem Manifold.locallyEquiconnectedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] : TauCeti.LocallyEquiconnectedSpace M := by
  rcases isEmpty_or_nonempty M with _ | _
  · infer_instance
  obtain ⟨n, ⟨f⟩⟩ := TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact (I := I) (M := M)
  obtain ⟨W, hW, hfW, -, r, hr, hrf⟩ := f.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  exact .of_retract (map_continuous f) hW hfW hr.continuousOn hrf
