/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Lie.Basic
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Subgroups that are manifolds are closed

A subgroup `K` of a Lie group `G` which, for the subspace topology, is a manifold modelled on a
finite-dimensional real vector space is locally compact, and a locally compact subgroup of a
Hausdorff topological group is closed. In particular a subgroup which is a finite-dimensional Lie
group for the subspace topology is closed (`TauCeti.Lie.isClosed_of_lieGroup`). This is the
converse of Cartan's closed-subgroup theorem (`TauCeti.Lie.isEmbeddedLieSubgroup_of_isClosed`).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.Lie

variable {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
  {HK : Type*} [TopologicalSpace HK] (IK : ModelWithCorners ℝ EK HK)
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners ℝ EG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] {K : Subgroup G}
  [ChartedSpace HK K]

include IK in
/-- A subgroup of a Lie group which, for the subspace topology, is a manifold modelled on a
finite-dimensional space is closed, being locally compact. This applies to a subgroup which is a
finite-dimensional Lie group for the subspace topology. -/
theorem isClosed_of_lieGroup [FiniteDimensional ℝ EK] [LieGroup IG ∞ G] :
    IsClosed (K : Set G) :=
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup IG ∞
  let _ : T2Space G := IG.t2Space_of_lieGroup ∞
  let _ : LocallyCompactSpace HK := IK.locallyCompactSpace
  let _ : LocallyCompactSpace K := ChartedSpace.locallyCompactSpace HK K
  K.isClosed_of_weaklyLocallyCompactSpace

end TauCeti.Lie
