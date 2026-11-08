/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Covering.Basic
import TauCeti.Topology.Algebra.Group.Covering
import TauCeti.Topology.Algebra.Group.Preconnected
import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.Homotopy.Covering
import TauCeti.Geometry.Manifold.Topology

/-!
# Lie homomorphisms with invertible differential

A smooth homomorphism with bijective Lie map is a local diffeomorphism at every point.
If its target is preconnected, it is a covering map. If its source is preconnected and its
target is simply connected, it is bijective. These are the local-isomorphism criteria used
when integrating Lie-algebra homomorphisms by graph subgroups.

## Main results

* `ContMDiffMonoidMorphism.isCoveringMap_of_lieMap_bijective`: the covering criterion.
* `ContMDiffMonoidMorphism.bijective_of_lieMap_bijective_of_simplyConnectedSpace`: the
  bijectivity criterion over a simply connected target.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Exercise 2.3, for the covering-map assertion.
-/

public section

open Function Manifold Topology Set
open scoped ContDiff Manifold

noncomputable section

namespace ContMDiffMonoidMorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K] [LieGroup J ∞ K]

/-- A smooth homomorphism with bijective Lie map onto a preconnected target is a covering map. -/
theorem isCoveringMap_of_lieMap_bijective [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [PreconnectedSpace K] (f : ContMDiffMonoidMorphism I J ∞ G K)
    (hf : Bijective (lieMap f)) : IsCoveringMap f := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : IsTopologicalGroup K := topologicalGroup_of_lieGroup J ∞
  have hlocal := (f.isLocalDiffeomorph_of_lieMap_bijective hf).isLocalHomeomorph
  exact f.toMonoidHom.isCoveringMap_of_isLocalHomeomorph_of_surjective hlocal
    (f.toMonoidHom.surjective_of_isOpenMap hlocal.isOpenMap)

/-- A smooth homomorphism with bijective Lie map from a preconnected group to a simply
connected group is bijective. -/
theorem bijective_of_lieMap_bijective_of_simplyConnectedSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [PreconnectedSpace G] [SimplyConnectedSpace K]
    (f : ContMDiffMonoidMorphism I J ∞ G K) (hf : Bijective (lieMap f)) : Bijective f := by
  let _ : ConnectedSpace G :=
    { toPreconnectedSpace := inferInstance, toNonempty := ⟨1⟩ }
  let _ : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace H G
  let _ : PathConnectedSpace G := PathConnectedSpace.of_locallyPathConnectedSpace
  have hcov := f.isCoveringMap_of_lieMap_bijective hf
  exact ⟨hcov.injective, hcov.surjective⟩

end ContMDiffMonoidMorphism
