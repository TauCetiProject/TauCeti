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
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Lie.AutomaticSmoothness

/-!
# Lie homomorphisms with invertible differential

A smooth homomorphism with bijective Lie map is a local diffeomorphism at every point.
If its target is preconnected, it is a covering map. If its source is preconnected and its
target is simply connected, it is bijective. Conversely, a locally homeomorphic homomorphism
between finite-dimensional real Lie groups is a smooth local diffeomorphism. Thus local
homeomorphy is equivalent to a bijective Lie map, and over a preconnected target the same is true
of being a covering map.

These are the local-isomorphism criteria used when integrating Lie-algebra homomorphisms by
graph subgroups.

## Main results

* `MonoidHom.isLocalDiffeomorph_of_isLocalHomeomorph`: local homeomorphisms of Lie groups
  are smooth local diffeomorphisms.
* `ContMDiffMonoidMorphism.isLocalHomeomorph_iff_lieMap_bijective`: the local criterion.
* `ContMDiffMonoidMorphism.isLocalDiffeomorph_iff_isLocalHomeomorph`: equivalence of local
  differential and topological isomorphisms.
* `ContMDiffMonoidMorphism.isCoveringMap_iff_lieMap_bijective`: equivalence of covering maps
  and bijective Lie maps.
* `ContMDiffMonoidMorphism.isCoveringMap_of_lieMap_bijective`: bijective Lie maps give covering
  maps.
* `ContMDiffMonoidMorphism.bijective_of_lieMap_bijective_of_simplyConnectedSpace`: the
  bijectivity criterion over a simply connected target.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Exercise 2.3, for the covering-map assertion.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 4.40 and Problem 20-11(b),(c).
-/

public section

open Function Manifold Topology Set
open scoped ContDiff Manifold

noncomputable section

namespace MonoidHom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K] [LieGroup J ∞ K]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable (I J) in
/-- A locally homeomorphic homomorphism between finite-dimensional real Lie groups is a smooth
local diffeomorphism for their given manifold structures. -/
theorem isLocalDiffeomorph_of_isLocalHomeomorph [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (f : G →* K) (hf : IsLocalHomeomorph f) :
    IsLocalDiffeomorph I J ∞ f := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : ChartedSpace H' G := hf.chartedSpaceComap
  let _ : LieGroup J ∞ G :=
    hf.lieGroup_chartedSpaceComap (I := J) (n := ∞) (map_mul f)
  let e : Diffeomorph I J G G ∞ :=
    { toEquiv := Equiv.refl G
      contMDiff_toFun := TauCeti.Lie.contMDiff_of_continuous_monoidHom
        (I := I) (I' := J) (ContinuousMonoidHom.id G) continuous_id
      contMDiff_invFun := TauCeti.Lie.contMDiff_of_continuous_monoidHom
        (I := J) (I' := I) (ContinuousMonoidHom.id G) continuous_id }
  -- The comparison diffeomorphism is the identity on the underlying group.
  have he : (e : G → G) = _root_.id := by
    rw [← Diffeomorph.coe_toEquiv]
    rfl
  intro x
  simpa only [he, Function.comp_id, id_eq] using
    (e.isLocalDiffeomorph x).comp J K
      (hf.isLocalDiffeomorph_chartedSpaceComap (I := J) (n := ∞) (e x))

end MonoidHom

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

/-- A smooth homomorphism of finite-dimensional real Lie groups is a local homeomorphism
exactly when its Lie map is bijective. -/
theorem isLocalHomeomorph_iff_lieMap_bijective [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (f : ContMDiffMonoidMorphism I J ∞ G K) :
    IsLocalHomeomorph f ↔ Bijective (lieMap f) := by
  refine ⟨fun hf ↦ ?_, fun hf ↦
    (f.isLocalDiffeomorph_of_lieMap_bijective hf).isLocalHomeomorph⟩
  exact f.lieMap_bijective_of_isLocalDiffeomorphAt
    (f.toMonoidHom.isLocalDiffeomorph_of_isLocalHomeomorph I J hf 1)

/-- A smooth homomorphism of finite-dimensional real Lie groups is a local diffeomorphism
exactly when it is a local homeomorphism. -/
theorem isLocalDiffeomorph_iff_isLocalHomeomorph [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (f : ContMDiffMonoidMorphism I J ∞ G K) :
    IsLocalDiffeomorph I J ∞ f ↔ IsLocalHomeomorph f :=
  f.isLocalDiffeomorph_iff_lieMap_bijective.trans
    f.isLocalHomeomorph_iff_lieMap_bijective.symm

/-- A smooth homomorphism to a preconnected finite-dimensional real Lie group is a covering map
exactly when its Lie map is bijective. -/
theorem isCoveringMap_iff_lieMap_bijective [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [PreconnectedSpace K]
    (f : ContMDiffMonoidMorphism I J ∞ G K) : IsCoveringMap f ↔ Bijective (lieMap f) :=
  ⟨fun hf ↦ f.isLocalHomeomorph_iff_lieMap_bijective.mp hf.isLocalHomeomorph,
    f.isCoveringMap_of_lieMap_bijective⟩

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
