/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Lie

/-!
# Proper étale Lie groupoids

`IsProperEtaleGroupoid` is the predicate defining a presentation of a smooth orbifold on the
native Lie groupoid carrier. It allows ineffective isotropy. Properness concerns the map from
total arrows to pairs of objects, and étaleness of target follows from étaleness of source by
inversion.

## References

* I. Moerdijk, [*Orbifolds as groupoids: an introduction*](https://arxiv.org/abs/math/0203100),
  Sections 1 and 3.
-/

public section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

/-- A proper étale Lie groupoid has Hausdorff total arrows, locally diffeomorphic source and target,
and proper source–target map. The remaining manifold and smoothness conditions are inherited from
`IsLieGroupoid`. Inversion gives the condition on target from the one on source. -/
class IsProperEtaleGroupoid {E H F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace K]
    (J : ModelWithCorners ℝ F K) [J.Boundaryless]
    (C : Type*) [Category C] [IsGroupoid C] [TopologicalSpace C] [ChartedSpace H C]
    [IsManifold I ∞ C] [TopologicalSpace (Quiver.Total C)] [ChartedSpace K (Quiver.Total C)]
    [IsManifold J ∞ (Quiver.Total C)] : Prop extends IsLieGroupoid I J C where
  /-- The total-arrow manifold is Hausdorff. -/
  t2Space_arrows : T2Space (Quiver.Total C) := by infer_instance
  /-- Source is a smooth local diffeomorphism. -/
  isLocalDiffeomorph_source : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C)
  /-- The joint source–target map is proper. -/
  isProperMap_source_target : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)

namespace IsProperEtaleGroupoid

variable {E H F K C : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [J.Boundaryless]
  [Category C] [IsGroupoid C] [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace K (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]

/-- An étale topological groupoid on Hausdorff second-countable manifolds with proper
source–target map gives a proper étale Lie groupoid. -/
theorem of_isTopologicalGroupoid [IsTopologicalGroupoid C]
    [T2Space (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    IsProperEtaleGroupoid I J C where
  toIsLieGroupoid := by
    have := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
    exact IsTopologicalGroupoid.isLieGroupoid_of_isLocalDiffeomorph hs ht
  isLocalDiffeomorph_source := hs
  isProperMap_source_target := hp

variable [IsProperEtaleGroupoid I J C]

/-- Target is a smooth local diffeomorphism in a proper étale presentation. -/
theorem isLocalDiffeomorph_target :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (IsLieGroupoid.isLocalDiffeomorph_source_iff_target I J C).1
    (isLocalDiffeomorph_source (I := I) (J := J))

end IsProperEtaleGroupoid

end TauCeti
