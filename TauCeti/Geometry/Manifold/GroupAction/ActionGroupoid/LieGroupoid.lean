/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid.Basic
public import TauCeti.Geometry.Manifold.Groupoid.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# The action Lie groupoid of a countable discrete group

Let a countable discrete group `G` act by smooth maps on a Hausdorff second-countable real smooth
manifold `X`. With the étale smooth structure of
`TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid.Basic`, whose object and arrow charts are
both modelled on the model of `X`, Mathlib's native action category
`CategoryTheory.ActionCategory G X` is a Lie groupoid
(`TauCeti.ActionGroupoid.isLieGroupoid_of_discreteTopology`). Every label is retained, including
labels acting trivially on `X`. This differs from the scoped instance
`TauCeti.ActionGroupoid.isLieGroupoid` of `GroupAction/ActionGroupoid/Lie.lean`, whose arrows are
modelled on the product of the group and base models.

The source map is a local diffeomorphism, hence a submersion. Composition is smooth on the
transverse fibre product of target and source because composing smooth families of composable
arrows gives a smooth family, and the two arrows of a composable pair depend smoothly on the pair.
Countability of `G` makes the arrow manifold, a disjoint union of copies of `X` indexed by `G`,
second countable.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti.ActionGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (G X : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MulAction G X] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- The source map of the action groupoid of a discrete group is a smooth submersion. -/
private theorem isSubmersion_source :
    Manifold.IsSubmersion I I ∞
      (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X) := by
  simpa using (isLocalDiffeomorph_source I ∞ G X).comp_isSubmersion
    (Manifold.IsSubmersion.id (I := I) (n := ∞) (M := Quiver.Total (ActionCategory G X)))

variable [FiniteDimensional ℝ E] [I.Boundaryless] [ContMDiffConstSMul I ∞ G X] [Countable G]
  [T2Space X] [SecondCountableTopology X]

/-- The action groupoid of a countable discrete group acting by smooth maps on a Hausdorff
second-countable smooth manifold is a Lie groupoid, with arrows modelled on the model of `X`. -/
instance isLieGroupoid_of_discreteTopology : IsLieGroupoid I I (ActionCategory G X) where
  isSubmersion_source := isSubmersion_source I G X
  contMDiff_unit := contMDiff_unit I ∞ G X
  contMDiff_inverse := contMDiff_inverse I ∞ G X
  -- Composition is smooth for smooth families of composable arrows.
  contMDiff_comp := contMDiff_composablePairs_comp_of_contMDiff (isSubmersion_source I G X)
    (contMDiff_inverse I ∞ G X) fun ha hb h ↦ contMDiff_comp I ∞ ha hb h

end TauCeti.ActionGroupoid
