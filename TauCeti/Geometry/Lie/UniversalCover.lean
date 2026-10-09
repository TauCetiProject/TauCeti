/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Manifold.Instances.UniversalCover
public import TauCeti.AlgebraicTopology.UniversalCover.Descent

/-!
# The Lie algebra of the universal covering group

Let `G` be a finite-dimensional real Lie group that is locally path-connected and semilocally simply
connected. Its universal cover `UniversalCover (1 : G)` is a Lie group, and the covering
homomorphism `UniversalCover.projHom` is a smooth local diffeomorphism. Its differential at the
identity is therefore a linear isomorphism, so the Lie functor sends the covering homomorphism to a
Lie-algebra isomorphism: the universal covering group and `G` have the same Lie algebra.

## Main results

* `TauCeti.UniversalCover.lieEquivProjHom`: the Lie-algebra equivalence induced by the universal
  covering projection.
* `TauCeti.UniversalCover.lieMap_projHom_bijective`: the Lie map of the covering homomorphism is
  bijective.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 7, "Covering Groups", and Chapter 8, "Induced Lie
  Algebra Homomorphisms".
-/

public section

open scoped ContDiff

namespace TauCeti.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace H G]
  [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G] [LieGroup I ∞ G]

variable (I G) in
/-- The covering homomorphism of the universal cover of a Lie group induces a bijection, hence a
Lie-algebra isomorphism, between the Lie algebras of left-invariant derivations. -/
theorem lieMap_projHom_bijective :
    Function.Bijective
      (lieMap ((projHom : UniversalCover (1 : G) →ₜ* G).toContMDiffMonoidMorphism I I)) :=
  Lie.lieMap_bijective_of_isLocalDiffeomorphAt _ <| by
    simpa using isLocalDiffeomorph_proj (I := I) (n := ∞) (1 : G) 1

variable (I G) in
/-- The universal covering projection induces an equivalence between the Lie algebra of the
universal covering group and the Lie algebra of the base group. -/
noncomputable def lieEquivProjHom :
    LeftInvariantDerivation I (UniversalCover (1 : G)) ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G :=
  LieEquiv.ofBijective
    (lieMap ((projHom : UniversalCover (1 : G) →ₜ* G).toContMDiffMonoidMorphism I I))
    (lieMap_projHom_bijective I G)

/-- The Lie-algebra equivalence induced by the universal covering projection acts by the Lie
functor. -/
@[simp]
theorem lieEquivProjHom_apply (X : LeftInvariantDerivation I (UniversalCover (1 : G))) :
    lieEquivProjHom I G X =
      lieMap ((projHom : UniversalCover (1 : G) →ₜ* G).toContMDiffMonoidMorphism I I) X := by
  simp [lieEquivProjHom]

end TauCeti.UniversalCover
