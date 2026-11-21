/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.ContinuousFunctor

/-!
# Naturality of the group adjoint action on left-invariant derivations

A smooth or continuous homomorphism between finite-dimensional real Lie groups intertwines their
group adjoint actions on left-invariant derivations through its Lie map. This transports the
tangent-space naturality identity `MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap` across
evaluation at the identity.

## Main results

* `ContMDiffMonoidMorphism.lieMap_Ad`: `lieMap φ (Ad g X) = Ad (φ g) (lieMap φ X)`.
* `ContMDiffMonoidMorphism.lieMap_comp_Ad`: operator form of adjoint equivariance for `lieMap`.
* `ContinuousMonoidHom.lieMap_Ad`: the corresponding identity for continuous homomorphisms.
-/

public section

noncomputable section

open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

/-- The Lie map of a smooth Lie-group homomorphism intertwines the group adjoint actions. -/
@[simp]
theorem ContMDiffMonoidMorphism.lieMap_Ad
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G) (X : LeftInvariantDerivation I G) :
    lieMap φ (TauCeti.Lie.Ad (I := I) g X) = TauCeti.Lie.Ad (I := I') (φ g) (lieMap φ X) := by
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let hG' := ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra hG'
  apply EquivLike.injective e'
  have h1 : e' (lieMap φ (TauCeti.Lie.Ad (I := I) g X)) =
      φ.toMonoidHom.groupLieAlgebraMap I I' (e (TauCeti.Lie.Ad (I := I) g X)) := by
    rw [MonoidHom.groupLieAlgebraMap_apply]
    exact leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap φ (TauCeti.Lie.Ad (I := I) g X)
  have h2 : e' (TauCeti.Lie.Ad (I := I') (φ g) (lieMap φ X)) =
      TauCeti.Lie.tangentAd (I := I') (φ g) (e' (lieMap φ X)) :=
    TauCeti.Lie.leftInvariantDerivationLieEquivGroupLieAlgebra_Ad (φ g) (lieMap φ X)
  have h3 : e' (lieMap φ X) = φ.toMonoidHom.groupLieAlgebraMap I I' (e X) := by
    rw [MonoidHom.groupLieAlgebraMap_apply]
    exact leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap φ X
  rw [h1, TauCeti.Lie.leftInvariantDerivationLieEquivGroupLieAlgebra_Ad, h2, h3,
    TauCeti.Lie.tangentAd_apply, TauCeti.Lie.tangentAd_apply]
  exact φ.toMonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap g (e X)

/-- Operator form of adjoint equivariance for the Lie map of a smooth homomorphism. -/
theorem ContMDiffMonoidMorphism.lieMap_comp_Ad
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G) :
    (lieMap φ).comp (TauCeti.Lie.Ad (I := I) g).toLieHom =
      (TauCeti.Lie.Ad (I := I') (φ g)).toLieHom.comp (lieMap φ) := by
  apply LieHom.ext
  intro X
  simpa only [LieHom.comp_apply, LieEquiv.coe_coe] using φ.lieMap_Ad g X

/-- The Lie map of a continuous homomorphism between finite-dimensional real Lie groups
intertwines the group adjoint actions. -/
@[simp]
theorem ContinuousMonoidHom.lieMap_Ad
    (f : G →ₜ* G') (g : G) (X : LeftInvariantDerivation I G) :
    ContinuousMonoidHom.lieMap (I := I) (I' := I') f (TauCeti.Lie.Ad (I := I) g X) =
      TauCeti.Lie.Ad (I := I') (f g) (ContinuousMonoidHom.lieMap (I := I) (I' := I') f X) := by
  rw [ContinuousMonoidHom.lieMap_def,
    ← ContinuousMonoidHom.coe_toContMDiffMonoidMorphism (I := I) (I' := I') f]
  exact (f.toContMDiffMonoidMorphism I I').lieMap_Ad g X

end
