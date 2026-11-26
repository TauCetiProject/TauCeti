/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.ContinuousFunctor

/-!
# Naturality of the group adjoint on left-invariant derivations

The tangent-space adjoint action is natural with respect to group homomorphisms
(`MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`). Transporting that identity across
evaluation at the identity shows that `lieMap` and `ContinuousMonoidHom.lieMap` intertwine the
derivation-level group adjoint `TauCeti.Lie.Ad`.

## Main results

* `ContMDiffMonoidMorphism.lieMap_Ad`: a smooth Lie-group homomorphism intertwines `TauCeti.Lie.Ad`.
* `ContinuousMonoidHom.lieMap_Ad`: the continuous-homomorphism counterpart.
-/

public section

noncomputable section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [LieGroup I ∞ G] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace ContMDiffMonoidMorphism

/-- **Naturality of the derivation adjoint.** The Lie map of a smooth homomorphism intertwines the
group adjoint actions on left-invariant derivations. -/
@[simp]
theorem lieMap_Ad (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G)
    (D : LeftInvariantDerivation I G) :
    lieMap φ (TauCeti.Lie.Ad (I := I) g D) =
      TauCeti.Lie.Ad (I := I') (φ g) (lieMap φ D) := by
  have hmap (X : LeftInvariantDerivation I G) :
      leftInvariantDerivationLieEquivGroupLieAlgebra
          (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')) (lieMap φ X) =
        φ.toMonoidHom.groupLieAlgebraMap I I'
          (leftInvariantDerivationLieEquivGroupLieAlgebra
            (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)) X) := by
    rw [leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap]
    exact (φ.toMonoidHom.groupLieAlgebraMap_apply I _).symm
  apply (leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))).injective
  simp only [LieEquiv.coe_toLieHom, hmap,
    TauCeti.Lie.leftInvariantDerivationLieEquivGroupLieAlgebra_Ad, TauCeti.Lie.tangentAd_apply]
  exact φ.toMonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap g _

end ContMDiffMonoidMorphism

/-- **Naturality of the derivation adjoint for continuous homomorphisms.** -/
@[simp]
theorem ContinuousMonoidHom.lieMap_Ad (φ : G →ₜ* G') (g : G)
    (D : LeftInvariantDerivation I G) :
    ContinuousMonoidHom.lieMap (I := I) (I' := I') φ (TauCeti.Lie.Ad (I := I) g D) =
      TauCeti.Lie.Ad (I := I') (φ g) (ContinuousMonoidHom.lieMap (I := I) (I' := I') φ D) := by
  rw [ContinuousMonoidHom.lieMap_def, ContMDiffMonoidMorphism.lieMap_Ad,
    ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]

end
