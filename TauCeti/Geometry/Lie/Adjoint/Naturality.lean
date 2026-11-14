/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.Prod

/-!
# Naturality of the group adjoint on left-invariant derivations

The tangent-space adjoint action is natural with respect to group homomorphisms
(`MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`). Transporting that identity across
evaluation at the identity shows that `lieMap` and `ContinuousMonoidHom.lieMap` intertwine the
derivation-level group adjoint `TauCeti.Lie.Ad`. As immediate consequences, the derivation adjoint
is trivial on commutative Lie groups and splits componentwise across `TauCeti.Lie.prodLieEquiv`.

## Main results

* `lieMap_Ad`: a smooth Lie-group homomorphism intertwines `TauCeti.Lie.Ad`.
* `ContinuousMonoidHom.lieMap_Ad`: the continuous-homomorphism counterpart.
* `TauCeti.Lie.Ad_eq_refl`: the adjoint action of a commutative Lie group is trivial.
* `TauCeti.Lie.prodLieEquiv_Ad`, `TauCeti.Lie.Ad_prodLieEquiv_symm`: the adjoint action on a
  product Lie group acts componentwise under `TauCeti.Lie.prodLieEquiv`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

section Homomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [LieGroup I ∞ G] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Naturality of the derivation adjoint.** The Lie map of a smooth homomorphism intertwines the
group adjoint actions on left-invariant derivations. -/
@[simp]
theorem lieMap_Ad (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G)
    (D : LeftInvariantDerivation I G) :
    lieMap φ (TauCeti.Lie.Ad (I := I) g D) =
      TauCeti.Lie.Ad (I := I') (φ g) (lieMap φ D) := by
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let hG' := ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra hG'
  have hmap (X : LeftInvariantDerivation I G) :
      e' (lieMap φ X) = φ.toMonoidHom.groupLieAlgebraMap I I' (e X) :=
    (leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap φ X).trans
      (φ.toMonoidHom.groupLieAlgebraMap_apply I (e X)).symm
  apply e'.injective
  simp only [LieEquiv.coe_toLieHom]
  have hleft : e' (lieMap φ (TauCeti.Lie.Ad (I := I) g D)) =
      φ.toMonoidHom.groupLieAlgebraMap I I'
        (TauCeti.Lie.adjointContinuousLinearMap (I := I) g (e D)) :=
    (hmap _).trans (congrArg (φ.toMonoidHom.groupLieAlgebraMap I I')
      ((TauCeti.Lie.leftInvariantDerivationLieEquivGroupLieAlgebra_Ad g D).trans
        (TauCeti.Lie.tangentAd_apply g (e D))))
  have hright : e' (TauCeti.Lie.Ad (I := I') (φ g) (lieMap φ D)) =
      TauCeti.Lie.adjointContinuousLinearMap (I := I') (φ g)
        (φ.toMonoidHom.groupLieAlgebraMap I I' (e D)) :=
    (TauCeti.Lie.leftInvariantDerivationLieEquivGroupLieAlgebra_Ad (φ g) (lieMap φ D)).trans
      ((TauCeti.Lie.tangentAd_apply (φ g) (e' (lieMap φ D))).trans
        (congrArg (TauCeti.Lie.adjointContinuousLinearMap (I := I') (φ g)) (hmap D)))
  exact hleft.trans
    ((φ.toMonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap g (e D)).trans hright.symm)

/-- Bundled naturality of the derivation adjoint along a smooth homomorphism. -/
theorem lieMap_comp_Ad (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G) :
    (lieMap φ).comp (TauCeti.Lie.Ad (I := I) g).toLieHom =
      (TauCeti.Lie.Ad (I := I') (φ g)).toLieHom.comp (lieMap φ) := by
  apply LieHom.ext
  intro D
  exact lieMap_Ad φ g D

/-- **Naturality of the derivation adjoint for continuous homomorphisms.** -/
@[simp]
theorem ContinuousMonoidHom.lieMap_Ad (φ : G →ₜ* G') (g : G)
    (D : LeftInvariantDerivation I G) :
    ContinuousMonoidHom.lieMap (I := I) (I' := I') φ (TauCeti.Lie.Ad (I := I) g D) =
      TauCeti.Lie.Ad (I := I') (φ g) (ContinuousMonoidHom.lieMap (I := I) (I' := I') φ D) := by
  rw [ContinuousMonoidHom.lieMap_def, _root_.lieMap_Ad,
    ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]

end Homomorphism

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [LieGroup I ∞ G] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The group adjoint on left-invariant derivations of a commutative Lie group is trivial. -/
@[simp]
theorem Ad_eq_refl [IsMulCommutative G] (g : G) :
    Ad (I := I) g = LieEquiv.refl := by
  apply LieEquiv.ext
  intro D
  rw [Ad_apply, tangentAd_apply, adjointContinuousLinearMap_eq_id, ContinuousLinearMap.id_apply,
    LieEquiv.refl_apply, LieEquiv.symm_apply_apply]

/-- Applying the group adjoint on a commutative Lie group leaves every derivation fixed. -/
theorem Ad_apply_eq_self [IsMulCommutative G] (g : G) (D : LeftInvariantDerivation I G) :
    Ad (I := I) g D = D := by
  simp

/-- Under `TauCeti.Lie.prodLieEquiv`, the adjoint action on a product Lie group acts componentwise
on the two factor Lie algebras. -/
theorem prodLieEquiv_Ad (p : G × G') (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    prodLieEquiv (Ad (I := I.prod I') p D) =
      (Ad (I := I) p.1 (prodLieEquiv D).1, Ad (I := I') p.2 (prodLieEquiv D).2) := by
  simp [prodLieEquiv_apply]

/-- The inverse product Lie equivalence intertwines the componentwise and product adjoint
actions. -/
@[simp]
theorem Ad_prodLieEquiv_symm (p : G × G')
    (X : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    Ad (I := I.prod I') p (prodLieEquiv.symm X) =
      prodLieEquiv.symm (Ad (I := I) p.1 X.1, Ad (I := I') p.2 X.2) := by
  apply (prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')).injective
  simp only [LieEquiv.coe_toLieHom, prodLieEquiv_Ad, LieEquiv.apply_symm_apply]

end TauCeti.Lie
