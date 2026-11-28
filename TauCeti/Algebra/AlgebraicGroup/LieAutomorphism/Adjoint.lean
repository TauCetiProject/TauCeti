/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LieAutomorphism.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Cotangent
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction

/-!
# The adjoint morphism to the Lie automorphism group scheme

For an affine group with finite projective cotangent space and a chosen basis of its tangent
Lie algebra, the adjoint representation factors through the subgroup of the general linear group
preserving the Lie bracket. Evaluating the factorization on a point gives its adjoint Lie
automorphism.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.LieAutomorphism

universe u v

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]
variable {n : ℕ} (b : Module.Basis (Fin n) R (Module.Dual R (Bialgebra.CotangentSpace R H)))

private theorem preserves_adjoint_genericMatrix :
    ConstantMultiplication.Preserves R n (bracketMatrix b)
      ((GeneralLinear.genericMatrix R n).map (Derivation.adjointCoordinateBialgHom b)) := by
  let _ := Derivation.adjointComodule (R := R) (H := H)
  have h : (GeneralLinear.genericMatrix R n).map (Derivation.adjointCoordinateBialgHom b) =
      LinearMap.toMatrix (b.baseChange H) (b.baseChange H)
        (Comodule.endOfPoint _ (AlgHom.id R H)) := by
    rw [Comodule.toMatrix_endOfPoint]
    ext i j
    rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply, Derivation.adjointCoordinateBialgHom_X]
    rfl
  rw [h, preserves_toMatrix_iff]
  exact Derivation.endOfPoint_adjointComodule_bracket (CommAlgCat.of R H) (toConv (AlgHom.id R H))

/-- The coordinate morphism of the adjoint action on the tangent Lie algebra. -/
noncomputable def adjointCoordinateMap : coordinateHopfAlgebra b ⟶ H :=
  CommHopfAlgCat.liftQuotient _
    (_root_.CommHopfAlgCat.ofHom (Derivation.adjointCoordinateBialgHom b))
    (ConstantMultiplication.definingHopfIdeal_toIdeal_le_ker_of_preserves_map_genericMatrix
      R n (bracketMatrix b) (Derivation.adjointCoordinateBialgHom b).toAlgHom
      (preserves_adjoint_genericMatrix H b))

/-- Composing with the inclusion in the general linear group gives the adjoint representation. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_adjointCoordinateMap :
    ConstantMultiplication.coordinateMap R n (bracketMatrix b) ≫ adjointCoordinateMap H b =
      _root_.CommHopfAlgCat.ofHom (Derivation.adjointCoordinateBialgHom b) := by
  rw [ConstantMultiplication.coordinateMap_def, adjointCoordinateMap]
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- On points over any coefficient algebra, the underlying linear map is the adjoint comodule
action. -/
theorem toLinearMap_pointsEquiv_mapPoints_adjointCoordinateMap (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (H := H) A) :
    (pointsEquiv b A
        ((adjointCoordinateMap H b).mapPointsFunctor.app A g)).toLinearEquiv.toLinearMap =
      (letI := Derivation.adjointComodule (R := R) (H := H); Comodule.endOfPoint _ g.ofConv) := by
  let _ := Derivation.adjointComodule (R := R) (H := H)
  let q : HopfAlgebra.points (H := coordinateHopfAlgebra b) A :=
    ((adjointCoordinateMap H b).mapPointsFunctor.app A) g
  have ht := coordinateMap_comp_adjointCoordinateMap H b
  rw [ConstantMultiplication.coordinateMap_def] at ht
  have hq := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp _ _ _ ht A g
  apply (LinearMap.toMatrix (b.baseChange A) (b.baseChange A)).injective
  refine (toMatrix_pointsEquiv b A q).trans ?_
  rw [GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply,
    show CommHopfAlgCat.quotientPointsHom _ _ A q = _ from hq.symm, Comodule.toMatrix_endOfPoint]
  rw [_root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, _root_.CommHopfAlgCat.hom_ofHom]
  ext i j
  simp only [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
    AlgHom.comp_apply, BialgHom.coe_toAlgHom, Derivation.adjointCoordinateBialgHom_X,
    Matrix.map_apply]

/-- On coefficient algebras in the universe of the point representation, the adjoint morphism
recovers the existing adjoint Lie automorphism. -/
@[simp]
theorem pointsEquiv_mapPoints_adjointCoordinateMap (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (H := H) A) :
    pointsEquiv b A ((adjointCoordinateMap H b).mapPointsFunctor.app A g) =
      Derivation.adjointLieEquiv A g := by
  apply LieEquiv.ext
  intro x
  have h := LinearMap.congr_fun (toLinearMap_pointsEquiv_mapPoints_adjointCoordinateMap H b A g) x
  exact h.trans
    ((Derivation.adjointComodule_endOfPoint_eq_adjointAction A g x).trans
      (Derivation.adjointLieEquiv_apply A g x).symm)

end TauCeti.LieAutomorphism
