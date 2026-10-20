/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.GroupFunctor
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ScalarExtension
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction

/-!
# Evaluating tensor automorphisms in a faithful representation

Evaluation on a finite comodule gives a homomorphism from tensor automorphisms of scalar
extension to linear automorphisms of that comodule's scalar extension. This homomorphism
commutes with change of the value algebra. Under Tannakian reconstruction it is the usual
point action, and its matrix is obtained by evaluating the comodule's coordinate morphism.
Thus evaluation realizes the same representation as the coordinate group-scheme map.

Over a field, evaluation on a faithful comodule is injective for every commutative value
algebra, including nonreduced algebras. In particular a single faithful comodule determines
all components of a tensor automorphism; this is stronger than testing field-valued points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 9, especially §9.4.
* The constructions use `TauCeti.Tannaka.fgPointTensorIsoEquiv`,
  `TauCeti.Comodule.coordinateBialgHom`, and the matrix-coefficient criterion for faithfulness.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v

section Evaluation

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Bialgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- Evaluation of tensor automorphisms on one finite comodule, as a group homomorphism. -/
noncomputable def tensorAutEvaluation (M : FGComoduleCat.{u, v, u} R H) :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) →*
      LinearMap.GeneralLinearGroup A (A ⊗[R] M) where
  toFun η := scalarExtensionComponentGL R H A η M
  map_one' := by
    apply Units.ext
    simp [Module.End.one_eq_id]
  map_mul' η θ := by
    apply Units.ext
    simp [Module.End.mul_eq_comp]

/-- The endomorphism underlying evaluation is the transported component. -/
@[simp]
theorem tensorAutEvaluation_coe (M : FGComoduleCat.{u, v, u} R H)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    (tensorAutEvaluation R H A M η : Module.End A (A ⊗[R] M)) =
      scalarExtensionComponent R H A η M :=
  scalarExtensionComponentGL_coe R H A η M

variable {A} {B : Type u} [CommSemiring B] [Algebra R B]

/-- Evaluation commutes with extension of the value algebra. -/
@[simp]
theorem tensorAutEvaluation_mapValue (f : A →ₐ[R] B)
    (M : FGComoduleCat.{u, v, u} R H)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    tensorAutEvaluation R H B M (tensorAutMapValue R H A B f η) =
      Module.End.mapValueGL f (tensorAutEvaluation R H A M η) := by
  apply Units.ext
  simp

end Evaluation

section Functor

variable (R : Type u) [CommRing R]
variable (H : Type v) [Semiring H] [Bialgebra R H]

/-- Evaluation on a finite comodule as a natural transformation of group-valued functors.
The target is lifted to the universe of tensor automorphisms. -/
noncomputable def tensorAutEvaluationNatTrans (M : FGComoduleCat.{u, v, u} R H) :
    tensorAutFunctor R H ⟶
      GeneralLinear.scalarExtensionAutomorphismsFunctor (R := R) (V := M) ⋙
        GrpCat.uliftFunctor.{max (u + 1) v, u} where
  app A := eqToHom (tensorAutFunctor_obj R H A) ≫
    GrpCat.ofHom (MulEquiv.ulift.{u, max (u + 1) v}.symm.toMonoidHom.comp
      (tensorAutEvaluation R H A M))
  naturality {A B} f := by
    -- The fixed-module functor exposes its objects for constructing natural transformations.
    -- Normalize them before using categorical cancellation.
    dsimp only [GeneralLinear.scalarExtensionAutomorphismsFunctor, Functor.comp_map,
      GrpCat.uliftFunctor]
    apply (cancel_epi (eqToHom (tensorAutFunctor_obj R H A).symm)).mp
    -- Expose the components before cancelling their categorical object transports.
    change (eqToHom (tensorAutFunctor_obj R H A).symm ≫
      (tensorAutFunctor R H).map f ≫ eqToHom (tensorAutFunctor_obj R H B) ≫
        GrpCat.ofHom (MulEquiv.ulift.{u, max (u + 1) v}.symm.toMonoidHom.comp
          (tensorAutEvaluation R H B M))) =
      eqToHom (tensorAutFunctor_obj R H A).symm ≫
        (eqToHom (tensorAutFunctor_obj R H A) ≫
          GrpCat.ofHom (MulEquiv.ulift.{u, max (u + 1) v}.symm.toMonoidHom.comp
            (tensorAutEvaluation R H A M))) ≫ _
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    apply GrpCat.ext
    intro η
    -- Evaluation in the lifted target and cancellation of the source object transports
    -- reduce the categorical square to the explicit base-change formula.
    change ULift.up (tensorAutEvaluation R H B M
      (eqToHom (tensorAutFunctor_obj R H B)
        ((tensorAutFunctor R H).map f
          (eqToHom (tensorAutFunctor_obj R H A).symm η)))) =
      ULift.up (GeneralLinear.mapScalarExtensionAutomorphisms (V := M) f
        (tensorAutEvaluation R H A M η))
    rw [tensorAutFunctor_map_transport_apply, tensorAutEvaluation_mapValue]
    congr 1
    apply Units.ext
    simpa only [Module.End.mapValueGL_coe] using
      (GeneralLinear.val_mapScalarExtensionAutomorphisms (V := M) f
        (tensorAutEvaluation R H A M η)).symm

/-- The component of the evaluation transformation is evaluation, with the specified universe
lift and object transport. -/
theorem tensorAutEvaluationNatTrans_app_apply (M : FGComoduleCat.{u, v, u} R H)
    (A : CommAlgCat.{u} R)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    ((tensorAutEvaluationNatTrans R H M).app A
      (eqToHom (tensorAutFunctor_obj R H A).symm η)).down =
        tensorAutEvaluation R H A M η := by
  -- The component is a composite through the opaque source object equality.
  -- After naming that composite, the inverse transports cancel.
  change ((eqToHom (tensorAutFunctor_obj R H A).symm ≫
    eqToHom (tensorAutFunctor_obj R H A) ≫
      GrpCat.ofHom (MulEquiv.ulift.{u, max (u + 1) v}.symm.toMonoidHom.comp
        (tensorAutEvaluation R H A M))) η).down = _
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rfl

end Functor

section PointAction

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- Evaluation of the tensor automorphism induced by a point is its comodule point action. -/
@[simp]
theorem tensorAutEvaluation_fgPointTensorIso
    (M : FGComoduleCat.{u, v, u} R H) (g : WithConv (H →ₐ[R] A)) :
    tensorAutEvaluation R H A M (fgPointTensorIso R H A g) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) := by
  apply Units.ext
  rw [tensorAutEvaluation_coe, scalarExtensionComponent_fgPointTensorIso]
  rfl

end PointAction

section Reconstruction

variable (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
variable (A : Type u) [CommRing A] [Algebra k A]

/-- The reconstruction isomorphism intertwines natural evaluation with the original comodule
point action, retaining the universe lift on the group-valued functors. -/
theorem tensorAutEvaluationNatTrans_reconstruction_apply
    (M : FGComoduleCat.{u, u, u} k H) (B : CommAlgCat.{u} k)
    (g : ULift.{u + 1} (WithConv (H →ₐ[k] B))) :
    ((tensorAutEvaluationNatTrans k H M).app B
      ((pointsFunctorIsoTensorAutFunctor k H).hom.app B g)).down =
        LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g.down) := by
  -- Expose evaluation's component to use the named reconstruction component equation.
  change tensorAutEvaluation k H B M
    (eqToHom (tensorAutFunctor_obj k H B)
      ((pointsFunctorIsoTensorAutFunctor k H).hom.app B g)) = _
  rw [pointsFunctorIsoTensorAutFunctor_hom_app_apply, tensorAutEvaluation_fgPointTensorIso]

/-- The component of a tensor automorphism is the action of its reconstructed point. -/
theorem tensorAutEvaluation_eq_pointsAction_reconstructedPoint
    (M : FGComoduleCat.{u, u, u} k H)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    tensorAutEvaluation k H A M η =
      LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction M (reconstructedPoint k H A η)) := by
  rw [← tensorAutEvaluation_fgPointTensorIso, fgPointTensorIso_reconstructedPoint]

/-- The matrix of evaluation is the matrix of the coordinate representation evaluated at the
reconstructed point. This identifies the Tannakian representation with the coordinate morphism
whose spectrum is the representation's group-scheme map. -/
theorem toMatrix_tensorAutEvaluation
    (M : FGComoduleCat.{u, u, u} k H) {n : ℕ} (b : Module.Basis (Fin n) k M)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    LinearMap.toMatrix (b.baseChange A) (b.baseChange A)
        (tensorAutEvaluation k H A M η : Module.End A (A ⊗[k] M)) =
      (GeneralLinear.pointsMulEquiv n
        (WithConv.toConv ((reconstructedPoint k H A η).ofConv.comp
          (Comodule.coordinateBialgHom (H := H) b).toAlgHom)) :
        Matrix (Fin n) (Fin n) A) := by
  rw [tensorAutEvaluation_coe, ← endOfPoint_reconstructedPoint,
    Comodule.toMatrix_endOfPoint, AlgHom.pointsMulEquiv_comp_coordinateBialgHom]

/-- A tensor automorphism is determined by its component on any faithful finite comodule.
No reducedness or field hypothesis on the value algebra is needed. -/
theorem tensorAutEvaluation_injective_of_isFaithful
    (M : FGComoduleCat.{u, u, u} k H)
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M)) :
    Function.Injective (tensorAutEvaluation k H A M) := by
  intro η θ h
  have hpoints : reconstructedPoint k H A η = reconstructedPoint k H A θ := by
    apply Comodule.pointsAction_injective_of_isFaithful hM
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[k] M)).symm.injective
    rw [tensorAutEvaluation_eq_pointsAction_reconstructedPoint,
      tensorAutEvaluation_eq_pointsAction_reconstructedPoint] at h
    exact h
  calc
    η = fgPointTensorIso k H A (reconstructedPoint k H A η) :=
      (fgPointTensorIso_reconstructedPoint k H A η).symm
    _ = fgPointTensorIso k H A (reconstructedPoint k H A θ) := congrArg _ hpoints
    _ = θ := fgPointTensorIso_reconstructedPoint k H A θ

end Reconstruction

end TauCeti.Tannaka
