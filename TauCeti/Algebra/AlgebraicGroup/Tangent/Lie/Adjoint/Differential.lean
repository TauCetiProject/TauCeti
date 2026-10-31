/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Infinitesimal
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential

/-!
# Differentiating the adjoint comodule

The differentiated action of the adjoint comodule is the Lie bracket on the dual of the
augmentation cotangent space. This connects the dual-number description of the infinitesimal
adjoint action with the differentiated representation used to study invariant subspaces.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.d, 10.18–10.23.
-/

public section

open scoped TensorProduct

namespace Derivation

open TauCeti TensorProduct TrivSqZeroExt WithConv

universe u

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

attribute [local instance] adjointComodule

/-- The differential of the adjoint comodule is the adjoint action of the tangent Lie algebra,
expressed in the cotangent-dual model. -/
-- Apply before the general differential and adjoint-coaction evaluation rules expand the input.
@[simp↓]
theorem differential_adjointComodule (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Comodule.differential (R := R) (H := H) d x =
      ⁅(cotangentDualLieEquiv (R := R) (H := H)).symm d, x⁆ := by
  -- The proof combines `Derivation.adDerivation_dualNumber_apply` with
  -- `TauCeti.Comodule.snd_endOfPoint_derivationToTrivSqZeroExtEquivLift`.
  let C := Bialgebra.CounitAlgebra R H R
  let V := Module.Dual R (Bialgebra.CotangentSpace R H)
  let s : DualNumber C →ₗ[R] R := (Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
    (sndHom C C).restrictScalars R
  -- Extract the infinitesimal coefficient after scalar extension, so both descriptions
  -- of the differentiated action can be compared in the cotangent-dual model.
  have hcoeff (z : DualNumber C ⊗[R] V) (a : H) :
      Bialgebra.CounitAlgebra.algEquivSelf R H R
          (cotangentLinearEquiv (B := R) (TensorProduct.lid R V
            (LinearMap.rTensor V s z)) a) =
        Bialgebra.CounitAlgebra.algEquivSelf R H R
          ((Bialgebra.CounitAlgebra.algEquivSelf R H (DualNumber C)
            (tangentScalarExtensionEquiv (R := R) (A := H) (B := DualNumber C) z a)).snd) := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, add_apply, snd_add, hz, hw]
    | tmul c y =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        algEquivSelf_cotangentLinearEquiv_apply,
        algEquivSelf_tangentScalarExtensionEquiv_tmul_apply,
        LinearMap.smul_apply, smul_eq_mul]
      simp only [algebraMap_eq_inl', snd_mul, snd_inl, fst_inl,
        op_smul_eq_smul, smul_eq_mul]
      simp only [s, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
        LinearMap.restrictScalars_apply, sndHom_apply]
      -- The coefficient synonym carries the same ring operations, with transported instances.
      erw [mul_zero, zero_add, map_mul]
      rw [AlgEquiv.commutes]
      exact mul_comm _ _
  -- Compute the adjoint action on the constant lift of the input tangent vector.
  have haction := tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (R := R) (H := H) (CommAlgCat.of R (DualNumber C))
    ((derivationMulEquivTangentKer R H R (.ofAdd d)).val) (1 ⊗ₜ[R] x)
  have hinit : tangentScalarExtensionEquiv (R := R) (A := H) (B := DualNumber C)
      (1 ⊗ₜ[R] x) =
      mapValue ((inlAlgHom R C C).comp
        (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm.toAlgHom)
          (cotangentLinearEquiv (B := R) x) := by
    ext a
    rw [tangentScalarExtensionEquiv_tmul_apply, one_mul, mapValue_apply]
    erw [AlgHom.comp_apply, cotangentLinearEquiv_apply_apply]
    simp only [AlgEquiv.coe_toAlgHom,
      Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
    rfl
  -- Compare infinitesimal coefficients using the two established dual-number formulas.
  apply (cotangentDualLieEquiv (R := R) (H := H)).injective
  rw [LieHom.map_lie, LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply]
  ext a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  rw [cotangentDualLieEquiv_apply,
    ← Comodule.snd_endOfPoint_derivationToTrivSqZeroExtEquivLift, hcoeff]
  rw [hinit] at haction
  have ha := DFunLike.congr_fun haction a
  -- The tangent-point equivalence packages the same dual-number lift.
  simp only [derivationMulEquivTangentKer_apply_ofConv, toAdd_ofAdd] at ha
  rw [ha]
  have hp : pointInCounitAlgebra (DualNumber C)
      ((derivationMulEquivTangentKer R H R (.ofAdd d)).val) =
      (Bialgebra.CounitAlgebra.pointsMulEquiv R H (DualNumber C)).symm
        ((derivationMulEquivTangentKer R H R (.ofAdd d)).val) := by
    apply WithConv.ofConv_injective
    ext b
    simp only [pointInCounitAlgebra_apply,
      Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply]
    exact (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R H (DualNumber C) _).symm
  rw [hp, adDerivation_dualNumber_apply]
  simp only [snd_add, snd_inl, snd_inr, zero_add, cotangentDualLieEquiv_apply]

end Derivation
