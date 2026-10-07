/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Scalar extension of linear Hom spaces

The canonical map from `A ⊗[R] Hom_R(M,N)` to `Hom_A(A ⊗[R] M, A ⊗[R] N)` sends
`a ⊗ f` to `a • f.baseChange A`. It is an equivalence when `M` is finite projective;
no finiteness condition is needed on `N` or on the commutative value algebra `A`.
This comparison allows a scalar-extended Hom representation to act on scalar-extended vectors.

The equivalence uses Mathlib's `lTensorHomEquivHomLTensor` and
`LinearMap.liftBaseChangeEquiv`, following the construction of
`TauCeti.Module.Dual.baseChangeEvaluationEquiv`.
-/

public section

open scoped TensorProduct

namespace LinearMap

universe u v w x

variable (R : Type u) (A : Type v) (M : Type w) (N : Type x)
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The canonical scalar-extension map on linear Hom spaces. -/
noncomputable def baseChangeTensorHom :
    A ⊗[R] (M →ₗ[R] N) →ₗ[A] (A ⊗[R] M →ₗ[A] A ⊗[R] N) :=
  liftBaseChange A (baseChangeHom R A M N)

variable {R A M N}

/-- A pure tensor acts by the scalar multiple of the base-changed linear map. -/
@[simp]
theorem baseChangeTensorHom_tmul (a : A) (f : M →ₗ[R] N) :
    baseChangeTensorHom R A M N (a ⊗ₜ[R] f) = a • f.baseChange A := by
  simp [baseChangeTensorHom]

/-- Scalar extension of a rank-one map evaluates by the scalar-extended dual pairing.
The tensor comparison assembles the scalar-extended functional and target vector. -/
@[simp]
theorem baseChangeTensorHom_distribBaseChange_symm_tmul
    (ξ : A ⊗[R] Module.Dual R M) (η : A ⊗[R] N) (z : A ⊗[R] M) :
    baseChangeTensorHom R A M N
        ((dualTensorHom R M N).baseChange A
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R A (Module.Dual R M) N).symm
            (ξ ⊗ₜ[A] η))) z =
      TauCeti.Module.Dual.baseChangeEvaluation ξ z • η := by
  induction ξ using TensorProduct.inductionOn with
  | add ξ ξ' h h' =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, h, h', add_smul]
  | tmul a φ =>
      induction η using TensorProduct.inductionOn with
      | add η η' h h' =>
          simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h, h', smul_add]
      | tmul b n =>
          induction z using TensorProduct.inductionOn with
          | add z z' h h' => simp only [map_add, h, h', add_smul]
          | tmul c m =>
              simp [TensorProduct.smul_tmul', Algebra.smul_def, mul_comm, mul_left_comm,
                mul_assoc]

variable [Module.Finite R M] [Module.Projective R M]

/-- Scalar extension commutes with linear Hom out of a finite projective module. -/
noncomputable def baseChangeTensorHomEquiv :
    A ⊗[R] (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] A ⊗[R] N) :=
  LinearEquiv.ofBijective (baseChangeTensorHom R A M N) <| by
    let e := (lTensorHomEquivHomLTensor R M A N).trans
      ((liftBaseChangeEquiv A).restrictScalars R)
    have he : e.toLinearMap = (baseChangeTensorHom R A M N).restrictScalars R := by
      apply TensorProduct.ext'
      intro a f
      apply TensorProduct.AlgebraTensorModule.ext
      intro b m
      simp only [e, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        LinearEquiv.restrictScalars_apply, lTensorHomEquivHomLTensor_apply,
        LinearMap.restrictScalars_apply, baseChangeTensorHom_tmul, LinearMap.smul_apply,
        LinearMap.baseChange_tmul]
      rw [← liftBaseChange]
      simp [TensorProduct.smul_tmul', mul_comm]
    rw [← coe_restrictScalars R, ← he]
    exact e.bijective

/-- The Hom comparison equivalence is the canonical scalar-extension map. -/
@[simp]
theorem baseChangeTensorHomEquiv_apply (z : A ⊗[R] (M →ₗ[R] N)) :
    baseChangeTensorHomEquiv (R := R) (A := A) (M := M) (N := N) z =
      baseChangeTensorHom R A M N z :=
  (rfl)

/-- The inverse Hom comparison sends a base-changed map to the corresponding tensor
with scalar coefficient one. -/
@[simp]
theorem baseChangeTensorHomEquiv_symm_baseChange (f : M →ₗ[R] N) :
    (baseChangeTensorHomEquiv (R := R) (A := A) (M := M) (N := N)).symm
        (f.baseChange A) = 1 ⊗ₜ[R] f := by
  apply (baseChangeTensorHomEquiv (R := R) (A := A) (M := M) (N := N)).injective
  simp

end LinearMap
