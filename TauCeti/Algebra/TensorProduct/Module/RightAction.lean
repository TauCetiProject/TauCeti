/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import TauCeti.Algebra.TensorProduct.Module

/-!
# The right-factor module action on a tensor product

An action on the right factor commuting with the ground scalars acts on the tensor product
by transporting Mathlib's `TensorProduct.leftModule` along `TensorProduct.comm`.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {R M N B : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Semiring B] [AddCommMonoid N] [Module R N] [Module B N] [SMulCommClass R B N]

/-- The action of `B` on `M ⊗[R] N` induced by its action on `N`. This is an explicit module
structure since a scalar can also act through the left factor. -/
abbrev rightModule : Module B (M ⊗[R] N) :=
  (TensorProduct.comm R M N).toAddEquiv.module B

/-- Tensor commutation takes the right-factor action to the left-factor action. -/
theorem comm_rightModule_smul (b : B) (x : M ⊗[R] N) :
    letI := rightModule (B := B) (R := R) (M := M) (N := N)
    TensorProduct.comm R M N (b • x) = b • TensorProduct.comm R M N x := by
  exact (TensorProduct.comm R M N).toAddEquiv.linearEquiv B |>.map_smul b x

/-- The right-factor action on a pure tensor acts on its right entry. -/
@[simp]
theorem rightModule_smul_tmul (b : B) (m : M) (n : N) :
    letI := rightModule (B := B) (R := R) (M := M) (N := N)
    b • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (b • n) := by
  apply (TensorProduct.comm R M N).injective
  rw [comm_rightModule_smul, comm_tmul, comm_tmul, smul_tmul']

/-- The right-factor action is the tensor extension of the original scalar endomorphism. -/
theorem rightModule_smul_eq_lTensor (b : B) (x : M ⊗[R] N) :
    letI := SMulCommClass.symm R B N
    letI := rightModule (B := B) (R := R) (M := M) (N := N)
    b • x = (Module.toModuleEnd R N b).lTensor M x := by
  let _ := SMulCommClass.symm R B N
  let _ := rightModule (B := B) (R := R) (M := M) (N := N)
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp only [rightModule_smul_tmul, LinearMap.lTensor_tmul, Module.toModuleEnd_apply,
      DistribSMul.toLinearMap_apply]
  | add x y hx hy => rw [smul_add, map_add, hx, hy]

end TensorProduct

namespace TauCeti.BialgebraModule

variable {R A B M N : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module A M] [Module B N]
  [IsScalarTower R A M] [IsScalarTower R B N]

/-- A pure tensor of scalars acts by the successive actions through its two factors. -/
theorem tensorPairAction_tmul_apply (a : A) (b : B) (x : M ⊗[R] N) :
    letI := TensorProduct.rightModule (B := B) (R := R) (M := M) (N := N)
    tensorPairAction R M N (a ⊗ₜ[R] b) x = a • (b • x) := by
  have h : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, map_mul, mul_apply_eq_comp, tensorPairAction_tmul_one]
  congr 1
  apply (TensorProduct.comm R M N).injective
  rw [comm_tensorPairAction_one_tmul, TensorProduct.comm_rightModule_smul]

end TauCeti.BialgebraModule
