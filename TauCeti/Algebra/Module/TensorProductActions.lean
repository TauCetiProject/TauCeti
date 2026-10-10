/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Tower

/-!
# Restricting a tensor-product algebra action to its factors

A module over `A ⊗[k] B` has commuting actions of `A` and `B`, obtained by restricting
along `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`.
These actions are explicit definitions, since an existing action of a factor may be different.
For `B = Aᵐᵒᵖ`, they are the left and right actions of an ordinary bimodule.

The factor actions agree with the ground-ring action. This supplies the restriction needed for
balanced tensor products of enveloping-algebra modules; it uses Mathlib's scalar restriction
without a new bimodule type.
-/

public section

open scoped TensorProduct
open _root_.Algebra.TensorProduct

namespace TauCeti.Algebra.TensorProduct

variable {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B]
  [Algebra k A] [Algebra k B]
  (M : Type*) [AddCommMonoid M] [Module (A ⊗[k] B) M]

/-- Restrict a tensor-product algebra module to the first factor. -/
abbrev moduleLeft : Module A M :=
  Module.compHom M (includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom

/-- Restrict a tensor-product algebra module to the second factor. -/
abbrev moduleRight : Module B M :=
  Module.compHom M (includeRight : B →ₐ[k] A ⊗[k] B).toRingHom

/-- The first-factor action is the action of `a ⊗ 1`. -/
@[simp]
theorem smul_moduleLeft (a : A) (m : M) :
    letI := moduleLeft (k := k) (A := A) (B := B) M
    a • m = (a ⊗ₜ[k] (1 : B)) • m := rfl

/-- The second-factor action is the action of `1 ⊗ b`. -/
@[simp]
theorem smul_moduleRight (b : B) (m : M) :
    letI := moduleRight (k := k) (A := A) (B := B) M
    b • m = ((1 : A) ⊗ₜ[k] b) • m := rfl

/-- The restricted factor actions commute. -/
theorem moduleSMulCommClass :
    letI := moduleLeft (k := k) (A := A) (B := B) M
    letI := moduleRight (k := k) (A := A) (B := B) M
    SMulCommClass A B M := by
  let _ := moduleLeft (k := k) (A := A) (B := B) M
  let _ := moduleRight (k := k) (A := A) (B := B) M
  refine ⟨fun a b m ↦ ?_⟩
  simp only [smul_moduleLeft, smul_moduleRight, ← mul_smul, tmul_mul_tmul,
    mul_one, one_mul]

section ScalarTower

variable [Module k M] [IsScalarTower k (A ⊗[k] B) M]

/-- Restricting to the first factor respects the ground-ring action. -/
theorem moduleLeftIsScalarTower :
    letI := moduleLeft (k := k) (A := A) (B := B) M
    IsScalarTower k A M := by
  let _ := moduleLeft (k := k) (A := A) (B := B) M
  refine IsScalarTower.of_algebraMap_smul fun r m ↦ ?_
  rw [smul_moduleLeft, ← algebraMap_apply, IsScalarTower.algebraMap_smul]

/-- Restricting to the second factor respects the ground-ring action. -/
theorem moduleRightIsScalarTower :
    letI := moduleRight (k := k) (A := A) (B := B) M
    IsScalarTower k B M := by
  let _ := moduleRight (k := k) (A := A) (B := B) M
  refine IsScalarTower.of_algebraMap_smul fun r m ↦ ?_
  rw [smul_moduleRight, ← algebraMap_apply', IsScalarTower.algebraMap_smul]

end ScalarTower


end TauCeti.Algebra.TensorProduct
