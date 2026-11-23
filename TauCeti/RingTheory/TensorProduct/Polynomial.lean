/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.GroupRingAction
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Equivariance of polynomial base change under coefficient actions

For an `A`-algebra `B` equipped with a commuting `MulSemiringAction` of a monoid `Γ`, Mathlib's
isomorphism `polyEquivTensor A B : B[X] ≃ₐ[A] B ⊗[A] A[X]` is `Γ`-equivariant for the
coefficientwise action on `B[X]` and the left-factor action `TensorProduct.leftHasSMul` on
`B ⊗[A] A[X]`. When `Γ` is a group, this identifies `MulSemiringAction.toRingAut Γ B[X]` with
`TauCeti.Algebra.TensorProduct.baseChangeSemilinearAction A B A[X] Γ`.

## Main declarations

* `polyEquivTensor_symm_smul`: equivariance of `(polyEquivTensor A B).symm` for a monoid action
  on `B`.
* `polyEquivTensor_smul`: equivariance of `polyEquivTensor A B` for a monoid action on `B`.
* `TauCeti.Algebra.TensorProduct.polyEquivTensor_toRingAut` and
  `TauCeti.Algebra.TensorProduct.polyEquivTensor'_toRingAut`: `polyEquivTensor A B` (resp.
  `polyEquivTensor' A B`) intertwines `MulSemiringAction.toRingAut Γ B[X]` with
  `baseChangeSemilinearAction A B A[X] Γ`.

The two monoid-action lemmas live in the root namespace, next to Mathlib's `polyEquivTensor` API,
since they are stated about elements of the Mathlib types `B ⊗[A] A[X]` and `B[X]`.
-/

public section

open Polynomial
open scoped TensorProduct

section MonoidAction

variable {A B Γ : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
  [Monoid Γ] [MulSemiringAction Γ B] [SMulCommClass A Γ B]

/-- `(polyEquivTensor A B).symm : B ⊗[A] A[X] ≃ₐ[A] B[X]` is equivariant for the left-factor
`Γ`-action on `B ⊗[A] A[X]` and the coefficientwise `Γ`-action on `B[X]`. -/
theorem polyEquivTensor_symm_smul (γ : Γ) (z : B ⊗[A] A[X]) :
    (polyEquivTensor A B).symm (γ • z) = γ • (polyEquivTensor A B).symm z := by
  induction z using TensorProduct.inductionOn with
  | tmul b q =>
    rw [TensorProduct.smul_tmul', polyEquivTensor_symm_apply_tmul_eq_smul,
      polyEquivTensor_symm_apply_tmul_eq_smul]
    ext n
    have hmap (a : A) : γ • algebraMap A B a = algebraMap A B a := by
      rw [Algebra.algebraMap_eq_smul_one, ← smul_comm, smul_one]
    simp [smul_eq_mul, smul_mul', hmap]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- `polyEquivTensor A B : B[X] ≃ₐ[A] B ⊗[A] A[X]` is equivariant for the coefficientwise
`Γ`-action on `B[X]` and the left-factor `Γ`-action on `B ⊗[A] A[X]`. -/
theorem polyEquivTensor_smul (γ : Γ) (p : B[X]) :
    polyEquivTensor A B (γ • p) = γ • polyEquivTensor A B p :=
  (polyEquivTensor A B).symm.injective <| by
    rw [AlgEquiv.symm_apply_apply, polyEquivTensor_symm_smul, AlgEquiv.symm_apply_apply]

end MonoidAction

namespace TauCeti.Algebra.TensorProduct

section GroupAction

variable (A B Γ : Type*) [CommSemiring A] [Group Γ]

/-- `polyEquivTensor A B : B[X] ≃ₐ[A] B ⊗[A] A[X]` intertwines the coefficientwise automorphism
action `MulSemiringAction.toRingAut Γ B[X]` with `baseChangeSemilinearAction A B A[X] Γ`. -/
theorem polyEquivTensor_toRingAut [Semiring B] [Algebra A B]
    [MulSemiringAction Γ B] [SMulCommClass Γ A B] (γ : Γ) (p : B[X]) :
    polyEquivTensor A B (MulSemiringAction.toRingAut Γ B[X] γ p) =
      baseChangeSemilinearAction A B A[X] Γ γ (polyEquivTensor A B p) := by
  have _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply,
    polyEquivTensor_smul, _root_.TensorProduct.baseChangeSemilinearAction_eq_smul]

/-- `polyEquivTensor' A B : B[X] ≃ₐ[B] B ⊗[A] A[X]` intertwines the coefficientwise automorphism
action `MulSemiringAction.toRingAut Γ B[X]` with `baseChangeSemilinearAction A B A[X] Γ`. -/
theorem polyEquivTensor'_toRingAut [CommSemiring B] [Algebra A B]
    [MulSemiringAction Γ B] [SMulCommClass Γ A B] (γ : Γ) (p : B[X]) :
    polyEquivTensor' A B (MulSemiringAction.toRingAut Γ B[X] γ p) =
      baseChangeSemilinearAction A B A[X] Γ γ (polyEquivTensor' A B p) := by
  rw [coe_polyEquivTensor', polyEquivTensor_toRingAut]

end GroupAction

end TauCeti.Algebra.TensorProduct
