/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cancelling iterated base change for Lie algebras

This file upgrades the linear equivalence
`TensorProduct.AlgebraTensorModule.cancelBaseChange` to a Lie algebra equivalence
`TauCeti.LieAlgebra.ExtendScalars.cancelBaseChange : A ⊗[S] (S ⊗[R] L) ≃ₗ⁅A⁆ A ⊗[R] L`, for a
tower of commutative rings `R → S → A`.
-/

public section

open scoped TensorProduct

namespace TauCeti.LieAlgebra.ExtendScalars

variable (R S A L : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  [LieRing L] [LieAlgebra R L]

/-- Iterating extension of scalars from `R` through `S` to `A` gives the same Lie algebra as
extending scalars directly from `R` to `A`. -/
def cancelBaseChange : A ⊗[S] (S ⊗[R] L) ≃ₗ⁅A⁆ A ⊗[R] L where
  __ := TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A L
  map_lie' {x y} := by
    induction x with
    | add x x' hx hx' => simp_all [add_lie]
    | tmul a sx =>
      induction sx with
      | add u v hu hv => simp_all [TensorProduct.tmul_add, add_lie]
      | tmul s x =>
        induction y with
        | add y y' hy hy' => simp_all [lie_add]
        | tmul b ty =>
          induction ty with
          | add u v hu hv => simp_all [TensorProduct.tmul_add, lie_add]
          | tmul t y => simp [Algebra.smul_def, mul_mul_mul_comm]

/-- `cancelBaseChange` sends `a ⊗ (s ⊗ x)` to `(s • a) ⊗ x`. -/
@[simp]
theorem cancelBaseChange_tmul (a : A) (s : S) (x : L) :
    cancelBaseChange R S A L (a ⊗ₜ[S] (s ⊗ₜ[R] x)) = (s • a) ⊗ₜ[R] x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S A a x s

/-- The inverse of `cancelBaseChange` sends `a ⊗ x` to `a ⊗ (1 ⊗ x)`. -/
@[simp]
theorem cancelBaseChange_symm_tmul (a : A) (x : L) :
    (cancelBaseChange R S A L).symm (a ⊗ₜ[R] x) = a ⊗ₜ[S] (1 ⊗ₜ[R] x) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S A a x

end TauCeti.LieAlgebra.ExtendScalars
