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
`TensorProduct.AlgebraTensorModule.cancelBaseChange` to a Lie algebra equivalence.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (R S A L : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  [LieRing L] [LieAlgebra R L]

/-- Iterating extension of scalars from `R` through `S` to `A` gives the same Lie algebra as
extending scalars directly from `R` to `A`. -/
def cancelBaseChange : A ⊗[S] (S ⊗[R] L) ≃ₗ⁅A⁆ A ⊗[R] L := by
  let sourceLieRingModule : LieRingModule (A ⊗[S] (S ⊗[R] L)) (A ⊗[S] (S ⊗[R] L)) :=
    inferInstance
  let targetLieRingModule : LieRingModule (A ⊗[R] L) (A ⊗[R] L) := inferInstance
  letI : Bracket (A ⊗[S] (S ⊗[R] L)) (A ⊗[S] (S ⊗[R] L)) :=
    sourceLieRingModule.toBracket
  letI : Bracket (A ⊗[R] L) (A ⊗[R] L) := targetLieRingModule.toBracket
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A L
  have map_lie_tmul (a b : A) (s t : S) (x y : L) :
      e ⁅a ⊗ₜ[S] (s ⊗ₜ[R] x), b ⊗ₜ[S] (t ⊗ₜ[R] y)⁆ =
        ⁅e (a ⊗ₜ[S] (s ⊗ₜ[R] x)), e (b ⊗ₜ[S] (t ⊗ₜ[R] y))⁆ := by
    simp only [LieAlgebra.ExtendScalars.bracket_tmul]
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      LieAlgebra.ExtendScalars.bracket_tmul]
    simp only [Algebra.smul_def, map_mul]
    rw [mul_mul_mul_comm]
  exact
    { __ := e
      map_lie' := by
        intro x y
        -- `LieEquiv.map_lie'` is stated through the inherited `LieHom`; unfold that wrapper to
        -- the local underlying linear equivalence before applying tensor-product induction.
        change e ⁅x, y⁆ = ⁅e x, e y⁆
        induction x using TensorProduct.inductionOn with
        | tmul a sx =>
          induction sx using TensorProduct.inductionOn with
          | tmul s x =>
            induction y using TensorProduct.inductionOn with
            | tmul b ty =>
              induction ty using TensorProduct.inductionOn with
              | tmul t y => exact map_lie_tmul a b s t x y
              | add u v hu hv =>
                  simpa only [TensorProduct.tmul_add, lie_add, map_add] using
                    congrArg₂ (fun p q => p + q) hu hv
            | add u v hu hv =>
                simpa only [lie_add, map_add] using congrArg₂ (fun p q => p + q) hu hv
          | add u v hu hv =>
              simpa only [TensorProduct.tmul_add, add_lie, map_add] using
                congrArg₂ (fun p q => p + q) hu hv
        | add u v hu hv =>
            simpa only [add_lie, map_add] using congrArg₂ (fun p q => p + q) hu hv }

@[simp]
theorem cancelBaseChange_tmul (a : A) (s : S) (x : L) :
    cancelBaseChange R S A L (a ⊗ₜ[S] (s ⊗ₜ[R] x)) = (s • a) ⊗ₜ[R] x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S A a x s

@[simp]
theorem cancelBaseChange_symm_tmul (a : A) (x : L) :
    (cancelBaseChange R S A L).symm (a ⊗ₜ[R] x) = a ⊗ₜ[S] (1 ⊗ₜ[R] x) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S A a x

end TauCeti
