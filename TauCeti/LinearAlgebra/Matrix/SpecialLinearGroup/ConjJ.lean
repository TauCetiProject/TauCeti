/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Conjugation by a coordinate reflection in the special linear group

Conjugating a two-by-two matrix by `diag(-1, 1)` negates both off-diagonal entries and
preserves its determinant. The canonical `conjJ` operation is available over every commutative
ring, for modular-form conjugation and reflection of binary quadratic forms.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- Conjugation by the coordinate reflection `diag(-1, 1)` in `SL₂(R)`. -/
def conjJ (γ : SL(2, R)) : SL(2, R) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    simpa only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, neg_mul_neg] using γ.det_coe⟩

@[simp] theorem coe_conjJ (γ : SL(2, R)) :
    (conjJ γ : Matrix (Fin 2) (Fin 2) R) = !![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1] := (rfl)

/-- Coordinate conjugation preserves the identity. -/
@[simp] theorem conjJ_one : conjJ (1 : SL(2, R)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Coordinate conjugation preserves multiplication. -/
@[simp] theorem conjJ_mul (γ δ : SL(2, R)) : conjJ (γ * δ) = conjJ γ * conjJ δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- Coordinate conjugation is an involution. -/
@[simp] theorem conjJ_conjJ (γ : SL(2, R)) : conjJ (conjJ γ) = γ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Coordinate conjugation as an involutive group automorphism. -/
def conjJMulAut : MulAut (SL(2, R)) where
  toFun := conjJ
  invFun := conjJ
  left_inv := conjJ_conjJ
  right_inv := conjJ_conjJ
  map_mul' := conjJ_mul

@[simp] theorem conjJMulAut_apply (γ : SL(2, R)) : conjJMulAut γ = conjJ γ := by rfl

@[simp] theorem conjJMulAut_symm_apply (γ : SL(2, R)) :
    conjJMulAut.symm γ = conjJ γ := by rfl

/-- The coordinate reflection has square equal to the identity automorphism. -/
@[simp] theorem conjJMulAut_mul_self :
    (conjJMulAut : MulAut (SL(2, R))) * conjJMulAut = 1 := by
  ext γ
  simp

/-- Coordinate conjugation preserves inverses. -/
@[simp] theorem conjJ_inv (γ : SL(2, R)) : conjJ γ⁻¹ = (conjJ γ)⁻¹ :=
  map_inv (conjJMulAut : MulAut (SL(2, R))) γ

/-- Coordinate conjugation commutes with a ring homomorphism on coefficients. -/
@[simp] theorem map_conjJ {S : Type*} [CommRing S] (f : R →+* S) (γ : SL(2, R)) :
    map f (conjJ γ) = conjJ (map f γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Matrix.SpecialLinearGroup
