/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The matrices `1 - u ⊗ v`

This file develops the matrix calculus for the rank-one perturbations `1 - vecMulVec u v` of the
identity: their products, the commutation and braid relations, the quadratic relation, the
inverse, the determinant, and the resulting element of the general linear group. Everything is
stated for plain pairs of vectors, and every hypothesis is a value of one of the pairings
`v ⬝ᵥ u` of the vectors involved.

The products, the commutation and braid relations, the two-sided inverse and the general linear
group element hold over an arbitrary ring, where the scalar of a product sits between the two
vectors: `vecMulVec u (c • v)` has entries `u i * c * v j`. The quadratic relation, the
determinant, the matrix inverse `⁻¹` and the induced linear automorphisms are stated over a
commutative ring.

## Main definitions

* `TauCeti.oneSubVecMulVecGL`: `1 - vecMulVec u v` as an element of the general linear group, when
  its self-pairing `v ⬝ᵥ u` is `t + 1` for a unit `t`.

## Main results

* `TauCeti.one_sub_vecMulVec_mul_comm` and `TauCeti.one_sub_vecMulVec_braid`: the commutation and
  braid relations, from the values of the pairings.
* `TauCeti.one_sub_vecMulVec_mul_self`: the quadratic relation.
* `TauCeti.det_one_sub_vecMulVec` and `TauCeti.inv_one_sub_vecMulVec`: the determinant and the
  inverse.
* `TauCeti.oneSubVecMulVecGL_toLinearEquiv_apply` and its inverse counterpart compute the
  induced linear automorphism on column vectors.
-/

public section

open Matrix

namespace TauCeti

variable {R α : Type*} [Fintype α] [DecidableEq α]

section Ring

variable [Ring R]

/-- The product of two rank-one perturbations of the identity. -/
theorem one_sub_vecMulVec_mul_one_sub_vecMulVec (u₁ v₁ u₂ v₂ : α → R) :
    (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) =
      1 - vecMulVec u₁ v₁ - vecMulVec u₂ v₂ + vecMulVec u₁ ((v₁ ⬝ᵥ u₂) • v₂) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec]
  abel

/-- Two rank-one perturbations of the identity commute when their cross-pairings vanish. -/
theorem one_sub_vecMulVec_mul_comm {u₁ v₁ u₂ v₂ : α → R} (h₁₂ : v₁ ⬝ᵥ u₂ = 0)
    (h₂₁ : v₂ ⬝ᵥ u₁ = 0) :
    (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) =
      (1 - vecMulVec u₂ v₂) * (1 - vecMulVec u₁ v₁) := by
  simp only [one_sub_vecMulVec_mul_one_sub_vecMulVec, h₁₂, h₂₁, zero_smul, vecMulVec_zero]
  abel

/-- Two rank-one perturbations of the identity obey the braid relation when each self-pairing
equals one plus the product of the cross-pairings, taken in the order starting with its own
row vector. -/
theorem one_sub_vecMulVec_braid {u₁ v₁ u₂ v₂ : α → R}
    (h₁ : v₁ ⬝ᵥ u₁ = 1 + (v₁ ⬝ᵥ u₂) * (v₂ ⬝ᵥ u₁))
    (h₂ : v₂ ⬝ᵥ u₂ = 1 + (v₂ ⬝ᵥ u₁) * (v₁ ⬝ᵥ u₂)) :
    (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) * (1 - vecMulVec u₁ v₁) =
      (1 - vecMulVec u₂ v₂) * (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec, smul_dotProduct,
    smul_eq_mul, h₁, h₂, add_smul, one_smul, vecMulVec_add]
  abel

/-- A right inverse for a rank-one perturbation of the identity whose self-pairing is `t + 1`. -/
theorem one_sub_vecMulVec_mul_inv (t : Rˣ) {u v : α → R} (h : v ⬝ᵥ u = (t : R) + 1) :
    (1 - vecMulVec u v) * (1 - vecMulVec u (((t⁻¹ : Rˣ) : R) • v)) = 1 := by
  simp only [one_sub_vecMulVec_mul_one_sub_vecMulVec, h, smul_smul, add_mul, one_mul,
    Units.mul_inv, add_smul, one_smul, vecMulVec_add]
  abel

/-- A left inverse for a rank-one perturbation of the identity whose self-pairing is `t + 1`. -/
theorem one_sub_vecMulVec_inv_mul (t : Rˣ) {u v : α → R} (h : v ⬝ᵥ u = (t : R) + 1) :
    (1 - vecMulVec u (((t⁻¹ : Rˣ) : R) • v)) * (1 - vecMulVec u v) = 1 := by
  simp only [one_sub_vecMulVec_mul_one_sub_vecMulVec, smul_dotProduct, smul_eq_mul, h, mul_add,
    Units.inv_mul, mul_one, add_smul, one_smul, vecMulVec_add]
  abel

/-- A rank-one perturbation of the identity as an element of the general linear group, when its
self-pairing is `t + 1`. -/
def oneSubVecMulVecGL (t : Rˣ) (u v : α → R) (h : v ⬝ᵥ u = (t : R) + 1) : GL α R where
  val := 1 - vecMulVec u v
  inv := 1 - vecMulVec u (((t⁻¹ : Rˣ) : R) • v)
  val_inv := one_sub_vecMulVec_mul_inv t h
  inv_val := one_sub_vecMulVec_inv_mul t h

/-- The matrix underlying `TauCeti.oneSubVecMulVecGL`. -/
@[simp]
theorem coe_oneSubVecMulVecGL (t : Rˣ) (u v : α → R) (h : v ⬝ᵥ u = (t : R) + 1) :
    (oneSubVecMulVecGL t u v h : Matrix α α R) = 1 - vecMulVec u v :=
  (rfl)

/-- The matrix underlying the inverse of `TauCeti.oneSubVecMulVecGL`. -/
@[simp]
theorem coe_oneSubVecMulVecGL_inv (t : Rˣ) (u v : α → R) (h : v ⬝ᵥ u = (t : R) + 1) :
    (↑(oneSubVecMulVecGL t u v h)⁻¹ : Matrix α α R) = 1 - vecMulVec u (((t⁻¹ : Rˣ) : R) • v) :=
  (rfl)

end Ring

variable [CommRing R]

/-- The quadratic relation for a rank-one perturbation of the identity whose self-pairing is
`t + 1`. -/
theorem one_sub_vecMulVec_mul_self (t : R) {u v : α → R} (h : v ⬝ᵥ u = t + 1) :
    (1 - vecMulVec u v) * (1 - vecMulVec u v) = (1 - t) • (1 - vecMulVec u v) + t • 1 := by
  rw [one_sub_vecMulVec_mul_one_sub_vecMulVec, h, vecMulVec_smul]
  module

/-- The determinant of a rank-one perturbation of the identity in terms of its self-pairing. -/
@[simp]
theorem det_one_sub_vecMulVec (u v : α → R) : (1 - vecMulVec u v).det = 1 - v ⬝ᵥ u := by
  rw [sub_eq_add_neg, ← neg_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
  ring

/-- The inverse of a rank-one perturbation of the identity whose self-pairing is `t + 1`.

This is not a `simp` lemma: the unit `t` occurs only in the right-hand side and in the
hypothesis, so `simp` cannot infer it from the left-hand side. Consumers that fix `t` — such as
`TauCeti.KnotTheory.inv_reducedBurauColMatrix` — carry the `simp` attribute instead. -/
theorem inv_one_sub_vecMulVec (t : Rˣ) {u v : α → R} (h : v ⬝ᵥ u = (t : R) + 1) :
    (1 - vecMulVec u v)⁻¹ = 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec u v :=
  Matrix.inv_eq_right_inv <| by rw [← vecMulVec_smul, one_sub_vecMulVec_mul_inv t h]

/-- The induced linear automorphism subtracts the row pairing in the column direction. -/
@[simp]
theorem oneSubVecMulVecGL_toLinearEquiv_apply (t : Rˣ) (u v x : α → R)
    (h : v ⬝ᵥ u = (t : R) + 1) :
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (α → R)
      (Matrix.GeneralLinearGroup.toLin (oneSubVecMulVecGL t u v h))) x =
        x - (v ⬝ᵥ x) • u := by
  simp only [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply, coe_oneSubVecMulVecGL,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

/-- The inverse induced automorphism rescales the same row pairing by the inverse unit. -/
@[simp]
theorem oneSubVecMulVecGL_toLinearEquiv_symm_apply (t : Rˣ) (u v x : α → R)
    (h : v ⬝ᵥ u = (t : R) + 1) :
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (α → R)
      (Matrix.GeneralLinearGroup.toLin (oneSubVecMulVecGL t u v h))).symm x =
        x - ((↑t⁻¹ : R) * (v ⬝ᵥ x)) • u := by
  rw [LinearEquiv.symm_apply_eq, oneSubVecMulVecGL_toLinearEquiv_apply]
  have ht : (↑t⁻¹ : R) * (v ⬝ᵥ x) * t = v ⬝ᵥ x := by rw [mul_right_comm, Units.inv_mul, one_mul]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, h, mul_add, mul_one, ht]
  module

end TauCeti
