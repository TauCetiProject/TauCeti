/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Ring

/-!
# Determinants of invariant hyperplane restrictions

Suppose the columns of `C` give coordinates on an invariant rank-`n` submodule
contained in the kernel of a covector `w`, and `A * C = C * X` expresses the
restriction of `A` in those coordinates. If `A` kills `u`, with last coordinate
one, then the weighted determinant `w (Fin.last n) * det X` equals the pairing
of `w` with `u` times the last principal minor of `A`.

The determinant of the first rows of `C` must be a unit. Neither the last coordinate
of `w` nor the pairing need be a unit, or even nonzero. This form therefore
works over arbitrary commutative rings, including at specializations where the
right kernel lies in the invariant hyperplane.

The calculation uses Mathlib's rank-one determinant identity
`Matrix.det_one_add_replicateCol_mul_replicateRow` (Weinstein--Aronszajn).
-/

public section

open Finset

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The determinant of an invariant hyperplane restriction in terms of a principal minor.
The columns of `C` lie in the kernel of `w`, their first `n` coordinates form an invertible
matrix, and `X` intertwines `A` with those columns. A right null vector `u` is normalized
by `u (Fin.last n) = 1`. Neither `w (Fin.last n)` nor `w ⬝ᵥ u` needs to be a unit
or nonzero. -/
theorem det_of_intertwining_of_mulVec_eq_zero
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (C : Matrix (Fin (n + 1)) (Fin n) R) (X : Matrix (Fin n) (Fin n) R)
    (u w : Fin (n + 1) → R)
    (hu : A *ᵥ u = 0) (hulast : u (Fin.last n) = 1)
    (hw : w ᵥ* C = 0)
    (hC : IsUnit (C.submatrix Fin.castSucc id).det) (hAX : A * C = C * X) :
    w (Fin.last n) * X.det = (w ⬝ᵥ u) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  let B := A.submatrix Fin.castSucc Fin.castSucc
  let D := C.submatrix Fin.castSucc id
  let v : Fin n → R := fun i => u i.castSucc
  let c : Fin n → R := fun j => C (Fin.last n) j
  let z : Fin n → R := -(c ᵥ* D⁻¹)
  have hcol (i : Fin n) : A i.castSucc (Fin.last n) = -(B *ᵥ v) i := by
    have h := congrFun hu i.castSucc
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, hulast, mul_one,
      Pi.zero_apply] at h
    exact eq_neg_of_add_eq_zero_right h
  have hrow (j : Fin n) : C (Fin.last n) j = -(z ᵥ* D) j := by
    simp only [z, neg_vecMul, vecMul_vecMul, nonsing_inv_mul D hC, vecMul_one,
      Pi.neg_apply, neg_neg, c]
  -- Normalize the column coordinates using D, without dividing by a coordinate of w.
  have hwrow : (fun i : Fin n => w i.castSucc) ᵥ* D = -(w (Fin.last n) • c) := by
    ext j
    have h := congrFun hw j
    simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, Pi.zero_apply] at h
    simpa only [vecMul, dotProduct, D, submatrix_apply, id_eq, Pi.neg_apply,
      Pi.smul_apply, smul_eq_mul, c] using eq_neg_of_add_eq_zero_left h
  have hwtop : (fun i : Fin n => w i.castSucc) = w (Fin.last n) • z := by
    have h := congrArg (fun r : Fin n → R => r ᵥ* D⁻¹) hwrow
    simpa only [vecMul_vecMul, mul_nonsing_inv D hC, vecMul_one, neg_vecMul,
      smul_vecMul, z, smul_neg] using h
  have hinter : B * (1 + vecMulVec v z) * D = D * X := by
    ext i j
    have h := congrFun (congrFun hAX i.castSucc) j
    simp only [mul_apply, Fin.sum_univ_castSucc, hcol, hrow] at h
    rw [mul_add, mul_one, add_mul, mul_vecMulVec, vecMulVec_mul]
    simpa only [add_apply, mul_apply, vecMulVec_apply, neg_mul_neg,
      B, D, submatrix_apply, id_eq] using h
  have hdet : (1 + vecMulVec v z).det = 1 + z ⬝ᵥ v := by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
  have hX : X.det = B.det * (1 + z ⬝ᵥ v) := by
    have h := congrArg det hinter
    rw [det_mul, det_mul, hdet, det_mul] at h
    exact hC.mul_right_cancel (by simpa only [D, mul_comm, mul_left_comm, mul_assoc] using h.symm)
  have hpair : w (Fin.last n) * (1 + z ⬝ᵥ v) = w ⬝ᵥ u := by
    have hwtop_apply (i : Fin n) : w i.castSucc = w (Fin.last n) * z i :=
      congrFun hwtop i
    simp only [dotProduct, Fin.sum_univ_castSucc, hulast, mul_one, hwtop_apply,
      v, mul_add, Finset.mul_sum, mul_assoc]
    ring
  rw [hX, mul_left_comm, hpair, mul_comm]

end Matrix
