/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Determinants of invariant hyperplane restrictions

Suppose the columns of `C` give coordinates on the kernel of a covector `w`, and
`A * C = C * X` expresses the restriction of `A` in those coordinates. If `A` kills
`u`, with last coordinate one, then the determinant of `X` is determined by the
last principal minor of `A` and the pairing of `w` with `u`.

The last coordinate of `w` and the determinant of the first rows of `C` must be
units. The pairing itself need not be a unit, or even nonzero. This form therefore
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
by `u (Fin.last n) = 1`. No nonvanishing assumption on `w ⬝ᵥ u` is required. -/
theorem det_of_intertwining_of_mulVec_eq_zero
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (C : Matrix (Fin (n + 1)) (Fin n) R) (X : Matrix (Fin n) (Fin n) R)
    (u w : Fin (n + 1) → R)
    (hu : A *ᵥ u = 0) (hulast : u (Fin.last n) = 1)
    (hw : w ᵥ* C = 0) (hwlast : IsUnit (w (Fin.last n)))
    (hC : IsUnit (C.submatrix Fin.castSucc id).det) (hAX : A * C = C * X) :
    w (Fin.last n) * X.det = (w ⬝ᵥ u) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  obtain ⟨a, ha⟩ := hwlast
  have hwlast : w (Fin.last n) = a := ha.symm
  rw [hwlast]
  let B := A.submatrix Fin.castSucc Fin.castSucc
  let D := C.submatrix Fin.castSucc id
  let v : Fin n → R := fun i => u i.castSucc
  let z : Fin n → R := fun i => ((a⁻¹ : Rˣ) : R) * w i.castSucc
  have hcol (i : Fin n) : A i.castSucc (Fin.last n) = -(B *ᵥ v) i := by
    have h := congrFun hu i.castSucc
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, hulast, mul_one,
      Pi.zero_apply] at h
    exact eq_neg_of_add_eq_zero_right h
  have hrow (j : Fin n) : C (Fin.last n) j = -(z ᵥ* D) j := by
    have h := congrFun hw j
    simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, hwlast, Pi.zero_apply] at h
    have hsum : (z ᵥ* D) j = ((a⁻¹ : Rˣ) : R) *
        ∑ i : Fin n, w i.castSucc * C i.castSucc j := by
      simp only [vecMul, dotProduct, z, D, submatrix_apply, id_eq, mul_assoc,
        Finset.mul_sum]
    rw [hsum]
    have ha := Units.inv_mul a
    linear_combination ((a⁻¹ : Rˣ) : R) * h - C (Fin.last n) j * ha
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
  have hpair : (a : R) * (1 + z ⬝ᵥ v) = w ⬝ᵥ u := by
    simp only [dotProduct, Fin.sum_univ_castSucc, hwlast, hulast, mul_one]
    simp only [z, v, mul_add, mul_one, Finset.mul_sum, ← mul_assoc, Units.mul_inv,
      one_mul]
    ring
  rw [hX, mul_left_comm, hpair, mul_comm]

end Matrix
