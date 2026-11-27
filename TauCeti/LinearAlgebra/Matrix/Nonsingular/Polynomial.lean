/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Matrix.Mul
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Right cancellation by a matrix pencil

A pencil `A + X B` acts injectively by right multiplication on matrices of polynomials
if `B` acts injectively on coefficient matrices. In particular the monic pencil `A + X I`
can be cancelled even over a noncommutative ring with zero divisors. This is the cancellation
used when a central indeterminate is adjoined in the quantum Jacobi identity; see
L. Alpöge's `Formalism.FourierDecayAlt.Qr.QJacobi`.
-/

public section

open Polynomial

namespace Matrix

variable {m n R : Type*} [Fintype n] [Semiring R]

/-- If the linear coefficient of a matrix pencil is right regular, then so is the pencil.
No commutativity or absence of zero divisors in the coefficient ring is required. -/
theorem isRightRegular_map_C_add_X_smul [IsLeftCancelAdd R] (A B : Matrix n n R)
    (hB : IsRightRegular B) : IsRightRegular (A.map C + (X : R[X]) • B.map C) := by
  intro P Q hPQ
  let D := Finset.univ.sup fun i : n × n ↦ max (P i.1 i.2).natDegree (Q i.1 i.2).natDegree
  have hD (i j : n) : max (P i j).natDegree (Q i j).natDegree ≤ D :=
    Finset.le_sup (f := fun ij : n × n ↦ max (P ij.1 ij.2).natDegree (Q ij.1 ij.2).natDegree)
      (Finset.mem_univ (i, j))
  have habove (d : ℕ) (hd : D < d) :
      P.map (fun p ↦ p.coeff d) = Q.map (fun p ↦ p.coeff d) := by
    ext i j
    rw [map_apply, map_apply, coeff_eq_zero_of_natDegree_lt ((le_max_left _ _).trans_lt
      ((hD i j).trans_lt hd)), coeff_eq_zero_of_natDegree_lt ((le_max_right _ _).trans_lt
      ((hD i j).trans_lt hd))]
  -- The constant term contributes equally once the next higher coefficients agree.
  have hstep (d : ℕ) (h : P.map (fun p ↦ p.coeff (d + 1)) = Q.map (fun p ↦ p.coeff (d + 1))) :
      P.map (fun p ↦ p.coeff d) = Q.map (fun p ↦ p.coeff d) := by
    have hc := congrArg (fun M : Matrix n n R[X] ↦ M.map (fun p ↦ p.coeff (d + 1))) hPQ
    rw [map_coeff_mul_map_C_add_X_smul, map_coeff_mul_map_C_add_X_smul, h] at hc
    exact hB (add_left_cancel hc)
  ext i j d
  have hcoeff : P.map (fun p ↦ p.coeff d) = Q.map (fun p ↦ p.coeff d) := by
    by_cases hd : d ≤ D + 1
    · induction hd using Nat.decreasingInduction with
      | self => exact habove _ (Nat.lt_succ_self _)
      | of_succ _ _ ih => exact hstep _ ih
    · exact habove _ (by omega)
  exact congrArg (fun M : Matrix n n R ↦ M i j) hcoeff

/-- Adding a central indeterminate to the diagonal of a constant matrix gives a
right-cancellable polynomial matrix. -/
theorem isRightRegular_map_C_add_diagonal_X [IsLeftCancelAdd R] [DecidableEq n]
    (A : Matrix n n R) :
    IsRightRegular (A.map C + diagonal (fun _ ↦ (X : R[X]))) := by
  have h1 : IsRightRegular (1 : Matrix n n R) := fun _ _ h ↦ by simpa only [mul_one] using h
  have h := isRightRegular_map_C_add_X_smul A 1 h1
  have hc : (1 : Matrix n n R).map (C : R →+* R[X]) = 1 := (C.mapMatrix).map_one
  simpa only [hc, smul_one_eq_diagonal, smul_eq_mul, mul_one] using h

end Matrix
