/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Principal subresultant coefficients

This file defines the fixed-bound principal subresultant coefficient of two polynomials.  Its
matrix is obtained from the Sylvester matrix by deleting the first and last `j` rows and the
last `j` columns from each polynomial block.  Thus the coefficient at index zero is the
resultant, while the terminal coefficient is a power of the coefficient at the smaller bound.

Keeping the bounds explicit is essential for specialization: mapping coefficients commutes with
the construction even when the degrees of the mapped polynomials drop.  These determinants are
the scalar data used by subresultant gcd criteria and projection operators.

## Main results

* `Polynomial.psc_zero`: the zeroth principal subresultant coefficient is the resultant.
* `Polynomial.psc_map`: fixed-bound principal subresultant coefficients commute with coefficient
  maps.
* `Polynomial.psc_terminal_left`, `Polynomial.psc_terminal_right`: the terminal determinants are
  powers of the coefficients at the smaller degree bound.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4.
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3.
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The square coefficient matrix whose determinant is the principal subresultant coefficient at
index `j` and formal degree bounds `m` and `n`.

Its columns are `q, X*q, ..., X^(m-j-1)*q`, followed by
`p, X*p, ..., X^(n-j-1)*p`; its rows read the coefficients of degrees
`j, ..., m+n-j-1`.  The definition is meaningful for every `j`; subresultant applications use
`j <= min m n`. -/
def _root_.Polynomial.subresultantMatrix [Semiring R] (p q : R[X]) (m n j : ℕ) :
    Matrix (Fin ((m - j) + (n - j))) (Fin ((m - j) + (n - j))) R :=
  Matrix.of fun i k =>
    k.addCases
      (fun k => if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + n then
        q.coeff (i.val + j - k.val) else 0)
      (fun k => if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + m then
        p.coeff (i.val + j - k.val) else 0)

/-- An entry of a principal subresultant matrix in the first, `q`-column block. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_castAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ)
    (i : Fin ((m - j) + (n - j))) (k : Fin (m - j)) :
    subresultantMatrix p q m n j i (Fin.castAdd (n - j) k) =
      if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + n then
        q.coeff (i.val + j - k.val) else 0 := by
  simp [subresultantMatrix]

/-- An entry of a principal subresultant matrix in the second, `p`-column block. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_natAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ)
    (i : Fin ((m - j) + (n - j))) (k : Fin (n - j)) :
    subresultantMatrix p q m n j i (Fin.natAdd (m - j) k) =
      if (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + m then
        p.coeff (i.val + j - k.val) else 0 := by
  simp [subresultantMatrix]

/-- At index zero, the principal subresultant matrix is Mathlib's Sylvester matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_zero [Semiring R]
    (p q : R[X]) (m n : ℕ) :
    subresultantMatrix p q m n 0 = p.sylvester q m n := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, Polynomial.sylvester]

/-- Mapping coefficients maps every entry of the fixed-bound principal subresultant matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_map [Semiring R] [Semiring S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    subresultantMatrix (p.map f) (q.map f) m n j =
      f.mapMatrix (subresultantMatrix p q m n j) := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, apply_ite f]

/-- The principal subresultant coefficient at index `j` and formal degree bounds `m` and `n`.

The bounds are part of the data: they are not recomputed after coefficient specialization. -/
noncomputable def _root_.Polynomial.psc [CommRing R] (p q : R[X]) (m n j : ℕ) : R :=
  (subresultantMatrix p q m n j).det

/-- The zeroth principal subresultant coefficient is the fixed-bound resultant. -/
@[simp]
theorem _root_.Polynomial.psc_zero [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n 0 = Polynomial.resultant p q m n := by
  simp [psc, Polynomial.resultant]

/-- Principal subresultant coefficients commute with coefficient maps at fixed bounds.  No
degree-preservation hypothesis is needed. -/
@[simp]
theorem _root_.Polynomial.psc_map [CommRing R] [CommRing S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    psc (p.map f) (q.map f) m n j = f (psc p q m n j) := by
  simp [psc, RingHom.map_det]

/-- At equal terminal bounds the principal subresultant coefficient is the empty determinant. -/
@[simp]
theorem _root_.Polynomial.psc_terminal_eq [CommRing R] (p q : R[X]) (m : ℕ) :
    psc p q m m m = 1 := by
  simp [psc, subresultantMatrix]

/-- At the left formal degree bound, the principal coefficient is the corresponding power of the
left polynomial's coefficient.  This is the terminal coefficient when `m ≤ n`; when `n < m`,
both sides reduce to `1` because the index is beyond the subresultant range. -/
@[simp]
theorem _root_.Polynomial.psc_terminal_left [CommRing R]
    (p q : R[X]) (m n : ℕ) :
    psc p q m n m = p.coeff m ^ (n - m) := by
  classical
  let M := subresultantMatrix p q m n m
  have htri : M.IsUpperTriangular := by
    intro i k hki
    induction k using Fin.addCases with
    | left k => exact Fin.elim0 (Fin.cast (by simp) k)
    | right k =>
        have hki' : (k : ℕ) < (i : ℕ) := by
          simpa only [id_eq, Fin.val_natAdd, Nat.sub_self, zero_add] using Fin.lt_def.mp hki
        simp only [M, subresultantMatrix, Matrix.of_apply, Fin.addCases_right]
        split_ifs with h
        · omega
        · rfl
  have hdiag (i : Fin ((m - m) + (n - m))) : M i i = p.coeff m := by
    induction i using Fin.addCases with
    | left i => exact Fin.elim0 (Fin.cast (by simp) i)
    | right i => simp [M, subresultantMatrix]
  rw [psc, Matrix.det_of_isUpperTriangular htri]
  simp_rw [hdiag]
  simp

/-- At the right formal degree bound, the principal coefficient is the corresponding power of the
right polynomial's coefficient.  This is the terminal coefficient when `n ≤ m`; when `m < n`,
both sides reduce to `1` because the index is beyond the subresultant range. -/
@[simp]
theorem _root_.Polynomial.psc_terminal_right [CommRing R]
    (p q : R[X]) (m n : ℕ) :
    psc p q m n n = q.coeff n ^ (m - n) := by
  classical
  let M := subresultantMatrix p q m n n
  have htri : M.IsUpperTriangular := by
    intro i k hki
    induction k using Fin.addCases with
    | left k =>
        have hki' : (k : ℕ) < (i : ℕ) := by
          simpa only [id_eq, Fin.val_castAdd] using Fin.lt_def.mp hki
        simp only [M, subresultantMatrix, Matrix.of_apply, Fin.addCases_left]
        split_ifs with h
        · omega
        · rfl
    | right k => exact Fin.elim0 (Fin.cast (by simp) k)
  have hdiag (i : Fin ((m - n) + (n - n))) : M i i = q.coeff n := by
    induction i using Fin.addCases with
    | left i => simp [M, subresultantMatrix]
    | right i => exact Fin.elim0 (Fin.cast (by simp) i)
  rw [psc, Matrix.det_of_isUpperTriangular htri]
  simp_rw [hdiag]
  simp

/-- The principal coefficient at the terminal subresultant index is a power of the coefficient
at the smaller formal degree bound. -/
theorem _root_.Polynomial.psc_min [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n (min m n) =
      if m ≤ n then p.coeff m ^ (n - m) else q.coeff n ^ (m - n) := by
  by_cases hmn : m ≤ n
  · simp [hmn]
  · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
    simp [hmn, hnm]

end TauCeti
