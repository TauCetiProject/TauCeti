/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.GroupTheory.Perm.Inversion
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.Algebra.Polynomial.Coeff.Basic

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

* `TauCeti.coefficientRow_dotProduct`: a row of shifted polynomial coefficients reads any
  coefficient of `A * q + B * p` from the coefficient vector of `(A, B)`.
* `Polynomial.subresultantMatrix_mulVec`: the matrix acts on a pair of coefficient vectors as
  `(A, B) ↦ A * q + B * p`, read on the coefficients of degrees `j, …, m+n-j-1`.
* `Polynomial.psc_zero`: the zeroth principal subresultant coefficient is the resultant.
* `Polynomial.psc_map_map`: fixed-bound principal subresultant coefficients commute with coefficient
  maps.
* `Polynomial.psc_comm`: swapping the polynomials multiplies by `(-1) ^ ((m - j) * (n - j))`.
* `Polynomial.psc_C_mul_left`, `Polynomial.psc_C_mul_right`: scaling one polynomial by a constant
  scales the coefficient by a power of that constant.
* `Polynomial.psc_left_bound`, `Polynomial.psc_right_bound`: at a formal degree bound, the
  determinant is a power of the coefficient at that bound.
* `Polynomial.psc_min`: the terminal determinant is a power of the coefficient at the smaller
  degree bound.

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

/-- When the formal bounds dominate the degrees, subresultant entries are simply
coefficients of the shifted input polynomials. -/
theorem _root_.Polynomial.subresultantMatrix_apply_eq_coeff [Semiring R]
    {p q : R[X]} {m n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j : ℕ)
    (i k : Fin ((m - j) + (n - j))) :
    subresultantMatrix p q m n j i k =
      k.addCases (fun k => (X ^ k.val * q).coeff (i.val + j))
        (fun k => (X ^ k.val * p).coeff (i.val + j)) := by
  induction k using Fin.addCases <;>
    simp [subresultantMatrix, coeff_X_pow_mul_of_natDegree_le hm,
      coeff_X_pow_mul_of_natDegree_le hn]

/-- At index zero, the principal subresultant matrix is Mathlib's Sylvester matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_zero [Semiring R]
    (p q : R[X]) (m n : ℕ) :
    subresultantMatrix p q m n 0 = p.sylvester q m n := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, Polynomial.sylvester]

/-- Mapping coefficients maps every entry of the fixed-bound principal subresultant matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantMatrix_map_map [Semiring R] [Semiring S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    subresultantMatrix (p.map f) (q.map f) m n j =
      f.mapMatrix (subresultantMatrix p q m n j) := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, apply_ite f]

/-- Swapping the polynomials and their bounds swaps the two column blocks of the principal
subresultant matrix. -/
theorem _root_.Polynomial.subresultantMatrix_comm [Semiring R] (p q : R[X]) (m n j : ℕ) :
    subresultantMatrix p q m n j =
      (subresultantMatrix q p n m j).reindex (finCongr (add_comm (n - j) (m - j))) finAddFlip := by
  ext i k
  induction k using Fin.addCases <;> simp [subresultantMatrix, finAddFlip]

/-- A row of coefficients of shifted `q` and `p` reads the coefficient of degree `d` of
`A * q + B * p`, where the two blocks of `v` are the coefficients of `A` and `B`.
The row lengths are arbitrary, and the formal bounds dominate the actual input degrees. -/
theorem coefficientRow_dotProduct [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (a b d : ℕ) (v : Fin (a + b) → R) :
    (Fin.addCases
      (fun l : Fin a => if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0)
      (fun l : Fin b => if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0))
      ⬝ᵥ v =
      (ofFn a (fun l => v (Fin.castAdd b l)) * q +
        ofFn b (fun l => v (Fin.natAdd a l)) * p).coeff d := by
  simp_rw [← coeff_X_pow_mul_of_natDegree_le hn, ← coeff_X_pow_mul_of_natDegree_le hm]
  simp only [dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    ofFn_eq_sum_monomial, Finset.sum_mul, coeff_add, finsetSum_coeff]
  congr 1 <;> refine Finset.sum_congr rfl fun l _ => ?_ <;>
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, mul_comm]

/-- The principal subresultant matrix acts on a vector as the linear map `(A, B) ↦ A * q + B * p`,
where `A` and `B` are the polynomials whose coefficients are the first `m - j` and the last `n - j`
entries of the vector, read on the coefficients of degrees `j, …, m+n-j-1`.  The formal bounds
must dominate the actual degrees. -/
theorem _root_.Polynomial.subresultantMatrix_mulVec [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j : ℕ)
    (v : Fin ((m - j) + (n - j)) → R) (i : Fin ((m - j) + (n - j))) :
    (subresultantMatrix p q m n j).mulVec v i =
      (ofFn (m - j) (fun k => v (Fin.castAdd (n - j) k)) * q +
        ofFn (n - j) (fun k => v (Fin.natAdd (m - j) k)) * p).coeff (i + j) := by
  exact coefficientRow_dotProduct hm hn (m - j) (n - j) (i.val + j) v

/-- The principal subresultant coefficient at index `j` and formal degree bounds `m` and `n`.

The bounds are part of the data: they are not recomputed after coefficient specialization. -/
noncomputable def _root_.Polynomial.psc [CommRing R] (p q : R[X]) (m n j : ℕ) : R :=
  (subresultantMatrix p q m n j).det

/-- The principal subresultant coefficient is the determinant of the principal subresultant
matrix. -/
theorem _root_.Polynomial.psc_def [CommRing R] (p q : R[X]) (m n j : ℕ) :
    psc p q m n j = (subresultantMatrix p q m n j).det := by
  rw [psc]

/-- The zeroth principal subresultant coefficient is the fixed-bound resultant. -/
@[simp]
theorem _root_.Polynomial.psc_zero [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n 0 = Polynomial.resultant p q m n := by
  simp [psc_def, Polynomial.resultant]

/-- Principal subresultant coefficients commute with coefficient maps at fixed bounds.  No
degree-preservation hypothesis is needed. -/
@[simp]
theorem _root_.Polynomial.psc_map_map [CommRing R] [CommRing S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    psc (p.map f) (q.map f) m n j = f (psc p q m n j) := by
  simp [psc_def, RingHom.map_det]

/-- Swapping the polynomials and their bounds changes the principal subresultant coefficient by
the sign `(-1) ^ ((m - j) * (n - j))`. -/
theorem _root_.Polynomial.psc_comm [CommRing R] (p q : R[X]) (m n j : ℕ) :
    psc p q m n j = (-1) ^ ((m - j) * (n - j)) * psc q p n m j := by
  rw [psc_def, psc_def, subresultantMatrix_comm, Matrix.det_reindex, finCongr_symm,
    sign_finAddFlip_trans_finCongr, mul_comm (n - j)]
  simp

/-- Scaling the left polynomial by a constant `r` scales its `n - j` columns, hence the principal
subresultant coefficient, by `r ^ (n - j)`. -/
theorem _root_.Polynomial.psc_C_mul_left [CommRing R] (p q : R[X]) (r : R) (m n j : ℕ) :
    psc (C r * p) q m n j = r ^ (n - j) * psc p q m n j := by
  have : subresultantMatrix (C r * p) q m n j = .of fun i k =>
      Fin.addCases (fun _ => 1) (fun _ => r) k * subresultantMatrix p q m n j i k := by
    ext i k
    induction k using Fin.addCases <;> simp [subresultantMatrix, coeff_C_mul]
  rw [psc_def, psc_def, this, Matrix.det_mul_row, Fin.prod_univ_add]
  simp

/-- Scaling the right polynomial by a constant `r` scales its `m - j` columns, hence the principal
subresultant coefficient, by `r ^ (m - j)`. -/
theorem _root_.Polynomial.psc_C_mul_right [CommRing R] (p q : R[X]) (r : R) (m n j : ℕ) :
    psc p (C r * q) m n j = r ^ (m - j) * psc p q m n j := by
  calc
    psc p (C r * q) m n j =
        (-1) ^ ((m - j) * (n - j)) * psc (C r * q) p n m j := psc_comm ..
    _ = (-1) ^ ((m - j) * (n - j)) * (r ^ (m - j) * psc q p n m j) := by
      rw [psc_C_mul_left]
    _ = r ^ (m - j) * ((-1) ^ ((m - j) * (n - j)) * psc q p n m j) := by
      ac_rfl
    _ = r ^ (m - j) * psc p q m n j := by rw [← psc_comm]

/-- At the left formal degree bound, the principal coefficient is the corresponding power of the
left polynomial's coefficient.  This is the terminal coefficient when `m ≤ n`; when `n < m`,
both sides reduce to `1` because the index is beyond the subresultant range. -/
@[simp]
theorem _root_.Polynomial.psc_left_bound [CommRing R]
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
  rw [psc_def, Matrix.det_of_isUpperTriangular htri]
  simp_rw [hdiag]
  simp

/-- At the right formal degree bound, the principal coefficient is the corresponding power of the
right polynomial's coefficient.  This is the terminal coefficient when `n ≤ m`; when `m < n`,
both sides reduce to `1` because the index is beyond the subresultant range. -/
@[simp]
theorem _root_.Polynomial.psc_right_bound [CommRing R]
    (p q : R[X]) (m n : ℕ) :
    psc p q m n n = q.coeff n ^ (m - n) := by
  rw [psc_comm, psc_left_bound]
  simp

/-- The principal coefficient at the terminal subresultant index is a power of the coefficient
at the smaller formal degree bound. -/
@[simp]
theorem _root_.Polynomial.psc_min [CommRing R] (p q : R[X]) (m n : ℕ) :
    psc p q m n (min m n) =
      if m ≤ n then p.coeff m ^ (n - m) else q.coeff n ^ (m - n) := by
  by_cases hmn : m ≤ n
  · simp [hmn]
  · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
    simp [hmn, hnm]

end TauCeti
