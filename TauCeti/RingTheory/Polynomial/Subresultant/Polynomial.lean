/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import TauCeti.RingTheory.Polynomial.Subresultant.Basic

/-!
# Subresultant polynomials

This file defines the fixed-bound subresultant polynomial of two polynomials.  Its coefficient
of degree `k ≤ j` is the Sylvester minor obtained by replacing the first row of the principal
subresultant matrix at index `j` by the row of coefficients of degree `k`.  At a strict index,
its coefficient of degree `j` is the principal subresultant coefficient.

The construction retains explicit degree bounds, so it commutes with coefficient maps even when
specialization lowers the degrees.  Its degree bound and top coefficient identify the scalar minor
that controls the subresultant gcd criterion.

## Main results

* `Polynomial.subresultant_coeff`: the coefficients are the prescribed minors through
  degree `j`, and vanish above `j`.
* `Polynomial.degree_subresultant_le`: the subresultant polynomial has degree at most
  `j`.
* `Polynomial.subresultant_map_map`: fixed-bound subresultant polynomials commute with
  coefficient maps.
* `Polynomial.subresultant_comm`: swapping the inputs gives the Sylvester block-swap
  sign.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4.
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3.
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The coefficient matrix defining the coefficient of degree `k` in the subresultant polynomial
at index `j` and formal degree bounds `m` and `n`.

The first row of `subresultantMatrix p q m n j`, which reads coefficients of degree `j`, is
replaced by the row reading coefficients of degree `k`.  Applications use `k ≤ j`. -/
def _root_.Polynomial.subresultantCoeffMatrix [Semiring R]
    (p q : R[X]) (m n j k : ℕ) :
    Matrix (Fin ((m - j) + (n - j))) (Fin ((m - j) + (n - j))) R :=
  Matrix.of fun i l =>
    let d := if i.val = 0 then k else i.val + j
    l.addCases
      (fun l => if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0)
      (fun l => if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0)

/-- An entry in the first, `q`-column block of a subresultant coefficient matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantCoeffMatrix_castAdd [Semiring R]
    (p q : R[X]) (m n j k : ℕ) (i : Fin ((m - j) + (n - j))) (l : Fin (m - j)) :
    subresultantCoeffMatrix p q m n j k i (Fin.castAdd (n - j) l) =
      let d := if i.val = 0 then k else i.val + j
      if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0 := by
  simp [subresultantCoeffMatrix]

/-- An entry in the second, `p`-column block of a subresultant coefficient matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantCoeffMatrix_natAdd [Semiring R]
    (p q : R[X]) (m n j k : ℕ) (i : Fin ((m - j) + (n - j))) (l : Fin (n - j)) :
    subresultantCoeffMatrix p q m n j k i (Fin.natAdd (m - j) l) =
      let d := if i.val = 0 then k else i.val + j
      if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0 := by
  simp [subresultantCoeffMatrix]

/-- At `k = j`, the coefficient matrix is the principal subresultant matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantCoeffMatrix_index [Semiring R]
    (p q : R[X]) (m n j : ℕ) :
    subresultantCoeffMatrix p q m n j j = subresultantMatrix p q m n j := by
  ext i l
  induction l using Fin.addCases with
  | left l =>
      rw [subresultantCoeffMatrix_castAdd, subresultantMatrix_castAdd]
      by_cases hi : i.val = 0 <;> simp [hi]
  | right l =>
      rw [subresultantCoeffMatrix_natAdd, subresultantMatrix_natAdd]
      by_cases hi : i.val = 0 <;> simp [hi]

/-- Mapping coefficients maps every entry of a fixed-bound subresultant coefficient matrix. -/
@[simp]
theorem _root_.Polynomial.subresultantCoeffMatrix_map_map [Semiring R] [Semiring S]
    (f : R →+* S) (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeffMatrix (p.map f) (q.map f) m n j k =
      f.mapMatrix (subresultantCoeffMatrix p q m n j k) := by
  ext i l
  induction l using Fin.addCases <;>
    simp [subresultantCoeffMatrix, apply_ite f]

/-- Swapping the polynomials and bounds swaps the column blocks of every subresultant coefficient
matrix. -/
theorem _root_.Polynomial.subresultantCoeffMatrix_comm [Semiring R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeffMatrix p q m n j k =
      (subresultantCoeffMatrix q p n m j k).reindex
        (finCongr (add_comm (n - j) (m - j)))
        (finSumFinEquiv.symm.trans <| (Equiv.sumComm _ _).trans finSumFinEquiv) := by
  ext i l
  induction l using Fin.addCases <;> simp [subresultantCoeffMatrix]

/-- The scalar minor used as the coefficient of degree `k` in the subresultant polynomial at
index `j`. -/
noncomputable def _root_.Polynomial.subresultantCoeff [CommRing R]
    (p q : R[X]) (m n j k : ℕ) : R :=
  (subresultantCoeffMatrix p q m n j k).det

/-- A subresultant coefficient is the determinant of its coefficient matrix. -/
theorem _root_.Polynomial.subresultantCoeff_def [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff p q m n j k = (subresultantCoeffMatrix p q m n j k).det := by
  rw [subresultantCoeff]

/-- The coefficient minor at `k = j` is the principal subresultant coefficient. -/
@[simp]
theorem _root_.Polynomial.subresultantCoeff_index [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    subresultantCoeff p q m n j j = psc p q m n j := by
  simp [subresultantCoeff_def, psc_def]

/-- Subresultant coefficient minors commute with coefficient maps at fixed bounds. -/
@[simp]
theorem _root_.Polynomial.subresultantCoeff_map_map [CommRing R] [CommRing S]
    (f : R →+* S) (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff (p.map f) (q.map f) m n j k =
      f (subresultantCoeff p q m n j k) := by
  simp [subresultantCoeff_def, RingHom.map_det]

set_option backward.defeqAttrib.useBackward true in
private theorem sign_blockSwap (m n : ℕ) :
    Equiv.Perm.sign
        ((finSumFinEquiv.symm.trans <| (Equiv.sumComm _ _).trans finSumFinEquiv).trans
          (finCongr (add_comm n m)).symm) =
      (-1) ^ (m * n) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  dsimp
  simp only [Fin.cast_lt_cast]
  simp_rw [← finSumFinEquiv.prod_comp, ← Finset.prod_map_equiv finSumFinEquiv.symm]
  simp only [Equiv.symm_apply_apply, ← Fin.val_fin_lt, Equiv.symm_symm, Function.comp_apply,
    ← Finset.prod_ite_mem_eq (Finset.map _ _), Finset.mem_map_equiv, Finset.mem_Ioi,
    Fintype.prod_sum_type, finSumFinEquiv_apply_left, Fin.val_castAdd, Sum.swap_inl,
    finSumFinEquiv_apply_right, Fin.val_natAdd, Sum.swap_inr, add_lt_add_iff_left,
    ← ite_not (α := ℤˣ) (p := _ < _) (y := 1), ← ite_and, and_not_self]
  simp [(Fin.isLt _).trans_le, (Fin.isLt _).le.trans, pow_mul]

/-- Swapping the inputs changes every coefficient minor by the Sylvester block-swap sign. -/
theorem _root_.Polynomial.subresultantCoeff_comm [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff p q m n j k =
      (-1) ^ ((m - j) * (n - j)) * subresultantCoeff q p n m j k := by
  rw [subresultantCoeff_def, subresultantCoeff_def, subresultantCoeffMatrix_comm,
    Matrix.det_reindex, sign_blockSwap]
  simp

/-- Scaling the left polynomial by `r` scales every coefficient minor by `r ^ (n - j)`. -/
theorem _root_.Polynomial.subresultantCoeff_C_mul_left [CommRing R]
    (p q : R[X]) (r : R) (m n j k : ℕ) :
    subresultantCoeff (C r * p) q m n j k =
      r ^ (n - j) * subresultantCoeff p q m n j k := by
  have hmatrix : subresultantCoeffMatrix (C r * p) q m n j k = .of fun i l =>
      Fin.addCases (fun _ => 1) (fun _ => r) l * subresultantCoeffMatrix p q m n j k i l := by
    ext i l
    induction l using Fin.addCases <;> simp [subresultantCoeffMatrix, coeff_C_mul]
  rw [subresultantCoeff_def, subresultantCoeff_def, hmatrix, Matrix.det_mul_row,
    Fin.prod_univ_add]
  simp

/-- Scaling the right polynomial by `r` scales every coefficient minor by `r ^ (m - j)`. -/
theorem _root_.Polynomial.subresultantCoeff_C_mul_right [CommRing R]
    (p q : R[X]) (r : R) (m n j k : ℕ) :
    subresultantCoeff p (C r * q) m n j k =
      r ^ (m - j) * subresultantCoeff p q m n j k := by
  have hmatrix : subresultantCoeffMatrix p (C r * q) m n j k = .of fun i l =>
      Fin.addCases (fun _ => r) (fun _ => 1) l * subresultantCoeffMatrix p q m n j k i l := by
    ext i l
    induction l using Fin.addCases <;> simp [subresultantCoeffMatrix, coeff_C_mul]
  rw [subresultantCoeff_def, subresultantCoeff_def, hmatrix, Matrix.det_mul_row,
    Fin.prod_univ_add]
  simp

/-- The fixed-bound subresultant polynomial at index `j`.

Its coefficient of degree `k ≤ j` is `subresultantCoeff p q m n j k`; all coefficients above
`j` vanish.  Subresultant polynomials occur only at strict indices `j < min m n`; outside that
range this definition is zero.  In particular, it does not turn a terminal empty determinant
into a polynomial, since terminal data is represented by `psc`. -/
noncomputable def _root_.Polynomial.subresultant [CommRing R]
    (p q : R[X]) (m n j : ℕ) : R[X] := by
  classical
  exact if j < min m n then
      ofFn (j + 1) fun k => subresultantCoeff p q m n j k
    else 0

/-- The coefficient formula for a fixed-bound subresultant polynomial. -/
@[simp]
theorem _root_.Polynomial.subresultant_coeff [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    (subresultant p q m n j).coeff k =
      if j < min m n ∧ k ≤ j then subresultantCoeff p q m n j k else 0 := by
  by_cases hj : j < min m n
  · by_cases hkj : k ≤ j
    · simp [subresultant, hj, hkj]
    · have hk : j + 1 ≤ k := by omega
      simp [subresultant, hj, hkj, hk]
  · simp [subresultant, hj]

/-- There is no subresultant polynomial at or beyond the terminal index. -/
@[simp]
theorem _root_.Polynomial.subresultant_eq_zero_of_min_le [CommRing R]
    (p q : R[X]) (m n j : ℕ) (hj : min m n ≤ j) :
    subresultant p q m n j = 0 := by
  simp [subresultant, Nat.not_lt.mpr hj]

/-- When both formal bounds are positive, the subresultant polynomial at index zero is the
constant resultant. -/
@[simp]
theorem _root_.Polynomial.subresultant_zero [CommRing R]
    (p q : R[X]) (m n : ℕ) (h : 0 < min m n) :
    subresultant p q m n 0 = C (Polynomial.resultant p q m n) := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp [h]
  · rw [coeff_C_of_ne_zero hk]
    simp [h, hk]

/-- The subresultant polynomial at index `j` has degree at most `j`. -/
theorem _root_.Polynomial.degree_subresultant_le [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    (subresultant p q m n j).degree ≤ j := by
  classical
  by_cases hj : j < min m n
  · simp only [subresultant, hj, ↓reduceIte]
    by_cases hzero : ofFn (R := R) (j + 1)
        (fun k => subresultantCoeff p q m n j k) = 0
    · simp [hzero]
    · have hdeg := ofFn_degree_lt (R := R)
          (fun k : Fin (j + 1) => subresultantCoeff p q m n j k)
      rw [degree_eq_natDegree hzero] at hdeg ⊢
      exact WithBot.coe_le_coe.2 (Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.1 hdeg))
  · simp [subresultant, hj]

/-- The subresultant polynomial has degree exactly `j` precisely when its principal coefficient
does not vanish. -/
theorem _root_.Polynomial.degree_subresultant_eq_iff [CommRing R]
    (p q : R[X]) (m n j : ℕ) (hj : j < min m n) :
    (subresultant p q m n j).degree = j ↔ psc p q m n j ≠ 0 := by
  constructor
  · intro h
    simpa [hj] using coeff_ne_zero_of_eq_degree h
  · intro h
    apply degree_eq_of_le_of_coeff_ne_zero (degree_subresultant_le ..)
    simpa [hj]

/-- Fixed-bound subresultant polynomials commute with coefficient maps.  No degree-preservation
hypothesis is required. -/
@[simp]
theorem _root_.Polynomial.subresultant_map_map [CommRing R] [CommRing S]
    (f : R →+* S) (p q : R[X]) (m n j : ℕ) :
    subresultant (p.map f) (q.map f) m n j =
      (subresultant p q m n j).map f := by
  ext k
  by_cases hj : j < min m n <;> by_cases hkj : k ≤ j <;> simp [hj, hkj]

/-- Scaling the left input by `r` scales its subresultant polynomial at index `j` by
`r ^ (n - j)`. -/
theorem _root_.Polynomial.subresultant_C_mul_left [CommRing R]
    (p q : R[X]) (r : R) (m n j : ℕ) :
    subresultant (C r * p) q m n j = C (r ^ (n - j)) * subresultant p q m n j := by
  ext k
  rw [coeff_C_mul]
  by_cases hj : j < min m n <;> by_cases hkj : k ≤ j <;>
    simp [hj, hkj, subresultantCoeff_C_mul_left]

/-- Scaling the right input by `r` scales its subresultant polynomial at index `j` by
`r ^ (m - j)`. -/
theorem _root_.Polynomial.subresultant_C_mul_right [CommRing R]
    (p q : R[X]) (r : R) (m n j : ℕ) :
    subresultant p (C r * q) m n j = C (r ^ (m - j)) * subresultant p q m n j := by
  ext k
  rw [coeff_C_mul]
  by_cases hj : j < min m n <;> by_cases hkj : k ≤ j <;>
    simp [hj, hkj, subresultantCoeff_C_mul_right]

/-- Swapping the inputs and their bounds changes the subresultant polynomial by the Sylvester
block-swap sign. -/
theorem _root_.Polynomial.subresultant_comm [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    subresultant p q m n j =
      C ((-1) ^ ((m - j) * (n - j))) * subresultant q p n m j := by
  ext k
  rw [coeff_C_mul]
  by_cases hj : j < min m n
  · have hj' : j < min n m := by simpa [min_comm] using hj
    by_cases hkj : k ≤ j
    · rw [subresultant_coeff, subresultant_coeff]
      simp only [hj, hj', hkj, and_self, ↓reduceIte]
      rw [subresultantCoeff_comm]
    · rw [subresultant_coeff, subresultant_coeff]
      simp [hkj]
  · have hj' : ¬j < min n m := by simpa [min_comm] using hj
    rw [subresultant_coeff, subresultant_coeff]
    simp [hj, hj']

end TauCeti
