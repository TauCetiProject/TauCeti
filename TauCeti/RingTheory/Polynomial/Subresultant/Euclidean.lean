/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.Polynomial
public import TauCeti.RingTheory.Polynomial.Subresultant.DegreeDrop
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Euclidean reduction of subresultants

Adding a polynomial multiple of the right input to the left input preserves all
fixed-bound subresultant minors, provided the multiplier fits the difference of the
bounds. In particular, division with remainder preserves the minors before the bounds
are lowered. The principal-coefficient recurrence then records the power of the leading
coefficient and the sign introduced by lowering bounds and swapping inputs.

These identities connect determinant subresultants to Euclidean remainder sequences.
They do not recompute formal bounds silently, and include the terminal principal index.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
second edition, Chapter 4 (subresultants and polynomial remainder sequences).
-/

public section

namespace TauCeti

open Polynomial Matrix

variable {R : Type*} [CommRing R]

/-- The column operation adding shifted multiples of the right input to the left block. -/
private noncomputable def reductionShear (a : R[X]) (u v : ℕ) :
    Matrix (Fin (u + v)) (Fin (u + v)) R :=
  (Matrix.fromBlocks (1 : Matrix (Fin u) (Fin u) R)
    (Matrix.of fun i l => (X ^ l.val * a).coeff i.val) 0
    (1 : Matrix (Fin v) (Fin v) R)).reindex finSumFinEquiv finSumFinEquiv

private theorem det_reductionShear (a : R[X]) (u v : ℕ) :
    (reductionShear a u v).det = 1 := by
  classical
  simp [reductionShear]

private theorem subresultantCoeffMatrix_add_mul {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (hj : j ≤ n) (k : ℕ) :
    subresultantCoeffMatrix (p + a * q) q m n j k =
      subresultantCoeffMatrix p q m n j k * reductionShear a (m - j) (n - j) := by
  classical
  have hp' : (p + a * q).natDegree ≤ m :=
    natDegree_add_le_of_degree_le hp (natDegree_mul_le.trans (by omega))
  ext i l
  rw [subresultantCoeffMatrix_apply_eq_coeff hp' hq]
  have hmul := subresultantCoeffMatrix_mulVec hp hq j k
    (fun i => reductionShear a (m - j) (n - j) i l) i
  -- Matrix multiplication reads each column through the coefficient-map API.
  rw [Matrix.mul_apply]
  induction l using Fin.addCases with
  | left l =>
      simp [Fin.sum_univ_add, reductionShear, Matrix.one_apply,
        subresultantCoeffMatrix_apply_eq_coeff hp hq]
  | right l =>
      have hdeg : (X ^ l.val * a).natDegree < m - j := by
        have hbound : (X ^ l.val * a).natDegree ≤ l.val + a.natDegree :=
          natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_pow_le l.val) _)
        omega
      have hpoly : ofFn (m - j) (fun i => (X ^ l.val * a).coeff i.val) =
          X ^ l.val * a := by
        simpa [toFn, LinearMap.pi] using ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg
      have hright : ofFn (n - j) (fun i => if i = l then (1 : R) else 0) =
          X ^ l.val := by
        simp [ofFn_eq_sum_monomial, apply_ite (monomial _), monomial_one_right_eq_X_pow]
      simpa [Matrix.mulVec, dotProduct, reductionShear, Matrix.one_apply, hpoly, hright,
        mul_add, mul_assoc, add_comm] using hmul.symm

/-- Adding a multiple of the right input preserves every fixed-bound coefficient minor.
The multiplier's degree plus the right bound must not exceed the left bound. -/
theorem _root_.Polynomial.subresultantCoeff_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (hj : j ≤ n) (k : ℕ) :
    subresultantCoeff (p + a * q) q m n j k = subresultantCoeff p q m n j k := by
  simp [subresultantCoeff_def, subresultantCoeffMatrix_add_mul hp hq ha hj,
    Matrix.det_mul, det_reductionShear]

/-- Polynomial reduction preserves principal coefficients, including the terminal index. -/
theorem _root_.Polynomial.psc_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (hj : j ≤ n) :
    psc (p + a * q) q m n j = psc p q m n j := by
  simpa only [subresultantCoeff_index] using
    subresultantCoeff_add_mul_left hp hq ha hj j

/-- Polynomial reduction preserves the fixed-bound subresultant polynomial. -/
theorem _root_.Polynomial.subresultant_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (hj : j ≤ n) :
    subresultant (p + a * q) q m n j = subresultant p q m n j := by
  ext k
  simp only [subresultant_coeff, subresultantCoeff_add_mul_left hp hq ha hj]

section Field

variable {K : Type*} [Field K]

/-- Division with remainder preserves coefficient minors at the original left bound and
actual right degree. The left bound may be oversized, and the remainder may be zero. -/
theorem _root_.Polynomial.subresultantCoeff_mod_left {p q : K[X]} {m j : ℕ}
    (hq : q ≠ 0) (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m)
    (hj : j ≤ q.natDegree) (k : ℕ) :
    subresultantCoeff (p % q) q m q.natDegree j k =
      subresultantCoeff p q m q.natDegree j k := by
  have hquot : (p / q).natDegree ≤ p.natDegree - q.natDegree := by
    rw [div_def]
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_divByMonic p (monic_mul_leadingCoeff_inv hq),
      natDegree_mul_leadingCoeff_inv q hq]
  have ha : (-(p / q)).natDegree + q.natDegree ≤ m := by
    rw [natDegree_neg]
    omega
  have heq : p + -(p / q) * q = p % q := by
    rw [EuclideanDomain.mod_eq_sub_mul_div]
    ring
  simpa only [heq] using subresultantCoeff_add_mul_left hp le_rfl ha hj k

/-- Division with remainder preserves principal coefficients before the left bound drops. -/
theorem _root_.Polynomial.psc_mod_left {p q : K[X]} {m j : ℕ}
    (hq : q ≠ 0) (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m)
    (hj : j ≤ q.natDegree) :
    psc (p % q) q m q.natDegree j = psc p q m q.natDegree j := by
  simpa only [subresultantCoeff_index] using subresultantCoeff_mod_left hq hp hqm hj j

/-- Division with remainder preserves the subresultant polynomial at fixed bounds. -/
theorem _root_.Polynomial.subresultant_mod_left {p q : K[X]} {m j : ℕ}
    (hq : q ≠ 0) (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m)
    (hj : j ≤ q.natDegree) :
    subresultant (p % q) q m q.natDegree j = subresultant p q m q.natDegree j := by
  ext k
  simp only [subresultant_coeff, subresultantCoeff_mod_left hq hp hqm hj]

/-- A Euclidean step for principal subresultant coefficients. Lowering the remainder's
bound to `r` contributes a leading-coefficient power; swapping the column blocks contributes
the displayed sign. The smaller terminal index and zero remainders are included. -/
theorem _root_.Polynomial.psc_eq_sign_mul_pow_mul_psc_mod {p q : K[X]} {m r j : ℕ}
    (hq : q ≠ 0) (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m)
    (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    psc p q m q.natDegree j =
      (-1) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
        psc q (p % q) q.natDegree r j := by
  rw [← psc_mod_left hq hp hqm hjq,
    psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hr le_rfl hrm hjr hjq,
    psc_comm (p % q) q r q.natDegree j, coeff_natDegree]
  have hgap : m - j = (m - r) + (r - j) := by omega
  rw [hgap, add_mul, pow_add]
  ring

/-- The principal-coefficient recurrence for the signed remainder `-(p % q)`.
Negating the remainder adds the sign of its `q.natDegree - j` columns. -/
theorem _root_.Polynomial.psc_eq_sign_mul_pow_mul_psc_neg_mod {p q : K[X]} {m r j : ℕ}
    (hq : q ≠ 0) (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m)
    (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    psc p q m q.natDegree j =
      (-1) ^ ((m - j + 1) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
        psc q (-(p % q)) q.natDegree r j := by
  have hneg := psc_C_mul_right q (p % q) (-1) q.natDegree r j
  simp only [map_neg, map_one, neg_mul, one_mul] at hneg
  rw [hneg, psc_eq_sign_mul_pow_mul_psc_mod hq hp hqm hr hrm hjr hjq,
    add_mul, one_mul, pow_add]
  ring_nf
  simp [mul_comm (q.natDegree - j) 2, pow_mul]

end Field

end TauCeti
