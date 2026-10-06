/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.Polynomial
public import TauCeti.RingTheory.Polynomial.Subresultant.DegreeDrop.Basic
public import TauCeti.RingTheory.Polynomial.Subresultant.Signed
import TauCeti.Algebra.Polynomial.OfFn
import TauCeti.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Euclidean reduction of subresultants

Adding a polynomial multiple of the right input to the left input preserves all
fixed-bound subresultant minors, provided the multiplier fits the difference of the
bounds. In particular, division with remainder preserves the minors before the bounds
are lowered. The principal-coefficient recurrence then records the power of the leading
coefficient and the sign introduced by lowering bounds and swapping inputs.

Reduction invariance holds over any commutative ring and at every index, including the
terminal principal index. Division with remainder requires a field; the divisor and
remainder may be zero. The principal-coefficient recurrences require the index to lie
at or below both the remainder bound and the divisor degree. Strictly between the
degree of the remainder and the degree of the divisor, the principal coefficients vanish.
For the signed principal coefficients, one step of the signed remainder sequence
`p, q, -(p % q)` multiplies the coefficients at or below the remainder bound by a common
factor independent of the index.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
second edition, Chapter 4 (subresultants and polynomial remainder sequences).
-/

public section

namespace TauCeti

open Polynomial Matrix

variable {R : Type*} [CommRing R]

/-- Add shifted multiples of the `q`-columns (first block) to the `p`-columns (second block),
realising `X ^ l * p ↦ X ^ l * (p + a * q)`. -/
private noncomputable def reductionShear (a : R[X]) (u v : ℕ) :
    Matrix (Fin (u + v)) (Fin (u + v)) R :=
  (Matrix.fromBlocks (1 : Matrix (Fin u) (Fin u) R)
    (Matrix.of fun i l => (X ^ l.val * a).coeff i.val) 0
    (1 : Matrix (Fin v) (Fin v) R)).reindex finSumFinEquiv finSumFinEquiv

private theorem reductionShear_apply_castAdd (a : R[X]) (u v : ℕ)
    (i : Fin (u + v)) (l : Fin u) :
    reductionShear a u v i (Fin.castAdd v l) =
      i.addCases (fun i => if i = l then 1 else 0) (fun _ => 0) := by
  classical
  induction i using Fin.addCases <;> simp [reductionShear, Matrix.one_apply]

private theorem reductionShear_apply_natAdd (a : R[X]) (u v : ℕ)
    (i : Fin (u + v)) (l : Fin v) :
    reductionShear a u v i (Fin.natAdd u l) =
      i.addCases (fun i => (X ^ l.val * a).coeff i.val)
        (fun i => if i = l then 1 else 0) := by
  classical
  induction i using Fin.addCases <;> simp [reductionShear, Matrix.one_apply]

private theorem det_reductionShear (a : R[X]) (u v : ℕ) :
    (reductionShear a u v).det = 1 := by
  classical
  simp [reductionShear]

private theorem subresultantCoeffMatrix_add_mul {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (k : ℕ) :
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
  rw [Matrix.mul_apply']
  -- Identify the column dot product with mulVec to apply hmul without expanding the sum.
  change _ = (subresultantCoeffMatrix p q m n j k).mulVec
    (fun i => reductionShear a (m - j) (n - j) i l) i
  rw [hmul]
  induction l using Fin.addCases with
  | left l =>
      simp [reductionShear_apply_castAdd, ← Pi.zero_def]
  | right l =>
      have hdeg : (X ^ l.val * a).natDegree < m - j := by
        have hbound : (X ^ l.val * a).natDegree ≤ l.val + a.natDegree :=
          natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_pow_le l.val) _)
        omega
      have hpoly : ofFn (m - j) (fun i => (X ^ l.val * a).coeff i.val) =
          X ^ l.val * a := by
        have hvec : (fun i : Fin (m - j) => (X ^ l.val * a).coeff i.val) =
            toFn (m - j) (X ^ l.val * a) := by
          ext i
          rw [toFn_apply]
        rw [hvec]
        exact ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg
      simp only [Fin.addCases_right, reductionShear_apply_natAdd,
        Fin.addCases_left, ofFn_single, hpoly]
      rw [mul_add, mul_assoc, add_comm]

/-- Adding a multiple of the right input preserves every fixed-bound coefficient minor.
The multiplier's degree plus the right bound must not exceed the left bound. -/
theorem _root_.Polynomial.subresultantCoeff_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) (k : ℕ) :
    subresultantCoeff (p + a * q) q m n j k = subresultantCoeff p q m n j k := by
  simp [subresultantCoeff_def, subresultantCoeffMatrix_add_mul hp hq ha,
    Matrix.det_mul, det_reductionShear]

/-- Polynomial reduction preserves principal coefficients, including the terminal index. -/
theorem _root_.Polynomial.psc_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) :
    psc (p + a * q) q m n j = psc p q m n j := by
  simpa only [subresultantCoeff_index] using
    subresultantCoeff_add_mul_left (j := j) hp hq ha j

/-- Polynomial reduction preserves the fixed-bound subresultant polynomial. -/
theorem _root_.Polynomial.subresultant_add_mul_left {p q a : R[X]} {m n j : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (ha : a.natDegree + n ≤ m) :
    subresultant (p + a * q) q m n j = subresultant p q m n j := by
  ext k
  simp only [subresultant_coeff, subresultantCoeff_add_mul_left hp hq ha]

section Field

variable {K : Type*} [Field K]

/-- Division with remainder preserves coefficient minors at the original left bound and
actual right degree. The left bound may be oversized, and the divisor and remainder may be zero. -/
theorem _root_.Polynomial.subresultantCoeff_mod_left {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m)
    (k : ℕ) :
    subresultantCoeff (p % q) q m q.natDegree j k =
      subresultantCoeff p q m q.natDegree j k := by
  by_cases hq : q = 0
  · subst q
    simp only [EuclideanDomain.mod_zero]
  by_cases hqm : q.natDegree ≤ m
  · have hquot : (p / q).natDegree ≤ p.natDegree - q.natDegree := by
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
    simpa only [heq] using subresultantCoeff_add_mul_left hp le_rfl ha k
  · have hmod : p % q = p :=
      (mod_eq_self_iff hq).mpr (degree_lt_degree (by omega))
    rw [hmod]

/-- Division with remainder preserves principal coefficients before the left bound drops. -/
theorem _root_.Polynomial.psc_mod_left {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) :
    psc (p % q) q m q.natDegree j = psc p q m q.natDegree j := by
  simpa only [subresultantCoeff_index] using subresultantCoeff_mod_left (j := j) hp j

/-- Division with remainder preserves the subresultant polynomial at fixed bounds. -/
theorem _root_.Polynomial.subresultant_mod_left {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) :
    subresultant (p % q) q m q.natDegree j = subresultant p q m q.natDegree j := by
  ext k
  simp only [subresultant_coeff, subresultantCoeff_mod_left hp]

/-- A Euclidean step for principal subresultant coefficients. Lowering the remainder's
bound from `m` to `r` contributes `q.leadingCoeff ^ (m - r)`; the displayed sign
comes from both the bound drop and the input swap. The smaller terminal index, zero
divisors, and zero remainders are included. -/
theorem _root_.Polynomial.psc_eq_sign_mul_leadingCoeff_pow_mul_psc_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m)
    (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    psc p q m q.natDegree j =
      (-1) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
        psc q (p % q) q.natDegree r j := by
  rw [← psc_mod_left hp,
    psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hr le_rfl hrm hjr hjq,
    psc_comm (p % q) q r q.natDegree j, coeff_natDegree]
  have hgap : m - j = (m - r) + (r - j) := by omega
  rw [hgap, add_mul, pow_add]
  ring

/-- The principal-coefficient recurrence for the signed remainder `-(p % q)`.
Negating the remainder adds the sign of its `q.natDegree - j` columns. -/
theorem _root_.Polynomial.psc_eq_sign_mul_leadingCoeff_pow_mul_psc_neg_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m)
    (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    psc p q m q.natDegree j =
      (-1) ^ ((m - j + 1) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
        psc q (-(p % q)) q.natDegree r j := by
  have hneg := psc_C_mul_right q (p % q) (-1) q.natDegree r j
  simp only [map_neg, map_one, neg_mul, one_mul] at hneg
  rw [hneg, psc_eq_sign_mul_leadingCoeff_pow_mul_psc_mod hp hr hrm hjr hjq,
    add_mul, one_mul, pow_add]
  have hsq : ((-1 : K) ^ (q.natDegree - j)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  linear_combination
    -((-1 : K) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r) *
      psc q (p % q) q.natDegree r j) * hsq

/-- Principal coefficients vanish at the indices strictly between the degree of the
remainder `p % q` and the degree of `q`. The remainder may be zero. -/
theorem _root_.Polynomial.psc_eq_zero_of_natDegree_mod_lt {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hrj : (p % q).natDegree < j) (hjq : j < q.natDegree)
    (hjm : j ≤ m) :
    psc p q m q.natDegree j = 0 := by
  rw [← psc_mod_left hp,
    psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hrj.le le_rfl hjm le_rfl hjq.le,
    psc_left_bound, coeff_eq_zero_of_natDegree_lt hrj, zero_pow (by omega), mul_zero]

/-- One step of the signed remainder sequence multiplies the signed principal coefficients by a
common factor. For indices at most a bound `r` for the remainder, the signed coefficients of
`(p, q)` are those of `(q, -(p % q))` times `(-1) ^ (m - q.natDegree).choose 2 *
q.leadingCoeff ^ (m - r)`, which does not depend on the index. -/
theorem _root_.Polynomial.signedPsc_eq_mul_signedPsc_neg_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m) (hr : (p % q).natDegree ≤ r)
    (hrm : r ≤ m) (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    signedPsc p q m q.natDegree j =
      (-1) ^ (m - q.natDegree).choose 2 * q.leadingCoeff ^ (m - r) *
        signedPsc q (-(p % q)) q.natDegree r j := by
  rw [signedPsc_of_le p q (le_min (hjq.trans hqm) hjq), signedPsc_of_le _ _ (le_min hjq hjr),
    psc_eq_sign_mul_leadingCoeff_pow_mul_psc_neg_mod hp hr hrm hjr hjq]
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self (q.natDegree - j)
  have hmj : m - j = (m - q.natDegree) + (q.natDegree - j) := by omega
  have hexp : (m - j).choose 2 + (m - j + 1) * (q.natDegree - j) =
      (m - q.natDegree).choose 2 + (q.natDegree - j).choose 2 +
        2 * ((m - q.natDegree) * (q.natDegree - j) + t) := by
    rw [hmj, Nat.add_choose_two]
    nlinarith [ht]
  have hsign : (-1 : K) ^ (m - j).choose 2 * (-1) ^ ((m - j + 1) * (q.natDegree - j)) =
      (-1) ^ (m - q.natDegree).choose 2 * (-1) ^ (q.natDegree - j).choose 2 := by
    rw [← pow_add, hexp, pow_add, pow_add, pow_mul]
    simp
  linear_combination (q.leadingCoeff ^ (m - r) * psc q (-(p % q)) q.natDegree r j) * hsign

/-- The signed principal coefficients vanish at the indices strictly between the degree of the
remainder `p % q` and the degree of `q`. -/
theorem _root_.Polynomial.signedPsc_eq_zero_of_natDegree_mod_lt {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hrj : (p % q).natDegree < j) (hjq : j < q.natDegree)
    (hjm : j ≤ m) :
    signedPsc p q m q.natDegree j = 0 := by
  rw [signedPsc_of_le p q (le_min hjm hjq.le), psc_eq_zero_of_natDegree_mod_lt hp hrj hjq hjm,
    mul_zero]

end Field

end TauCeti
