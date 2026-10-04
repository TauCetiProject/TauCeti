/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.DegreeDrop.Basic

/-!
# Degree drops in subresultant polynomials

Below the smaller degree bounds, lowering a bound scales the entire subresultant polynomial,
not just its principal coefficient. At a smaller terminal bound, the surviving polynomial is
instead a scalar multiple of the corresponding input. Thus terminal scalar data must not be replaced
by the zero polynomial used outside the strict subresultant range.

The coefficient-minor formulas retain formal bounds and hold over arbitrary commutative rings.
The specialization formulas use reducta taken before mapping coefficients, allowing degree
drops and zero fibers. These identities supply the specialization laws for comparisons with
polynomial remainder sequences.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4 (specialization of subresultants).
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*}

variable [CommRing R]

/-- Below both smaller bounds, an arbitrary right-bound drop scales the whole subresultant
polynomial. The formula does not replace a terminal scalar minor by a polynomial. -/
theorem _root_.Polynomial.subresultant_eq_C_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hj : j < min m n) :
    subresultant p q m N j = C (p.coeff m ^ (N - n)) * subresultant p q m n j := by
  ext k
  have hj' : j < min m N := by omega
  by_cases hk : k ≤ j
  · simp only [subresultant_coeff, hj, hj', hk, and_self, ↓reduceIte, coeff_C_mul]
    exact subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hN
      (by omega) (by omega) k
  · simp only [coeff_C_mul, subresultant_coeff, hk, and_false, ↓reduceIte, mul_zero]

/-- Below both smaller bounds, a left-bound drop scales the whole subresultant polynomial,
including the column-block sign. -/
theorem _root_.Polynomial.subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hj : j < min m n) :
    subresultant p q M n j = C ((-1) ^ ((M - m) * (n - j)) * q.coeff n ^ (M - m)) *
      subresultant p q m n j := by
  ext k
  have hj' : j < min M n := by omega
  by_cases hk : k ≤ j
  · simp only [subresultant_coeff, hj, hj', hk, and_self, ↓reduceIte, coeff_C_mul]
    simpa only [mul_assoc] using
      subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM
        (by omega) (by omega) k
  · simp only [coeff_C_mul, subresultant_coeff, hk, and_false, ↓reduceIte, mul_zero]

/-- When only the right bound drops, the subresultant at its smaller terminal index survives
as a scalar multiple of the right polynomial, rather than a terminal subresultant polynomial. -/
@[simp]
theorem _root_.Polynomial.subresultant_right_bound_of_degree_drop {p q : R[X]} {m n N : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hnm : n < m) (hnN : n < N) :
    subresultant p q m N n =
      C (p.coeff m ^ (N - n) * q.coeff n ^ (m - n - 1)) * q := by
  ext k
  have hj : n < min m N := by omega
  rw [coeff_C_mul, subresultant_coeff]
  by_cases hk : k ≤ n
  · simp only [hj, hk, and_self, ↓reduceIte]
    rw [subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hnN.le hnm le_rfl,
      subresultantCoeff_right_bound p q hnm hk]
    ring
  · have hq : q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hk, hq]

/-- The smaller left terminal index likewise survives as a scalar multiple of the left input,
with the sign from swapping the formal column blocks. -/
@[simp]
theorem _root_.Polynomial.subresultant_left_bound_of_degree_drop {p q : R[X]} {m M n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hmn : m < n) (hmM : m < M) :
    subresultant p q M n m =
      C ((-1) ^ ((M - m) * (n - m)) * q.coeff n ^ (M - m) *
        p.coeff m ^ (n - m - 1)) * p := by
  rw [subresultant_comm, subresultant_right_bound_of_degree_drop hn hm hmn hmM,
    ← mul_assoc, ← C_mul]
  congr 2
  ring

/-- Dropping both formal bounds forces every subresultant polynomial to vanish, not merely
its principal coefficient. Outside the strict range the polynomial is zero by convention. -/
@[simp]
theorem _root_.Polynomial.subresultant_eq_zero_of_natDegree_lt_bounds {p q : R[X]}
    {m n j : ℕ} (hm : p.natDegree < m) (hn : q.natDegree < n) :
    subresultant p q m n j = 0 := by
  by_cases hj : j < min m n
  · have hnpos : 0 < n := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    ext k
    rw [subresultant_coeff]
    by_cases hk : k ≤ j
    · simp only [hj, hk, and_self, ↓reduceIte, coeff_zero]
      rw [subresultantCoeff_succ_right hm.le (by omega) (by omega) (by omega),
        coeff_eq_zero_of_natDegree_lt hm, zero_mul]
    · simp [hk]
  · exact subresultant_eq_zero_of_min_le p q m n j (by omega)

/-- After specialization, a right-bound drop below the smaller bounds scales the mapped
subresultant. The reduced input is obtained by truncating before mapping. -/
theorem _root_.Polynomial.map_subresultant_of_right_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m n N j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hj : j < min m n) :
    (subresultant p q m N j).map f = C (f (p.coeff m) ^ (N - n)) *
      subresultant (p.map f) ((q.reductum (n + 1)).map f) m n j := by
  have htrunc : (q.reductum (n + 1)).map f = q.map f := by
    rw [← reductum_map]
    exact reductum_eq_self (by omega)
  rw [htrunc, ← subresultant_map_map,
    subresultant_eq_C_coeff_pow_mul_of_right_degree_drop hm hn hN hj, coeff_map]

/-- The left-bound specialization formula retains the column-block sign and the right
coefficient power, with truncation before mapping. -/
theorem _root_.Polynomial.map_subresultant_of_left_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m M n j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hM : m ≤ M) (hj : j < min m n) :
    (subresultant p q M n j).map f =
      C ((-1) ^ ((M - m) * (n - j)) * f (q.coeff n) ^ (M - m)) *
        subresultant ((p.reductum (m + 1)).map f) (q.map f) m n j := by
  have htrunc : (p.reductum (m + 1)).map f = p.map f := by
    rw [← reductum_map]
    exact reductum_eq_self (by omega)
  rw [htrunc, ← subresultant_map_map,
    subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hj, coeff_map]

end TauCeti
