/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Coefficients of polynomials with a degree bound

Multiplication by `X ^ l` shifts a polynomial's coefficients by `l`. When its degree is
bounded by `n`, the shifted coefficients vanish outside the window from `l` to `l + n`.
This identity identifies bounded coefficient rows with coefficients of shifted polynomials.
Such a polynomial is determined by its coefficients indexed by `Fin (n + 1)`:
`Polynomial.eq_of_natDegree_le_of_coeff_fin_eq`.

If `p` has smaller degree than `q`, then the largest degree at which the coefficients of `p` and
`q` differ is the degree of `q`, where `p` has coefficient `0`.
`Polynomial.exists_coeff_iff_of_degree_lt` records this in the form in which it decides a
lexicographic comparison of coefficient sequences, starting from the top degree.

Over an ordered semiring, products of polynomials with nonnegative coefficients retain
nonnegative coefficients (`Polynomial.coeff_mul_nonneg`), and multiplying by `1 + C a * X ^ k`
(`0 ≤ a`) does not decrease any coefficient (`Polynomial.coeff_le_coeff_mul_one_add_C_mul_X_pow`).
-/

public section

namespace Polynomial

/-- The coefficients of `X ^ l * p` vanish outside the window from `l` to `l + n`
when `p.natDegree ≤ n`. -/
theorem coeff_X_pow_mul_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (l d : ℕ) :
    (X ^ l * p).coeff d = if l ≤ d ∧ d ≤ l + n then p.coeff (d - l) else 0 := by
  grind [coeff_X_pow_mul', coeff_eq_zero_of_natDegree_lt]

/-- Two polynomials of degree at most `n` are equal once their coefficients agree at every
index `i : Fin (n + 1)`. -/
theorem eq_of_natDegree_le_of_coeff_fin_eq {R : Type*} [Semiring R] {p q : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (h : ∀ i : Fin (n + 1), p.coeff i = q.coeff i) :
    p = q :=
  (ext_iff_natDegree_le hp hq).2 fun k hk => h ⟨k, Nat.lt_succ_of_le hk⟩

/-- If `p` has smaller degree than `q`, then the largest degree at which `p` and `q` differ is the
degree of `q`, where `p` has coefficient `0`. So for an irreflexive relation `r`, there is a
degree `i` above which `p` and `q` agree and with `r (p.coeff i) (q.coeff i)` exactly when
`r 0 q.leadingCoeff`. -/
theorem exists_coeff_iff_of_degree_lt {R : Type*} [Semiring R] {r : R → R → Prop}
    (hr : ∀ a, ¬ r a a) {p q : R[X]} (h : p.degree < q.degree) :
    (∃ i, (∀ j, i < j → p.coeff j = q.coeff j) ∧ r (p.coeff i) (q.coeff i)) ↔
      r 0 q.leadingCoeff := by
  have hp := coeff_natDegree_eq_zero_of_degree_lt h
  have hpq (j : ℕ) (hj : q.natDegree < j) : p.coeff j = q.coeff j := by
    rw [coeff_eq_zero_of_natDegree_lt hj, coeff_eq_zero_of_degree_lt
      (h.trans_le (degree_le_natDegree.trans (by exact_mod_cast hj.le)))]
  refine ⟨fun ⟨i, hi, hpqi⟩ ↦ ?_, fun hq ↦ ⟨_, hpq, by rwa [hp, coeff_natDegree]⟩⟩
  rcases lt_trichotomy i q.natDegree with hlt | rfl | hgt
  · -- Otherwise `p` and `q` agree at the degree of `q`, where `p` vanishes and `q` does not.
    exact absurd (by rw [← coeff_natDegree, ← hi _ hlt, hp])
      (leadingCoeff_ne_zero.2 (ne_zero_of_degree_gt h))
  · rwa [hp, coeff_natDegree] at hpqi
  · rw [hpq i hgt] at hpqi
    exact absurd hpqi (hr _)

/-- The product of two polynomials with nonnegative coefficients has nonnegative coefficients. -/
theorem coeff_mul_nonneg {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {p q : R[X]} (hp : ∀ d, 0 ≤ p.coeff d) (hq : ∀ d, 0 ≤ q.coeff d) (d : ℕ) :
    0 ≤ (p * q).coeff d := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hp _) (hq _)

/-- Multiplying a polynomial with nonnegative coefficients by `1 + C a * X ^ k` (`0 ≤ a`) does not
decrease any coefficient. -/
theorem coeff_le_coeff_mul_one_add_C_mul_X_pow {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {p : R[X]} (hp : ∀ d, 0 ≤ p.coeff d) {a : R} (ha : 0 ≤ a) (k d : ℕ) :
    p.coeff d ≤ (p * (1 + C a * X ^ k)).coeff d := by
  rw [mul_add, mul_one, coeff_add]
  refine le_add_of_nonneg_right ?_
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with hd
  · rw [coeff_mul_C]
    exact mul_nonneg (hp (d - k)) ha
  · exact le_rfl

end Polynomial
