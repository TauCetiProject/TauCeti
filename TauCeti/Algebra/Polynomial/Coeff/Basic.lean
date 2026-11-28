/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.Ring
import TauCeti.Data.Nat.Factorial.Basic

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

For `p > 0`, multiplying `(B * X ^ (p * m)).coeff j` or `(B * (X ^ p + C p * A) ^ h).coeff j` by
`j!` produces a multiple of `p ^ m` or `p ^ h` (`Polynomial.pow_dvd_factorial_mul_coeff_mul_X_pow`
and `Polynomial.pow_dvd_factorial_mul_coeff_mul_X_pow_add_C_mul`).
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

/-- If `0 < p`, then `(p : R) ^ m` divides `(j.factorial : R) * (B * X ^ (p * m)).coeff j`
over any semiring `R`. -/
theorem pow_dvd_factorial_mul_coeff_mul_X_pow {R : Type*} [Semiring R]
    {p : ℕ} (hp : 0 < p) (m j : ℕ) (B : R[X]) :
    (p : R) ^ m ∣ (j.factorial : R) * (B * X ^ (p * m)).coeff j := by
  rcases lt_or_ge j (p * m) with hlt | hge
  · simp only [coeff_mul_X_pow', not_le.mpr hlt, ↓reduceIte, mul_zero, dvd_zero]
  · obtain ⟨q_fac, hq_fac⟩ := Nat.pow_dvd_factorial_of_mul_le hp hge
    have hcast : (j.factorial : R) = (p : R) ^ m * (q_fac : R) := by
      rw [hq_fac, Nat.cast_mul, Nat.cast_pow]
    rw [hcast, mul_assoc]
    exact dvd_mul_right _ _

/-- If `0 < p`, then `(p : R) ^ h` divides
`(j.factorial : R) * (B * (X ^ p + C (p : R) * A) ^ h).coeff j` over any commutative semiring
`R`. -/
theorem pow_dvd_factorial_mul_coeff_mul_X_pow_add_C_mul {R : Type*} [CommSemiring R]
    {p : ℕ} (hp : 0 < p) (h j : ℕ) (B A : R[X]) :
    (p : R) ^ h ∣ (j.factorial : R) * (B * (X ^ p + C (p : R) * A) ^ h).coeff j := by
  rw [(Commute.all (X ^ p : R[X]) (C (p : R) * A)).add_pow h, Finset.mul_sum,
    finsetSum_coeff, Finset.mul_sum]
  refine Finset.dvd_sum fun m hm ↦ ?_
  have hm_le : m ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  set B' : R[X] := B * A ^ (h - m) * (h.choose m : R[X])
  have hterm : B * ((X ^ p) ^ m * (C (p : R) * A) ^ (h - m) * (h.choose m : R[X])) =
      C ((p : R) ^ (h - m)) * (B' * X ^ (p * m)) := by
    rw [mul_pow, ← C_pow, ← pow_mul]
    dsimp only [B']
    ring
  rw [hterm, coeff_C_mul, mul_left_comm]
  conv_lhs => rw [← Nat.sub_add_cancel hm_le, pow_add]
  exact mul_dvd_mul_left _ (pow_dvd_factorial_mul_coeff_mul_X_pow hp m j B')

end Polynomial
