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

If `p` has smaller degree than `q`, then the largest degree at which the coefficients of `p` and
`q` differ is the degree of `q`, where `p` has coefficient `0`.
`Polynomial.exists_coeff_iff_of_degree_lt` records this in the form in which it decides a
lexicographic comparison of coefficient sequences, starting from the top degree.
-/

public section

namespace Polynomial

/-- The coefficients of `X ^ l * p` vanish outside the window from `l` to `l + n`
when `p.natDegree ≤ n`. -/
theorem coeff_X_pow_mul_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (l d : ℕ) :
    (X ^ l * p).coeff d = if l ≤ d ∧ d ≤ l + n then p.coeff (d - l) else 0 := by
  grind [coeff_X_pow_mul', coeff_eq_zero_of_natDegree_lt]

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

end Polynomial
