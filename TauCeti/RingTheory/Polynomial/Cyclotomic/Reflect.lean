/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.Algebra.Polynomial.Reverse

/-!
# Cyclotomic polynomials are palindromic

For `n ≠ 1` the coefficient sequence of the cyclotomic polynomial `Φ_n` reads the same in both
directions: over any commutative ring, reflecting `cyclotomic n R` at its degree `φ(n)` returns
`cyclotomic n R`, so its coefficients of index `k` and `φ(n) - k` agree for `k ≤ φ(n)`. The
exception is `Φ_1 = X - 1`, whose reflection `1 - X` is `-Φ_1`.

Palindromicity is what makes the two-variable cyclotomic values `Φ_n(a, b)` symmetric in `a`
and `b` for `n ≠ 1`.

## Main results

* `Polynomial.reflect_cyclotomic`: `(cyclotomic n R).reflect n.totient = cyclotomic n R` for
  `n ≠ 1`.
* `Polynomial.coeff_cyclotomic_totient_sub`: for `n ≠ 1` and `k ≤ φ(n)`, the coefficients of
  `cyclotomic n R` of index `φ(n) - k` and `k` agree.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/- The proof is by strong induction through the factorization `X ^ n - 1 = ∏_{d ∣ n} Φ_d`: the
reflection of `X ^ n - 1` at `n` is `-(X ^ n - 1)`, the proper divisors of `n ≥ 2` contribute the
single sign of `Φ_1`, and the remaining factor is cancelled because it is monic. The statement
below, covering `n = 1` as well, is the one carried through that induction. -/

/-- Reflecting `Φ_n` at `φ(n)` negates it when `n = 1` and fixes it otherwise. -/
private theorem reflect_cyclotomic_eq_C_mul (n : ℕ) :
    (cyclotomic n R).reflect n.totient = C (if n = 1 then -1 else 1) * cyclotomic n R := by
  induction n using Nat.strong_induction_on with | _ n ih
  rcases Nat.lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := by omega
    simp [reflect_one]
  · simp [reflect_sub, reflect_one]
  -- For `n ≥ 2`, write `X ^ n - 1 = Φ_n * Q` with `Q` the product over the proper divisors.
  set Q := ∏ d ∈ n.properDivisors, cyclotomic d R with hQ
  have hX : (X ^ n - 1 : R[X]) = cyclotomic n R * Q := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (by omega), ← Nat.cons_self_properDivisors (by omega),
      Finset.prod_cons]
  have hdeg : n.totient + ∑ d ∈ n.properDivisors, d.totient = n := by
    rw [← Finset.sum_cons Nat.self_notMem_properDivisors, Nat.cons_self_properDivisors (by omega),
      Nat.sum_totient]
  -- By induction, reflecting `Q` only picks up the sign of its factor `Φ_1`.
  have hreflQ : Q.reflect (∑ d ∈ n.properDivisors, d.totient) = -Q := by
    rw [hQ, reflect_prod _ _ _ fun d _ => natDegree_cyclotomic_le,
      Finset.prod_congr rfl fun d hd => ih d (Nat.mem_properDivisors.1 hd).2,
      Finset.prod_mul_distrib, ← map_prod, Finset.prod_ite_eq']
    simp [Nat.one_mem_properDivisors_iff_one_lt.2 hn]
  have hQdeg : Q.natDegree ≤ ∑ d ∈ n.properDivisors, d.totient :=
    (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun d _ => natDegree_cyclotomic_le)
  have hreflX : (X ^ n - 1 : R[X]).reflect n = -(X ^ n - 1) := by
    rw [reflect_sub, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, reflect_one]
    ring
  have key : (cyclotomic n R).reflect n.totient * -Q = -(cyclotomic n R * Q) := by
    rw [← hreflQ, ← reflect_mul _ _ natDegree_cyclotomic_le hQdeg, hdeg, ← hX, hreflX]
  have hmonic : Q.Monic := monic_prod_of_monic _ _ fun d _ => cyclotomic.monic d R
  have hzero : ((cyclotomic n R).reflect n.totient - cyclotomic n R) * Q = 0 := by
    linear_combination -key
  simp [sub_eq_zero.mp (hmonic.mul_left_eq_zero_iff.mp hzero), hn.ne']

/-- **Cyclotomic polynomials are palindromic.** For `n ≠ 1`, reflecting `Φ_n` at its degree
`φ(n)` returns `Φ_n`. -/
@[simp]
theorem reflect_cyclotomic {n : ℕ} (hn : n ≠ 1) :
    (cyclotomic n R).reflect n.totient = cyclotomic n R := by
  simp [reflect_cyclotomic_eq_C_mul, hn]

/-- For `n ≠ 1` and `k ≤ φ(n)`, the coefficients of `Φ_n` of index `φ(n) - k` and `k` agree. -/
@[simp]
theorem coeff_cyclotomic_totient_sub {n k : ℕ} (hn : n ≠ 1) (hk : k ≤ n.totient) :
    (cyclotomic n R).coeff (n.totient - k) = (cyclotomic n R).coeff k := by
  conv_rhs => rw [← reflect_cyclotomic hn]
  rw [coeff_reflect, revAt_le hk]

end Polynomial
