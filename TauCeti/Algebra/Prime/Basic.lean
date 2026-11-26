/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Prime.Defs

/-!
# Powers of a prime and elements it does not divide

If a prime `p` does not divide `u`, then multiplying `a` by any power of `u` does not change
whether `p` divides it. For example, replacing an integer radicand `a` by `a * u ^ 2` with
`p ∤ u` keeps it in the same square class without changing whether `p` divides it.

In a cancellative commutative monoid with zero, every power of a prime `p` is relatively prime to
an element `p` does not divide, since the divisors of `p ^ n` are the associates of the powers of
`p`. Unlike `IsRelPrime.pow_left`, this needs no `DecompositionMonoid` instance, so it applies to
multivariate polynomial rings without choosing a GCD structure.

## Main results

* `Prime.dvd_mul_pow_iff`: for a prime `p` with `p ∤ u`, `p ∣ a * u ^ n ↔ p ∣ a`.
* `Prime.isRelPrime_pow_of_not_dvd`: for a prime `p` with `p ∤ q`, `p ^ n` and `q` are relatively
  prime.
-/

public section

variable {M : Type*} [CommMonoidWithZero M] {p a u : M}

/-- If a prime `p` does not divide `u`, then `p` divides `a * u ^ n` exactly when it
divides `a`. -/
@[simp]
theorem Prime.dvd_mul_pow_iff (hp : Prime p) (hu : ¬ p ∣ u) {n : ℕ} :
    p ∣ a * u ^ n ↔ p ∣ a := by
  rw [hp.dvd_mul, or_iff_left (mt hp.dvd_of_dvd_pow hu)]

/-- If a prime `p` does not divide `q`, then every power of `p` is relatively prime to `q`. -/
theorem Prime.isRelPrime_pow_of_not_dvd [IsCancelMulZero M] {q : M} (hp : Prime p)
    (h : ¬ p ∣ q) (n : ℕ) : IsRelPrime (p ^ n) q := by
  intro d hd hdq
  -- `d` is associated to some `p ^ i`, and `i > 0` would make `p` divide `q`.
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp n).1 hd
  rcases i with _ | i
  · exact associated_one_iff_isUnit.1 (by simpa using hi)
  · exact absurd ((dvd_pow_self p i.succ_ne_zero).trans (hi.symm.dvd.trans hdq)) h
