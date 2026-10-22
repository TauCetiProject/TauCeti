/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect

/-!
# Roots of elements of perfect rings

Let `R` be a perfect ring of exponential characteristic `p`. Every `x ∈ R` has a unique
`p ^ n`-th root `(iterateFrobeniusEquiv R p n).symm x` for each `n`. This file records how these
roots relate to each other, and the fact that `p`-th powers can be cancelled from annihilation
relations because Frobenius is injective.

## Main results

* `TauCeti.iterateFrobeniusEquiv_symm_add_pow`: the `p ^ n`-th power of the `p ^ (m + n)`-th root
  of `x` is its `p ^ m`-th root.
* `TauCeti.iterateFrobeniusEquiv_symm_succ_pow`: the `p`-th power of the `p ^ (n + 1)`-th root
  of `x` is its `p ^ n`-th root.
* `TauCeti.iterateFrobeniusEquiv_symm_dvd_of_le`: deeper roots of `x` divide shallower ones.
* `TauCeti.mul_eq_zero_of_mul_pow_p_eq_zero`: `a * b ^ p = 0` implies `a * b = 0`.
-/

public section

namespace TauCeti

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p] [PerfectRing R p]

/-- The `p ^ n`-th power of the `p ^ (m + n)`-th root of `x` is its `p ^ m`-th root. -/
theorem iterateFrobeniusEquiv_symm_add_pow (x : R) (m n : ℕ) :
    (iterateFrobeniusEquiv R p (m + n)).symm x ^ p ^ n = (iterateFrobeniusEquiv R p m).symm x := by
  rw [add_comm, iterateFrobeniusEquiv_symm_add_apply, ← iterateFrobeniusEquiv_def,
    RingEquiv.apply_symm_apply]

/-- The `p`-th power of the `p ^ (n + 1)`-th root of `x` is its `p ^ n`-th root. -/
theorem iterateFrobeniusEquiv_symm_succ_pow (x : R) (n : ℕ) :
    (iterateFrobeniusEquiv R p (n + 1)).symm x ^ p = (iterateFrobeniusEquiv R p n).symm x := by
  simpa using iterateFrobeniusEquiv_symm_add_pow x n 1

/-- Deeper roots of `x` divide shallower ones: the `p ^ n`-th root of `x` divides its
`p ^ m`-th root when `m ≤ n`. -/
theorem iterateFrobeniusEquiv_symm_dvd_of_le (x : R) {m n : ℕ} (h : m ≤ n) :
    (iterateFrobeniusEquiv R p n).symm x ∣ (iterateFrobeniusEquiv R p m).symm x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← iterateFrobeniusEquiv_symm_add_pow x m k]
  exact dvd_pow_self _ (pow_ne_zero _ (expChar_ne_zero R p))

/-- In a perfect ring of exponential characteristic `p`, if `a` kills `b ^ p` then `a` kills `b`:
the `p`-th power of `a * b` is a multiple of `a * b ^ p`, and Frobenius is injective. -/
theorem mul_eq_zero_of_mul_pow_p_eq_zero {a b : R} (h : a * b ^ p = 0) : a * b = 0 := by
  apply injective_frobenius R p
  rw [frobenius_def, map_zero, mul_pow, ← pow_sub_one_mul (expChar_ne_zero R p) a, mul_assoc, h,
    mul_zero]

end TauCeti
