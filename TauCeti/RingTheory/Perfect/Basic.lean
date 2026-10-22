/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.GroupWithZero.Basic

/-!
# Roots of elements of perfect rings

Let `R` be a perfect ring of exponential characteristic `p`. Every `x ∈ R` has a unique
`p ^ n`-th root `(iterateFrobeniusEquiv R p n).symm x` for each `n`. This file records how these
roots relate to each other, the fact that `R` is reduced when `p` is prime, and the fact that
`p`-th powers can be cancelled from annihilation relations.

## Main results

* `TauCeti.iterateFrobeniusEquiv_symm_add_pow`: the `p ^ n`-th power of the `p ^ (m + n)`-th root
  of `x` is its `p ^ m`-th root.
* `TauCeti.iterateFrobeniusEquiv_symm_succ_pow`: the `p`-th power of the `p ^ (n + 1)`-th root
  of `x` is its `p ^ n`-th root.
* `TauCeti.iterateFrobeniusEquiv_symm_dvd_of_le`: deeper roots of `x` divide shallower ones.
* `TauCeti.isReduced_of_perfectRing`: a perfect ring of prime characteristic is reduced.
* `TauCeti.mul_eq_zero_of_mul_pow_expChar_eq_zero`: `a * b ^ p = 0` implies `a * b = 0`.
* `TauCeti.mul_iterateFrobeniusEquiv_symm_succ_eq_zero`: an element killing the `p ^ n`-th root
  of `x` also kills its `p ^ (n + 1)`-th root.
-/

public section

namespace TauCeti

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p] [PerfectRing R p]

/-- The `p ^ n`-th power of the `p ^ (m + n)`-th root of `x` is its `p ^ m`-th root. -/
@[simp]
theorem iterateFrobeniusEquiv_symm_add_pow (x : R) (m n : ℕ) :
    (iterateFrobeniusEquiv R p (m + n)).symm x ^ p ^ n = (iterateFrobeniusEquiv R p m).symm x := by
  rw [add_comm, iterateFrobeniusEquiv_symm_add_apply, ← iterateFrobeniusEquiv_def,
    RingEquiv.apply_symm_apply]

/-- The `p`-th power of the `p ^ (n + 1)`-th root of `x` is its `p ^ n`-th root. -/
@[simp]
theorem iterateFrobeniusEquiv_symm_succ_pow (x : R) (n : ℕ) :
    (iterateFrobeniusEquiv R p (n + 1)).symm x ^ p = (iterateFrobeniusEquiv R p n).symm x := by
  rw [← iterateFrobeniusEquiv_symm_add_pow x n 1, pow_one]

/-- Deeper roots of `x` divide shallower ones: the `p ^ n`-th root of `x` divides its
`p ^ m`-th root when `m ≤ n`. -/
theorem iterateFrobeniusEquiv_symm_dvd_of_le (x : R) {m n : ℕ} (h : m ≤ n) :
    (iterateFrobeniusEquiv R p n).symm x ∣ (iterateFrobeniusEquiv R p m).symm x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← iterateFrobeniusEquiv_symm_add_pow x m k]
  exact dvd_pow_self _ (pow_ne_zero _ (expChar_ne_zero R p))

variable (R p) in
/-- A perfect ring of prime characteristic `p` is reduced. -/
theorem isReduced_of_perfectRing [hp : Fact p.Prime] : IsReduced R :=
  -- If `x ^ n = 0`, then the `p ^ n`-th power of `x` vanishes, and Frobenius is injective.
  ⟨fun x ⟨n, hn⟩ ↦ (iterateFrobeniusEquiv R p n).injective <| by
    rw [map_zero, iterateFrobeniusEquiv_def,
      pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hn]⟩

/-- In a perfect ring of exponential characteristic `p`, if `a` kills `b ^ p` then `a` kills
`b`. -/
theorem mul_eq_zero_of_mul_pow_expChar_eq_zero {a b : R} (h : a * b ^ p = 0) : a * b = 0 := by
  -- In exponential characteristic `1` there is nothing to prove; otherwise `R` is reduced.
  obtain hp | rfl := expChar_is_prime_or_one R p
  · have := Fact.mk hp
    have := isReduced_of_perfectRing R p
    exact mul_eq_zero_of_mul_pow_eq_zero h
  · simpa using h

/-- If `c` kills the `p ^ n`-th root of `x`, then it kills the `p ^ (n + 1)`-th root of `x`. -/
theorem mul_iterateFrobeniusEquiv_symm_succ_eq_zero {x c : R} {n : ℕ}
    (h : c * (iterateFrobeniusEquiv R p n).symm x = 0) :
    c * (iterateFrobeniusEquiv R p (n + 1)).symm x = 0 := by
  -- The `p ^ n`-th root is the `p`-th power of the `p ^ (n + 1)`-th root.
  rw [← iterateFrobeniusEquiv_symm_succ_pow x n] at h
  exact mul_eq_zero_of_mul_pow_expChar_eq_zero h

/-- If `c` kills the `p ^ n`-th root of `x`, then it kills every positive power of the
`p ^ (n + 1)`-th root of `x`. -/
theorem mul_iterateFrobeniusEquiv_symm_succ_pow_eq_zero {x c : R} {n k : ℕ} (hk : k ≠ 0)
    (h : c * (iterateFrobeniusEquiv R p n).symm x = 0) :
    c * (iterateFrobeniusEquiv R p (n + 1)).symm x ^ k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ', ← mul_assoc, mul_iterateFrobeniusEquiv_symm_succ_eq_zero h, zero_mul]

end TauCeti
