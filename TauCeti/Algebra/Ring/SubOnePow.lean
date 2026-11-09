/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas

/-!
# The prime `p` divides `(x - 1) ^ p ^ k` when `x ^ p ^ k = 1`

For commuting elements `x` and `y` of a ring and a prime `p`, the binomial theorem gives
`x ^ p ^ k = ((x - y) + y) ^ p ^ k = (x - y) ^ p ^ k + y ^ p ^ k + p * c` for some `c`, because
every binomial coefficient `(p ^ k).choose m` with `0 < m < p ^ k` is divisible by `p`. Hence
`(p : A) ∣ (x - y) ^ p ^ k` if and only if `(p : A) ∣ x ^ p ^ k - y ^ p ^ k`. Taking `y = 1`, an
element `x` with `x ^ p ^ k = 1` satisfies `(p : A) ∣ (x - 1) ^ p ^ k`; no commutativity of the
ring is needed.

This is the integral shadow of the freshman's dream `(x - y) ^ p ^ k = x ^ p ^ k - y ^ p ^ k` in
characteristic `p`. It is what makes the group-like elements `g - 1`, for `g` of `p`-power order
in a group algebra over the `p`-adic integers, topologically nilpotent.

## Main results

* `Nat.Prime.dvd_sub_pow_iff_dvd_pow_sub_pow`: for commuting `x` and `y`,
  `(p : A) ∣ (x - y) ^ p ^ k ↔ (p : A) ∣ x ^ p ^ k - y ^ p ^ k`.
* `Nat.Prime.dvd_sub_one_pow_of_pow_eq_one`: `(p : A) ∣ (x - 1) ^ p ^ k` when `x ^ p ^ k = 1`.
-/

public section

variable {A : Type*} [Ring A] {p : ℕ}

/-- For commuting elements `x` and `y` of a ring and a prime `p`, `p` divides `(x - y) ^ p ^ k`
if and only if it divides `x ^ p ^ k - y ^ p ^ k`. -/
theorem Nat.Prime.dvd_sub_pow_iff_dvd_pow_sub_pow (hp : p.Prime) {x y : A} (h : Commute x y)
    (k : ℕ) : (p : A) ∣ (x - y) ^ p ^ k ↔ (p : A) ∣ x ^ p ^ k - y ^ p ^ k := by
  obtain ⟨r, hr⟩ := (h.sub_left (Commute.refl y)).exists_add_pow_prime_pow_eq hp k
  rw [sub_add_cancel] at hr
  rw [hr, add_right_comm, add_sub_cancel_right, mul_assoc, mul_assoc,
    dvd_add_left (dvd_mul_right _ _)]

/-- If `x ^ p ^ k = 1` in a ring, for a prime `p`, then `p` divides `(x - 1) ^ p ^ k`. -/
theorem Nat.Prime.dvd_sub_one_pow_of_pow_eq_one (hp : p.Prime) {x : A} {k : ℕ}
    (hx : x ^ p ^ k = 1) : (p : A) ∣ (x - 1) ^ p ^ k :=
  (hp.dvd_sub_pow_iff_dvd_pow_sub_pow (Commute.one_right x) k).2 (by simp [hx])
