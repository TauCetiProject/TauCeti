/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Basic

import Mathlib.Algebra.Ring.GeomSum

/-!
# Powers of congruent elements

If `a ≡ b` modulo `p` in a commutative ring, then raising to an exponent `m` divisible by `p ^ k`
improves the congruence to `a ^ m ≡ b ^ m` modulo `p ^ (k + 1)`. Mathlib's
`dvd_sub_pow_of_dvd_sub` is the case `m = p ^ k`; the general case follows since `a ^ c - b ^ c`
is again divisible by `p` for every `c`. This is the congruence behind Dwork's lemma on ghost
components of Witt vectors.
-/

public section

namespace TauCeti

/-- If `p` divides `a - b` and `p ^ k` divides `m`, then `p ^ (k + 1)` divides `a ^ m - b ^ m`. -/
theorem dvd_sub_pow_of_dvd_sub_of_pow_dvd {R : Type*} [CommRing R] {p k m : ℕ} {a b : R}
    (h : (p : R) ∣ a - b) (hm : p ^ k ∣ m) : (p : R) ^ (k + 1) ∣ a ^ m - b ^ m := by
  obtain ⟨c, rfl⟩ := hm
  rw [mul_comm, pow_mul, pow_mul]
  exact dvd_sub_pow_of_dvd_sub (h.trans (sub_dvd_pow_sub_pow a b c)) k

end TauCeti
