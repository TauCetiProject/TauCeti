/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Basic
public import Mathlib.RingTheory.Multiplicity

import Mathlib.Algebra.Ring.GeomSum

/-!
# Powers of congruent elements

If `a ≡ b` modulo `p` in a commutative ring, then raising to an exponent `m` divisible by `p ^ k`
improves the congruence to `a ^ m ≡ b ^ m` modulo `p ^ (k + 1)`. Mathlib's
`dvd_sub_pow_of_dvd_sub` is the case `m = p ^ k`; the general case follows since `a ^ c - b ^ c`
is again divisible by `p` for every `c`. This is the congruence behind Dwork's lemma on ghost
components of Witt vectors.

The file also records which divisors of `n` carry the full `p`-part of `n`: a divisor `d` of `n`
that does not divide `n / p` is divisible by `p ^ v_p(n)`
(`TauCeti.pow_multiplicity_dvd_of_not_dvd_div`).
-/

public section

namespace TauCeti

/-- If `p` divides `a - b` and `p ^ k` divides `m`, then `p ^ (k + 1)` divides `a ^ m - b ^ m`. -/
theorem dvd_sub_pow_of_dvd_sub_of_pow_dvd {R : Type*} [CommRing R] {p k m : ℕ} {a b : R}
    (h : (p : R) ∣ a - b) (hm : p ^ k ∣ m) : (p : R) ^ (k + 1) ∣ a ^ m - b ^ m := by
  obtain ⟨c, rfl⟩ := hm
  rw [mul_comm, pow_mul, pow_mul]
  exact dvd_sub_pow_of_dvd_sub (h.trans (sub_dvd_pow_sub_pow a b c)) k

/-- For a prime `p`, a divisor `d` of `n` that does not divide `n / p` is divisible by
`p ^ v_p(n)`. -/
theorem pow_multiplicity_dvd_of_not_dvd_div {p n d : ℕ} (hp : p.Prime) (hd : d ∣ n)
    (hdp : ¬d ∣ n / p) : p ^ multiplicity p n ∣ d := by
  obtain ⟨c, rfl⟩ := hd
  have hc : ¬p ∣ c := by
    rintro ⟨c', rfl⟩
    exact hdp ⟨c', by rw [mul_left_comm, Nat.mul_div_cancel_left _ hp.pos]⟩
  exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hc)).dvd_of_dvd_mul_right
    (pow_multiplicity_dvd p (d * c))

end TauCeti
