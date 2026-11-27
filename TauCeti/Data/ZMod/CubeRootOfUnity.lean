/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
import TauCeti.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-!
# Cube roots of unity modulo a prime

For a prime `p`, the polynomial `T ^ 2 + T + 1` has a root in `ZMod p` exactly when
`p ≢ 2 (mod 3)`. For `p = 3` the root is `1`. For `p ≠ 3` a root is the same thing as an element of
multiplicative order `3`, which exists exactly when `3` divides the order `p - 1` of the cyclic
group of units.

This decides which primes split in the Eisenstein integers `ℤ[ω]`, `ω ^ 2 + ω + 1 = 0`.

## Main results

* `ZMod.exists_sq_add_add_one_eq_zero_iff`: `T ^ 2 + T + 1` has a root modulo the prime `p` if and
  only if `p % 3 ≠ 2`.
-/

public section

namespace ZMod

/-- For a prime `p`, the polynomial `T ^ 2 + T + 1` has a root in `ZMod p` if and only if `p` is
not congruent to `2` modulo `3`. -/
theorem exists_sq_add_add_one_eq_zero_iff {p : ℕ} [hp : Fact p.Prime] :
    (∃ t : ZMod p, t ^ 2 + t + 1 = 0) ↔ p % 3 ≠ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · rintro ⟨t, ht⟩ hp3
    have ht3 : t ^ 3 = 1 := TauCeti.pow_three_eq_one_of_sq_add_add_one_eq_zero ht
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1] at ht
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination ht
      have hp3' := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1
        ((ZMod.natCast_eq_zero_iff 3 p).1 h3)
      omega
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_pow three_ne_zero] at ht3
      exact zero_ne_one ht3
    have hdvd := ZMod.orderOf_dvd_card_sub_one ht0
    rw [orderOf_eq_prime ht3 ht1] at hdvd
    have := hp.out.two_le
    omega
  · intro hp3
    rcases Nat.lt_or_ge (p % 3) 1 with h0 | h1
    · have hp3eq : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).1
        (Nat.dvd_of_mod_eq_zero (by omega))
      have h3 : ((3 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 3 p).2 (by rw [← hp3eq])
      push_cast at h3
      exact ⟨1, by linear_combination h3⟩
    · have h3 : 3 ∣ Fintype.card (ZMod p)ˣ := by
        rw [ZMod.card_units]
        have := hp.out.two_le
        omega
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 h3
      have hu3 : (u : ZMod p) ^ 3 = 1 := by
        have h := congrArg Units.val (pow_orderOf_eq_one u)
        rwa [hu, Units.val_pow_eq_pow_val, Units.val_one] at h
      have hu1 : (u : ZMod p) ≠ 1 := by
        intro h1'
        have hu1' : u = 1 := Units.ext (by rw [h1', Units.val_one])
        rw [hu1', orderOf_one] at hu
        omega
      have hmul : ((u : ZMod p) - 1) * ((u : ZMod p) ^ 2 + u + 1) = 0 := by
        linear_combination hu3
      exact ⟨u, (mul_eq_zero.1 hmul).resolve_left (sub_ne_zero.2 hu1)⟩

end ZMod
