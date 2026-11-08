/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# The prime powers that decide whether a divisor fits beside a fixed factor

Let `f` and `d` both divide `h`. Whether the product `f * d` still divides `h` is decided one
prime at a time, and only at the primes of `f`: room for `f * d` fails at `p` exactly when `d`
carries `p` to a power that exceeds the room `h` leaves after `f`, which is `v_p h - v_p f`. So
`f * d ∣ h` holds exactly when no prime `p` of `f` divides `d` to the exponent
`v_p h - v_p f + 1`.

The one-sided reading is what makes the statement useful: the primes outside `f` impose no
condition, because `d ∣ h` already leaves them enough room.

The exponents `v_p h - v_p f + 1` are themselves exponents of prime powers dividing `h`, both
one prime at a time and all at once, since the primes of `f` are distinct.

## Main results

* `Nat.mul_dvd_iff_forall_not_pow_dvd`: `f * d ∣ h` as non-divisibility of `d` by a
  prime power at each prime of `f`.
* `Nat.pow_factorization_sub_factorization_add_one_dvd`: the tested prime power divides `h`
  whenever `p` does.
* `Nat.prod_pow_factorization_sub_factorization_add_one_dvd`: so does their product over the
  primes of `f`, once every prime of `f` divides `h`.
-/

public section

namespace Nat

open Finset

/-- **A divisor fits beside a fixed factor exactly away from prime powers.** For `f` and `d`
dividing a nonzero `h`, the product `f * d` divides `h` if and only if no prime `p` of `f`
divides `d` to the exponent `v_p h - v_p f + 1`.

Only the primes of `f` are tested: at a prime `p` not dividing `f` the hypothesis `d ∣ h`
already gives `v_p d ≤ v_p h`. -/
theorem mul_dvd_iff_forall_not_pow_dvd {f d h : ℕ} (hh : h ≠ 0) (hf : f ∣ h) (hd : d ∣ h) :
    f * d ∣ h ↔
      ∀ p ∈ f.primeFactors, ¬p ^ (h.factorization p - f.factorization p + 1) ∣ d := by
  have hf0 := ne_zero_of_dvd_ne_zero hh hf
  have hd0 := ne_zero_of_dvd_ne_zero hh hd
  rw [← factorization_le_iff_dvd (mul_ne_zero hf0 hd0) hh, factorization_mul hf0 hd0,
    Finsupp.le_def]
  refine forall_congr' fun p => ?_
  have hfh := (factorization_le_iff_dvd hf0 hh).2 hf p
  by_cases hp : p ∈ f.primeFactors
  · rw [(prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hd0]
    simp only [Finsupp.coe_add, Pi.add_apply, hp, forall_const]
    omega
  · have : f.factorization p = 0 := by rwa [← Finsupp.notMem_support_iff, support_factorization]
    simpa [hp, this] using (factorization_le_iff_dvd hd0 hh).2 hd p

/-- **The prime power tested by `mul_dvd_iff_forall_not_pow_dvd` divides `h`.** Let `p` be a
prime of `f` that divides `h`. Every power of `p` divides `h = 0`. For `h ≠ 0`, the exponent
`v_p h - v_p f + 1` does not exceed `v_p h`: `f` contributes at least one power of `p`, and `h`
has at least one. -/
theorem pow_factorization_sub_factorization_add_one_dvd {f h p : ℕ}
    (hp : p ∈ f.primeFactors) (hph : p ∣ h) :
    p ^ (h.factorization p - f.factorization p + 1) ∣ h := by
  rcases eq_or_ne h 0 with rfl | hh
  · exact dvd_zero _
  have hprime := prime_of_mem_primeFactors hp
  have : f.factorization p ≠ 0 := by rwa [← Finsupp.mem_support_iff, support_factorization]
  have := hprime.factorization_pos_of_dvd hh hph
  rw [hprime.pow_dvd_iff_le_factorization hh]
  omega

/-- **The product of the prime powers tested by `mul_dvd_iff_forall_not_pow_dvd` divides `h`.**
Suppose every prime of `f` divides `h` (for instance when `f ∣ h`). Everything divides `h = 0`.
For `h ≠ 0`, the prime powers `p ^ (v_p h - v_p f + 1)` occur at distinct primes and each divides
`h`, so their product still divides `h`: it is the product of prime powers read off a finitely
supported exponent function bounded by the factorization of `h`. -/
theorem prod_pow_factorization_sub_factorization_add_one_dvd {f h : ℕ}
    (hf : ∀ p ∈ f.primeFactors, p ∣ h) :
    (∏ p ∈ f.primeFactors, p ^ (h.factorization p - f.factorization p + 1)) ∣ h := by
  classical
  rcases eq_or_ne h 0 with rfl | hh
  · exact dvd_zero _
  rw [← Finsupp.prod_indicator_index (fun p => h.factorization p - f.factorization p + 1)
    (h := (· ^ ·)) fun _ _ => pow_zero _]
  refine prod_pow_dvd_of_le_factorization fun p => ?_
  rw [Finsupp.indicator_apply]
  split_ifs with hp
  · exact ((prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hh).mp
      (pow_factorization_sub_factorization_add_one_dvd hp (hf p hp))
  · exact zero_le _

end Nat
