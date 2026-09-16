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

* `TauCeti.Nat.mul_dvd_iff_forall_not_pow_dvd`: `f * d ∣ h` as non-divisibility of `d` by a
  prime power at each prime of `f`.
* `TauCeti.Nat.pow_sub_factorization_add_one_dvd`: the tested prime power divides `h`.
* `TauCeti.Nat.prod_pow_sub_factorization_add_one_dvd`: so does their product over the primes
  of `f`.
-/

public section

namespace TauCeti.Nat

open Finset

/-- **A divisor fits beside a fixed factor exactly away from prime powers.** For `f` and `d`
dividing a nonzero `h`, the product `f * d` divides `h` if and only if no prime `p` of `f`
divides `d` to the exponent `v_p h - v_p f + 1`.

Only the primes of `f` are tested: at a prime `p` not dividing `f` the hypothesis `d ∣ h`
already gives `v_p d ≤ v_p h`. -/
theorem mul_dvd_iff_forall_not_pow_dvd {f d h : ℕ} (hh : h ≠ 0) (hf : f ∣ h) (hd : d ∣ h) :
    f * d ∣ h ↔
      ∀ p ∈ f.primeFactors, ¬p ^ (h.factorization p - f.factorization p + 1) ∣ d := by
  have hf0 : f ≠ 0 := fun h0 => hh (zero_dvd_iff.mp (h0 ▸ hf))
  have hd0 : d ≠ 0 := fun h0 => hh (zero_dvd_iff.mp (h0 ▸ hd))
  have hfh : ∀ p, f.factorization p ≤ h.factorization p :=
    fun p => (Nat.factorization_le_iff_dvd hf0 hh).mpr hf p
  have hdh : ∀ p, d.factorization p ≤ h.factorization p :=
    fun p => (Nat.factorization_le_iff_dvd hd0 hh).mpr hd p
  rw [← Nat.factorization_le_iff_dvd (Nat.mul_ne_zero hf0 hd0) hh, Finsupp.le_def,
    Nat.factorization_mul hf0 hd0]
  simp only [Finsupp.coe_add, Pi.add_apply]
  constructor
  · intro hle p hp hdvd
    have hb : 0 < f.factorization p :=
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hf0
        (Nat.dvd_of_mem_primeFactors hp))
    have := ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hd0).mp hdvd
    have := hle p
    have := hfh p
    omega
  · intro hp p
    by_cases hmem : p ∈ f.primeFactors
    · have hb : 0 < f.factorization p :=
        (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hmem) hf0
          (Nat.dvd_of_mem_primeFactors hmem))
      have hlt : ¬(h.factorization p - f.factorization p + 1 ≤ d.factorization p) :=
        fun hle => hp p hmem
          (((Nat.prime_of_mem_primeFactors hmem).pow_dvd_iff_le_factorization hd0).mpr hle)
      have := hfh p
      omega
    · have : f.factorization p = 0 := by
        rw [← Nat.support_factorization] at hmem
        exact Finsupp.notMem_support_iff.mp hmem
      have := hdh p
      omega

/-- **The prime power tested by `mul_dvd_iff_forall_not_pow_dvd` divides `h`.** For `f` dividing a
nonzero `h` and `p` a prime of `f`, the exponent `v_p h - v_p f + 1` does not exceed `v_p h`,
because `f` contributes at least one power of `p`. -/
theorem pow_sub_factorization_add_one_dvd {f h : ℕ} (hh : h ≠ 0) (hf : f ∣ h) {p : ℕ}
    (hp : p ∈ f.primeFactors) :
    p ^ (h.factorization p - f.factorization p + 1) ∣ h := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hf0 : f ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hpos : 0 < f.factorization p :=
    hprime.factorization_pos_of_dvd hf0 (Nat.dvd_of_mem_primeFactors hp)
  have hle : f.factorization p ≤ h.factorization p := (Nat.factorization_le_iff_dvd hf0 hh).mpr hf p
  refine (hprime.pow_dvd_iff_le_factorization hh).mpr ?_
  omega

/-- **The product of the prime powers tested by `mul_dvd_iff_forall_not_pow_dvd` divides `h`.**
The primes of `f` are distinct, so the prime powers `p ^ (v_p h - v_p f + 1)` occur at distinct
primes and their product still divides `h`. -/
theorem prod_pow_sub_factorization_add_one_dvd {f h : ℕ} (hh : h ≠ 0) (hf : f ∣ h) :
    (∏ p ∈ f.primeFactors, p ^ (h.factorization p - f.factorization p + 1)) ∣ h := by
  have hf0 : f ≠ 0 := fun h0 => hh (zero_dvd_iff.mp (h0 ▸ hf))
  have hne : ∀ p ∈ f.primeFactors, p ^ (h.factorization p - f.factorization p + 1) ≠ 0 :=
    fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Nat.factorization_le_iff_dvd (Finset.prod_ne_zero_iff.mpr hne) hh, Finsupp.le_def,
    Nat.factorization_prod hne]
  intro q
  have hterm : ∀ p ∈ f.primeFactors,
      ((p ^ (h.factorization p - f.factorization p + 1)).factorization) q
        = if p = q then h.factorization p - f.factorization p + 1 else 0 := by
    intro p hp
    rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow, Finsupp.single_apply]
  rw [Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' f.primeFactors q
      (fun p => h.factorization p - f.factorization p + 1)]
  split_ifs with hq
  · have hprime := Nat.prime_of_mem_primeFactors hq
    have hpos : 0 < f.factorization q :=
      hprime.factorization_pos_of_dvd hf0 (Nat.dvd_of_mem_primeFactors hq)
    have hle : f.factorization q ≤ h.factorization q :=
      (Nat.factorization_le_iff_dvd hf0 hh).mpr hf q
    omega
  · exact Nat.zero_le _

end TauCeti.Nat
