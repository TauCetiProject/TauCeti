/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factors

/-!
# Powers of natural numbers

A natural number `n ≠ 1` either is not a power of `b`, or is a power `b ^ k` with a positive
exponent `k`, because `b ^ 0 = 1`. Moreover, any natural number `n` that is not a power of `b` has
a prime divisor distinct from `b`; for a prime `p`, this makes the powers of `p` exactly the
natural numbers with no prime divisor other than `p`.

For positive bases `b < a` and `n ≥ 3`, we also bound differences of powers below by
`(a + b) * a ^ (n - 2)`.

## Main results

* `Nat.forall_ne_pow_or_exists_pos_eq_pow`: the dichotomy above. Its consumer is the case split
  on the coefficients of the universal normalised logarithm in
  `TauCeti/RingTheory/FormalGroup/ExponentTwo/Universal.lean`, whose free coefficients sit in the
  degrees `n ≥ 2` that are not powers of two.
* `Nat.exists_prime_dvd_ne_of_forall_ne_pow`: every `n` not of the form `b ^ k` has a prime divisor
  `q ≠ b`.
* `Nat.Prime.forall_prime_ne_not_dvd_iff_exists_pow_eq`: for a prime `p`, a natural number has no
  prime divisor distinct from `p` if and only if it is a power of `p`.
* `Nat.add_mul_pow_sub_two_lt_pow_sub_pow`: the strict lower bound above.
-/

public section

namespace Nat

/-- A natural number `n ≠ 1` either is not a power of `b`, or is `b ^ k` for some `k > 0`. -/
theorem forall_ne_pow_or_exists_pos_eq_pow {b n : ℕ} (hn : n ≠ 1) :
    (∀ k : ℕ, n ≠ b ^ k) ∨ ∃ k, 0 < k ∧ n = b ^ k := by
  refine or_iff_not_imp_left.2 fun h ↦ ?_
  obtain ⟨k, hk⟩ := not_forall_not.mp h
  exact ⟨k, Nat.pos_of_ne_zero fun h0 ↦ hn (by rw [hk, h0, pow_zero]), hk⟩

/-- Any natural number `n` that is not a power of `b` has a prime divisor distinct from `b`. -/
theorem exists_prime_dvd_ne_of_forall_ne_pow {b n : ℕ} (hpow : ∀ k, n ≠ b ^ k) :
    ∃ q, q.Prime ∧ q ∣ n ∧ q ≠ b := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne b 2 with rfl | hb
    · exact ⟨3, Nat.prime_three, dvd_zero 3, by decide⟩
    · exact ⟨2, Nat.prime_two, dvd_zero 2, hb.symm⟩
  · by_contra! h
    exact hpow n.primeFactorsList.length
      (Nat.eq_prime_pow_of_unique_prime_dvd hn fun {q} hq hdvd ↦ h q hq hdvd)

/-- A natural number has no prime divisor distinct from a prime `p` if and only if it is a power of
`p`. -/
theorem Prime.forall_prime_ne_not_dvd_iff_exists_pow_eq {p k : ℕ} (hp : p.Prime) :
    (∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k) ↔ ∃ n : ℕ, p ^ n = k := by
  refine ⟨fun hno ↦ ?_, fun ⟨n, hn⟩ q hq hqp hqd ↦
    hqp (Nat.prime_eq_prime_of_dvd_pow hq hp (hn ▸ hqd))⟩
  by_contra! hpow
  obtain ⟨q, hq, hqk, hqp⟩ := exists_prime_dvd_ne_of_forall_ne_pow fun n h ↦ hpow n h.symm
  exact hno q hq hqp hqk

/-- For positive bases `b < a` and `n ≥ 3`, `a ^ n - b ^ n` strictly exceeds
`(a + b) * a ^ (n - 2) = a ^ (n - 1) + b * a ^ (n - 2)`. -/
theorem add_mul_pow_sub_two_lt_pow_sub_pow {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hn : 3 ≤ n) : (a + b) * a ^ (n - 2) < a ^ n - b ^ n := by
  have hpow : b ^ (n - 2) < a ^ (n - 2) :=
    Nat.pow_lt_pow_left hba (by omega)
  have ha : a ^ n = a ^ (n - 2) * a ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ n)]
  have hb' : b ^ n = b ^ (n - 2) * b ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ n)]
  have hsq : a + b ≤ a ^ 2 - b ^ 2 := by
    rw [pow_two_sub_pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hmul := mul_le_mul_right (a ^ (n - 2)) hsq
  have hstrict := Nat.mul_lt_mul_of_pos_right hpow (Nat.pow_pos hb : 0 < b ^ 2)
  have hfactor : (a ^ 2 - b ^ 2) * a ^ (n - 2) + a ^ (n - 2) * b ^ 2 = a ^ n := by
    rw [mul_comm (a ^ (n - 2)) (b ^ 2), ← add_mul,
      Nat.sub_add_cancel (Nat.pow_le_pow_left hba.le 2), ha, mul_comm]
  omega

end Nat
