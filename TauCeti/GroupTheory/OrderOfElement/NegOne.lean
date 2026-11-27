/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement

/-!
# Powers equal to `-1` and the order of an element

If `-1 ≠ 1` in a monoid with distributive negation, no power of an element of odd order is `-1`,
as recorded by `TauCeti.pow_ne_neg_one_of_odd_orderOf`.

Let `u` be an element of order `2 * m`, with `m ≠ 0`, in a ring without zero divisors. Then
`u ^ m` squares to `1` and is not `1`, so it is `-1`, the only other square root of `1`. Since
the powers of `u` repeat with period `2 * m`, the exponents `k` with `u ^ k = -1` are exactly the
odd multiples of `m`: those with `m ∣ k` and `¬ 2 * m ∣ k`.

The hypothesis that there are no zero divisors is needed: in `ZMod 8` the residue `3` has order
`2` but is not `-1`. In characteristic two no element has even order, since `-1 = 1`.

Applied to residues modulo a prime, this decides which `q ^ k + 1` the prime divides from the
multiplicative order of `q`.

## Main results

* `TauCeti.pow_eq_neg_one_of_orderOf_eq_two_mul`: if `orderOf u = 2 * m` and `m ≠ 0`, then
  `u ^ m = -1`.
* `TauCeti.pow_eq_neg_one_iff_of_orderOf_eq_two_mul`: if `orderOf u = 2 * m` and `m ≠ 0`, then
  `u ^ k = -1` if and only if `m ∣ k` and `¬ 2 * m ∣ k`.
-/

public section

namespace TauCeti

/-- If `-1 ≠ 1`, no power of an element of odd order is `-1`. -/
theorem pow_ne_neg_one_of_odd_orderOf {M : Type*} [Monoid M] [HasDistribNeg M] {a : M}
    (h : (-1 : M) ≠ 1) (ha : Odd (orderOf a)) (i : ℕ) : a ^ i ≠ -1 := by
  intro he
  have hp : (a ^ i) ^ orderOf a = 1 := by
    rw [pow_right_comm, pow_orderOf_eq_one, one_pow]
  rw [he, ha.neg_one_pow] at hp
  exact h hp

variable {R : Type*} [Ring R] [NoZeroDivisors R] {u : R} {m : ℕ}

/-- In a ring without zero divisors, an element of order `2 * m` with `m ≠ 0` has `m`-th power
`-1`. -/
theorem pow_eq_neg_one_of_orderOf_eq_two_mul (hu : orderOf u = 2 * m) (hm : m ≠ 0) :
    u ^ m = -1 := by
  have hsq : u ^ m * u ^ m = 1 := by rw [← pow_add, ← two_mul, ← hu, pow_orderOf_eq_one]
  exact (mul_self_eq_one_iff.1 hsq).resolve_left (pow_ne_one_of_lt_orderOf hm (by omega))

/-- In a ring without zero divisors, if `u` has order `2 * m` with `m ≠ 0`, then `u ^ k = -1`
exactly for the odd multiples `k` of `m`. -/
theorem pow_eq_neg_one_iff_of_orderOf_eq_two_mul (hu : orderOf u = 2 * m) (hm : m ≠ 0) (k : ℕ) :
    u ^ k = -1 ↔ m ∣ k ∧ ¬ 2 * m ∣ k := by
  have hm' := pow_eq_neg_one_of_orderOf_eq_two_mul hu hm
  -- `-1 ≠ 1`, because `u ^ m = -1` while `m` is less than the order of `u`.
  have hne : (-1 : R) ≠ 1 := hm' ▸ pow_ne_one_of_lt_orderOf hm (by omega)
  constructor
  · intro hk
    refine ⟨?_, fun h => hne (hk ▸ orderOf_dvd_iff_pow_eq_one.1 (hu ▸ h))⟩
    have h2k : u ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hk, neg_one_sq]
    rw [← Nat.mul_dvd_mul_iff_left two_pos, ← hu]
    exact orderOf_dvd_of_pow_eq_one h2k
  · rintro ⟨⟨t, rfl⟩, h⟩
    have ht : Odd t := Nat.not_even_iff_odd.1 fun ht =>
      h (mul_comm m 2 ▸ Nat.mul_dvd_mul_left m (even_iff_two_dvd.1 ht))
    rw [pow_mul, hm', ht.neg_one_pow]

end TauCeti
