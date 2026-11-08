/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Powers of natural numbers

A natural number `n ≠ 1` either is not a power of `b`, or is a power `b ^ k` with a positive
exponent `k`, because `b ^ 0 = 1`.

For positive bases `b < a` and `n ≥ 3`, we also bound differences of powers below by
`(a + b) * a ^ (n - 2)`.

## Main results

* `Nat.forall_ne_pow_or_exists_pos_eq_pow`: the dichotomy above. Its consumer is the case split
  on the coefficients of the universal normalised logarithm in
  `TauCeti/RingTheory/FormalGroup/ExponentTwo/Universal.lean`, whose free coefficients sit in the
  degrees `n ≥ 2` that are not powers of two.
* `Nat.add_mul_pow_sub_two_lt_pow_sub_pow`: the strict lower bound above.
-/

public section

namespace Nat

/-- A natural number `n ≠ 1` either is not a power of `b`, or is `b ^ k` for some `k > 0`. -/
theorem forall_ne_pow_or_exists_pos_eq_pow {b n : ℕ} (hn : n ≠ 1) :
    (∀ k : ℕ, n ≠ b ^ k) ∨ ∃ k, 0 < k ∧ n = b ^ k := by
  refine or_iff_not_imp_left.2 fun h ↦ ?_
  obtain ⟨k, hk⟩ := not_forall_not.mp h
  exact ⟨k, Nat.pos_of_ne_zero fun h0 ↦ hn (by rw [hk, h0, Nat.pow_zero]), hk⟩

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
    rw [Nat.pow_two_sub_pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hmul := Nat.mul_le_mul_right (a ^ (n - 2)) hsq
  have hstrict := Nat.mul_lt_mul_of_pos_right hpow (Nat.pow_pos hb : 0 < b ^ 2)
  have hfactor : (a ^ 2 - b ^ 2) * a ^ (n - 2) + a ^ (n - 2) * b ^ 2 = a ^ n := by
    rw [mul_comm (a ^ (n - 2)) (b ^ 2), ← Nat.add_mul,
      Nat.sub_add_cancel (Nat.pow_le_pow_left hba.le 2), ha, mul_comm]
  omega

end Nat
