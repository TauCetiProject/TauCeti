/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Natural numbers that are powers

A natural number `n ≠ 1` either is not a power of `b`, or is a power `b ^ k` with a positive
exponent `k`, because `b ^ 0 = 1`.

## Main results

* `Nat.forall_ne_pow_or_exists_pos_eq_pow`: the dichotomy above. Its consumer is the case split
  on the coefficients of the universal normalised logarithm in
  `TauCeti/RingTheory/FormalGroup/ExponentTwo/Universal.lean`, whose free coefficients sit in the
  degrees `n ≥ 2` that are not powers of two.
-/

public section

namespace Nat

/-- A natural number `n ≠ 1` either is not a power of `b`, or is `b ^ k` for some `k > 0`. -/
theorem forall_ne_pow_or_exists_pos_eq_pow {b n : ℕ} (hn : n ≠ 1) :
    (∀ k : ℕ, n ≠ b ^ k) ∨ ∃ k, 0 < k ∧ n = b ^ k := by
  refine or_iff_not_imp_left.2 fun h ↦ ?_
  obtain ⟨k, hk⟩ := not_forall_not.mp h
  exact ⟨k, Nat.pos_of_ne_zero fun h0 ↦ hn (by rw [hk, h0, Nat.pow_zero]), hk⟩

end Nat
