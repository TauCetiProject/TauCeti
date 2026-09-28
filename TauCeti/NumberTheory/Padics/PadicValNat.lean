/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

/-!
# Sublinear growth of the `p`-adic valuation of natural numbers

Since `p ^ padicValNat p n ∣ n`, the valuation `padicValNat p n` is at most logarithmic in `n`.
This file records the consequence that any fixed multiple of it, shifted by any constant, is
eventually below `n`:

`∀ᶠ n in atTop, M + c * padicValNat p n ≤ n`.

This is the estimate that makes a power series with coefficients `1 / n` converge on the open
unit disc of a `p`-adic field, for instance the logarithm series.
-/

public section

open Filter

namespace TauCeti

/-- The `p`-adic valuation of natural numbers grows sublinearly: for all constants `M` and `c`,
eventually `M + c * padicValNat p n ≤ n`. -/
theorem eventually_add_mul_padicValNat_le (p M c : ℕ) :
    ∀ᶠ n in atTop, M + c * padicValNat p n ≤ n := by
  rcases lt_or_ge p 2 with hp | hp
  · -- For `p ≤ 1` the valuation vanishes identically.
    filter_upwards [eventually_ge_atTop M] with n hn
    obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    all_goals simpa using hn
  refine eventually_atTop.2 ⟨M + c * (M + c * c + c) + 1, fun n hn => ?_⟩
  set k := padicValNat p n
  have hk : 2 ^ k ≤ n :=
    (Nat.pow_le_pow_left hp k).trans (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
  by_cases hkK : k ≤ M + c * c + c
  · have := Nat.mul_le_mul_left c hkK
    omega
  · -- Write `k = c + j`; then `2 ^ k ≥ (c + 1) * (j + 1)`, which exceeds `M + c * k`.
    obtain ⟨j, hj⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
    have hprod := Nat.mul_le_mul (Nat.lt_two_pow_self : c < 2 ^ c)
      (Nat.lt_two_pow_self : j < 2 ^ j)
    rw [← pow_add, ← hj] at hprod
    rw [hj] at hkK ⊢
    nlinarith

end TauCeti
