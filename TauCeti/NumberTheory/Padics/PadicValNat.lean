/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sublinear growth of the `p`-adic valuation of natural numbers

Since `p ^ padicValNat p n ∣ n`, the valuation `padicValNat p n` is at most logarithmic in `n`.
This file records the consequence that any fixed multiple of it, shifted by any constant, is
eventually below `n`:

`∀ᶠ n in atTop, M + c * padicValNat p n ≤ n`,

together with the uniform form `c * padicValNat p n ≤ n + C` for some constant `C`, and the sharp
bound `e * padicValNat p n < i * (n - 1)` for `n ≥ 2` whenever `e < (p - 1) * i`.

These are the estimates that make a power series with coefficients `1 / n` converge on the open
unit disc of a `p`-adic field, for instance the logarithm series, and make its nonlinear terms
strictly smaller than the linear one on sufficiently deep inputs.
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

/-- Scaled by any constant `c`, the `p`-adic valuation of natural numbers is bounded by `n` up to
an additive constant: for some `C`, `c * padicValNat p n ≤ n + C` for all `n`. -/
theorem exists_mul_padicValNat_le_add (p c : ℕ) : ∃ C, ∀ n, c * padicValNat p n ≤ n + C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_add_mul_padicValNat_le p 0 c)
  refine ⟨c * N, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · have := Nat.mul_le_mul_left c ((Nat.padicValNat_le_self (p := p) n).trans hn.le)
    omega
  · simpa using (hN n hn).trans (Nat.le_add_right n (c * N))

/-- If `e < (p - 1) * i`, then `e * padicValNat p n < i * (n - 1)` for every `n ≥ 2`. -/
theorem mul_padicValNat_lt_mul_sub_one {p e i n : ℕ} (hi : e < (p - 1) * i)
    (hn : 2 ≤ n) : e * padicValNat p n < i * (n - 1) := by
  set k := padicValNat p n
  -- From `p * k ≤ n`: `(p - 1) * k ≤ n - 1`, since `k = 0` or `k ≥ 1`.
  have hk : (p - 1) * k ≤ n - 1 := by
    have h : p * k ≤ n := mul_padicValNat_le
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0]
    · rw [Nat.sub_one_mul]
      omega
  refine Nat.lt_of_mul_lt_mul_left (a := p - 1) ?_
  calc (p - 1) * (e * k) = e * ((p - 1) * k) := by ring
    _ ≤ e * (n - 1) := Nat.mul_le_mul_left e hk
    _ < (p - 1) * i * (n - 1) := Nat.mul_lt_mul_of_pos_right hi (by omega)
    _ = (p - 1) * (i * (n - 1)) := by ring

end TauCeti
