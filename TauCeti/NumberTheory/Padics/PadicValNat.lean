/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

The logarithmic form of the bound, `padicValNat p n * log p ≤ log n` (so in particular
`padicValNat p n ≤ log n / log 2`), bounds the exponents of an
integer composed of finitely many primes by its logarithm, as needed for gaps between such
integers and for exponential Diophantine equations.
-/

public section

open Filter

namespace TauCeti

/-- The `p`-adic valuation of natural numbers grows sublinearly: for all constants `M` and `c`,
eventually `M + c * padicValNat p n ≤ n`. -/
theorem eventually_add_mul_padicValNat_le (p M c : ℕ) :
    ∀ᶠ n in atTop, M + c * padicValNat p n ≤ n := by
  simp only [Nat.padicValNat_def]
  rcases lt_or_ge p 2 with hp | hp
  · -- For `p ≤ 1` the valuation vanishes identically.
    filter_upwards [eventually_ge_atTop M] with n hn
    obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    all_goals simpa using hn
  refine eventually_atTop.2 ⟨M + c * (M + c * c + c) + 1, fun n hn => ?_⟩
  set k := multiplicity p n
  have hk : 2 ^ k ≤ n :=
    (Nat.pow_le_pow_left hp k).trans (Nat.le_of_dvd (by omega) (pow_multiplicity_dvd p n))
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
  rcases le_total N n with hn | hn
  · have := hN n hn
    omega
  · have := Nat.mul_le_mul_left c
      ((Nat.padicValNat_def.trans_le (Nat.multiplicity_le_self (p := p) n)).trans hn)
    omega

/-- If `e < (p - 1) * i`, then `e * padicValNat p n < i * (n - 1)` for every `n ≥ 2`. -/
theorem mul_padicValNat_lt_mul_sub_one {p e i n : ℕ} (hi : e < (p - 1) * i)
    (hn : 2 ≤ n) : e * padicValNat p n < i * (n - 1) := by
  rw [Nat.padicValNat_def]
  set k := multiplicity p n
  -- From `p * k ≤ n`: `(p - 1) * k ≤ n - 1`, since `k = 0` or `k ≥ 1`.
  have hk : (p - 1) * k ≤ n - 1 := by
    have h : p * k ≤ n := mul_multiplicity_le
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0]
    · rw [Nat.sub_one_mul]
      omega
  refine Nat.lt_of_mul_lt_mul_left (a := p - 1) ?_
  calc (p - 1) * (e * k) = e * ((p - 1) * k) := by ring
    _ ≤ e * (n - 1) := Nat.mul_le_mul_left e hk
    _ < (p - 1) * i * (n - 1) := Nat.mul_lt_mul_of_pos_right hi (by omega)
    _ = (p - 1) * (i * (n - 1)) := by ring

/-- The `p`-adic valuation of `n` is at most logarithmic in `n`:
`padicValNat p n * log p ≤ log n`. -/
theorem padicValNat_mul_log_le_log (p n : ℕ) : padicValNat p n * Real.log p ≤ Real.log n := by
  rw [Nat.padicValNat_def]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rcases p.eq_zero_or_pos with rfl | hp
  · simpa using Real.log_natCast_nonneg n
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) (mod_cast Nat.le_of_dvd hn (pow_multiplicity_dvd p n))

/-- The `p`-adic valuation of `n` is at most `log n / log 2`. -/
theorem padicValNat_le_log_div_log_two (p n : ℕ) :
    (padicValNat p n : ℝ) ≤ Real.log n / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos one_lt_two)]
  rcases lt_or_ge p 2 with hp | hp
  · -- For `p ≤ 1` the valuation vanishes identically.
    obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    all_goals simpa [Nat.padicValNat_def] using Real.log_natCast_nonneg n
  refine le_trans ?_ (padicValNat_mul_log_le_log p n)
  gcongr
  exact_mod_cast hp

end TauCeti
