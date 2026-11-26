/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import TauCeti.Analysis.SpecialFunctions.Log.PowerDecay

/-!
# One-sided estimates from a second cutoff

An inequality at an integer cutoff has a main term controlled by the size of the lift count and
errors from two remainders evaluated at a much larger cutoff. Inverse-logarithmic decay at that
second cutoff makes the errors negligible. The scale and constant are those in
`New.eventually_primeRemainder_natCast_le` in lsernau/grh-lean at `72fead1`.
-/

public section

open Filter Real

namespace TauCeti

/-- Transfer the two-cutoff inequality to a one-sided power bound at integer cutoffs. Here `C`
is the coefficient of the main term, `y` the second cutoff, `L` the logarithmic scale, and `m`
the lift count. The two remainders need rapid logarithmic decay at `y`, not at the initial
cutoff. -/
theorem eventually_le_rpow_natCast_of_two_cutoffs {R S : ℝ → ℝ} {C ε : ℝ} {B : ℕ} (hC : 0 ≤ C)
    (hB : 24 ≤ ε * (B : ℝ)) (hR : ∀ᶠ y : ℝ in atTop, |R y| ≤ log y ^ (-(B : ℝ)))
    (hS : ∀ᶠ y : ℝ in atTop, |S y| ≤ log y ^ (-(B : ℝ)))
    (hMain : ∀ᶠ n : ℕ in atTop, ∃ y > 0, ∃ L ≥ 0, ∃ m : ℝ,
      (n : ℝ) ^ (ε / 6) - 1 ≤ log y ∧ L ≤ (n : ℝ) ^ ε + 1 ∧ √(n : ℝ) ≤ m ∧
      R n ≤ C * L ^ 6 / m + |R y| + L * |S y|) :
    ∀ᶠ n : ℕ in atTop, R n ≤ (64 * C + 3) * (n : ℝ) ^ (-(1 / 2) + 6 * ε) := by
  have hε : 0 < ε := pos_of_mul_pos_left (by linarith only [hB]) (Nat.cast_nonneg B)
  have hδ : 0 < ε / 6 := by positivity
  have hpowerr : -(ε / 6 / 2) * (B : ℝ) ≤ -2 := by linarith only [hB]
  have hcast : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hMain, eventually_ge_atTop (1 : ℕ),
    hcast.eventually (eventually_abs_le_rpow_of_log_rpow_decay hδ hpowerr hR),
    hcast.eventually (eventually_abs_le_rpow_of_log_rpow_decay hδ hpowerr hS)] with n hn hn₁ hRy hSy
  obtain ⟨y, hy, L, hL, m, hylog, hLmax, hm, hsum⟩ := hn
  let x : ℝ := n
  have hx₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn₁
  have hx : 0 < x := zero_lt_one.trans_le hx₁
  have hL₂ : L ≤ 2 * x ^ ε := by
    have hpow := one_le_rpow hx₁ hε.le
    linarith only [hLmax, hpow]
  rw [sqrt_eq_rpow] at hm
  have hmain : C * L ^ 6 / m ≤ 64 * C * x ^ (-(1 / 2) + 6 * ε) := by
    calc
      _ ≤ C * (2 * x ^ ε) ^ 6 / x ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := by
        rw [mul_pow, ← rpow_mul_natCast hx.le, rpow_add hx, rpow_neg hx.le, div_eq_mul_inv]
        norm_num
        ring_nf
  have hRerr := (hRy y hy hylog).trans (rpow_le_rpow_of_exponent_le hx₁ (by linarith :
    (-2 : ℝ) ≤ -(1 / 2) + 6 * ε))
  have hSerr : L * |S y| ≤ 2 * x ^ (-(1 / 2) + 6 * ε) := by
    calc
      _ ≤ (2 * x ^ ε) * x ^ (-2 : ℝ) := by gcongr; exact hSy y hy hylog
      _ = 2 * x ^ (ε - 2) := by rw [sub_eq_add_neg, rpow_add hx, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_le hx₁ (by linarith)) (by norm_num)
  linarith only [hsum, hmain, hRerr, hSerr]

end TauCeti
