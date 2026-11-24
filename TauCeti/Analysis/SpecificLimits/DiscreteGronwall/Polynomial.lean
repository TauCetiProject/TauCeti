/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Discrete Grönwall polynomial-growth bounds

A nonnegative sequence `μ : ℕ → ℝ` whose `s`-th term is bounded by
`(K / s) * (c + ∑_{k < s} μ k)` for `s ≥ s₀ ≥ 1` has partial sums `c + ∑_{k < s} μ k` bounded
polynomially by `(c + ∑_{k < s₀} μ k) * s ^ K` (`TauCeti.add_sum_range_le_mul_pow_of_le_div`),
derived from `antitoneOn_nat_Ici_of_succ_le` on the normalized sequence
`(c + ∑_{k < s} μ k) / s ^ K` via the Bernoulli step. This bound controls weighted coefficients in
power-series convergence arguments for complex ODEs.
-/

public section

namespace TauCeti

/-- Discrete Grönwall polynomial-growth bound: if `0 ≤ c`, `μ s ≥ 0`, and
`μ s ≤ (K / s) * (c + ∑_{k < s} μ k)` for all `s ≥ s₀ ≥ 1`, then
`c + ∑_{k < s} μ k ≤ (c + ∑_{k < s₀} μ k) * s ^ K` for all `s ≥ s₀`. -/
theorem add_sum_range_le_mul_pow_of_le_div {μ : ℕ → ℝ} {c : ℝ} {s₀ K : ℕ}
    (hs₀1 : 1 ≤ s₀) (hc : 0 ≤ c) (hμ0 : ∀ s, 0 ≤ μ s)
    (hstep : ∀ s : ℕ, s₀ ≤ s → μ s ≤ (K : ℝ) / s * (c + ∑ k ∈ Finset.range s, μ k)) :
    ∀ s : ℕ, s₀ ≤ s →
      c + ∑ k ∈ Finset.range s, μ k ≤ (c + ∑ k ∈ Finset.range s₀, μ k) * (s : ℝ) ^ K := by
  set S : ℕ → ℝ := fun s ↦ c + ∑ k ∈ Finset.range s, μ k
  have hS_nn : ∀ s, 0 ≤ S s := fun s ↦
    add_nonneg hc (Finset.sum_nonneg fun k _ ↦ hμ0 k)
  set u : ℕ → ℝ := fun s ↦ S s / (s : ℝ) ^ K
  have hu_step : ∀ s ≥ s₀, u (s + 1) ≤ u s := by
    intro s hs
    have hs_pos : (0 : ℝ) < s := by exact_mod_cast (hs₀1.trans hs)
    have hpow_step : (s : ℝ) ^ K * (1 + (K : ℝ) / s) ≤ ((s + 1 : ℕ) : ℝ) ^ K := by
      rw [div_eq_mul_inv]
      refine (mul_le_mul_of_nonneg_left
        (one_add_mul_le_pow (by linarith [inv_nonneg.mpr hs_pos.le]) K) (by positivity)).trans_eq ?_
      rw [← mul_pow]
      push_cast
      rw [mul_add, mul_one, mul_inv_cancel₀ hs_pos.ne']
    have hSs : S (s + 1) = S s + μ s := by simp [S, Finset.sum_range_succ, add_assoc]
    have hS_le : S (s + 1) ≤ S s * (1 + (K : ℝ) / s) := by linarith [hSs, hstep s hs]
    have hden_pos : (0 : ℝ) < (s : ℝ) ^ K * (1 + (K : ℝ) / s) := by positivity
    dsimp only [u]
    calc S (s + 1) / ((s + 1 : ℕ) : ℝ) ^ K
        ≤ S (s + 1) / ((s : ℝ) ^ K * (1 + (K : ℝ) / s)) :=
            div_le_div_of_nonneg_left (hS_nn (s + 1)) hden_pos hpow_step
      _ ≤ (S s * (1 + (K : ℝ) / s)) / ((s : ℝ) ^ K * (1 + (K : ℝ) / s)) := by gcongr
      _ = S s / (s : ℝ) ^ K := by
            rw [mul_div_mul_right _ _ (by positivity)]
  intro s hs
  have hgr : u s ≤ u s₀ :=
    antitoneOn_nat_Ici_of_succ_le hu_step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  have hs_pos : (0 : ℝ) < (s : ℝ) ^ K := by
    have : (0 : ℝ) < s := by exact_mod_cast (hs₀1.trans hs)
    positivity
  have hs₀_ge : (1 : ℝ) ≤ (s₀ : ℝ) ^ K :=
    one_le_pow₀ (n := K) (by exact_mod_cast hs₀1)
  calc S s = u s * (s : ℝ) ^ K := (div_mul_cancel₀ _ hs_pos.ne').symm
    _ ≤ u s₀ * (s : ℝ) ^ K := mul_le_mul_of_nonneg_right hgr hs_pos.le
    _ ≤ S s₀ * (s : ℝ) ^ K := mul_le_mul_of_nonneg_right (div_le_self (hS_nn s₀) hs₀_ge) hs_pos.le

end TauCeti
