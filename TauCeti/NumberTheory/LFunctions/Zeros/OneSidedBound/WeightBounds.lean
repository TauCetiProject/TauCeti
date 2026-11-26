/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounds on weights of a theta-lift chain

For cutoffs `x ≤ x₁ ≤ b`, the two base weights are `x * b / x₁` and `b`. The shift at
index `i` adds `(i + 1) * r ^ 8`, where `r` is the target rank. Separation of the cutoffs gives
a lower bound for the smaller weight, so the shifts are small both additively and on taking logs.

The normalization is that of `New.Data.shiftedWeight` in `New/Reduction/Data/AdmissibleData`
and the estimates in `New/Reduction/Data/LevelAndTwists` of the shorter GRH formalization
(<https://github.com/lsernau/grh-lean>, revision `72fead1`).
-/

public section

namespace TauCeti.OneSidedBound

/-- Cutoffs separated by powers of exponent `k + 1` give a smaller weight between
`x ^ k` and `b / x ^ k`. Both quotients are natural-number quotients. -/
theorem cutoffWeight_mem_Icc {x x₁ b k : ℕ} (hx : 0 < x)
    (hxx₁ : x ^ (k + 1) ≤ x₁) (hx₁b : x₁ ^ (k + 1) ≤ b) :
    x * b / x₁ ∈ Set.Icc (x ^ k) (b / x ^ k) := by
  have h₁ : x ≤ x₁ := (Nat.le_self_pow (Nat.succ_ne_zero k) x).trans hxx₁
  have hx₁ : 0 < x₁ := hx.trans_le h₁
  constructor
  · apply (Nat.le_div_iff_mul_le hx₁).2
    calc
      x ^ k * x₁ ≤ x₁ ^ k * x₁ := by gcongr
      _ = x₁ ^ (k + 1) := (pow_succ x₁ k).symm
      _ ≤ b := hx₁b
      _ ≤ x * b := Nat.le_mul_of_pos_left b hx
  · apply (Nat.le_div_iff_mul_le (pow_pos hx k)).2
    apply Nat.le_of_mul_le_mul_right _ hx
    calc
      (x * b / x₁ * x ^ k) * x = x * b / x₁ * x ^ (k + 1) := by
        rw [mul_assoc, ← pow_succ]
      _ ≤ x * b / x₁ * x₁ := by gcongr
      _ ≤ b * x := by simpa [mul_comm] using Nat.mul_div_le (x * b) x₁

/-- Both choices of cutoff weight are multiples of `q` and lie between `x * b / x₁` and `b`
when `x ≤ x₁` and `b` is a multiple of `q * x₁`. -/
theorem dvd_and_cutoffWeight_mem_Icc {x x₁ b q : ℕ} (large : Prop) [Decidable large]
    (hx : x ≤ x₁) (hb : q * x₁ ∣ b) :
    q ∣ (if large then b else x * b / x₁) ∧
      (if large then b else x * b / x₁) ∈ Set.Icc (x * b / x₁) b := by
  have hle : x * b / x₁ ≤ b := Nat.div_le_of_le_mul (Nat.mul_le_mul_right b hx)
  split
  · exact ⟨(dvd_mul_right q x₁).trans hb, hle, le_rfl⟩
  · exact ⟨Nat.dvd_div_of_mul_dvd_right (hb.trans (dvd_mul_left b x)), le_rfl, hle⟩

/-- In a chain with `m² ≤ 4x` and `r ≤ 3x⁵`, the shift at any index up to `4m` is at most
`x ^ 42`, once `x ≥ 3 ^ 8`. -/
theorem shiftedWeight_mem_Icc {x m r i κ : ℕ} (hx : 3 ^ 8 ≤ x)
    (hm : m ^ 2 ≤ 4 * x) (hr : r ≤ 3 * x ^ 5) (hi : i ≤ 4 * m) :
    κ + (i + 1) * r ^ 8 ∈ Set.Icc κ (κ + x ^ 42) := by
  have hidx : i + 1 ≤ x := by
    by_cases h : m < 32
    · omega
    · have hmul : (32 : ℕ) * m ≤ m ^ 2 := by
        simpa [sq] using Nat.mul_le_mul_right m (by omega : 32 ≤ m)
      omega
  have hpow : r ^ 8 ≤ 3 ^ 8 * x ^ 40 := by
    simpa [mul_pow, ← pow_mul] using Nat.pow_le_pow_left hr 8
  refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left ?_ _⟩
  calc
    (i + 1) * r ^ 8 ≤ x * (3 ^ 8 * x ^ 40) := Nat.mul_le_mul hidx hpow
    _ ≤ x * (x * x ^ 40) := by gcongr
    _ = x ^ 42 := by rw [← pow_succ', ← pow_succ']

/-- The logarithm of a shifted weight increases by at most `1 / x` if the base weight
is at least `x ^ 43` and the shift is at most `x ^ 42`. -/
theorem log_shiftedWeight_le {x κ δ : ℕ} (hκ : x ^ 43 ≤ κ)
    (hδ : δ ≤ x ^ 42) : Real.log ((κ + δ : ℕ) : ℝ) ≤ Real.log κ + 1 / x := by
  obtain rfl | hx := Nat.eq_zero_or_pos x
  · have hδ₀ : δ = 0 := by simpa using hδ
    simp [hδ₀]
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  have hκR : 0 < (κ : ℝ) := by exact_mod_cast (pow_pos hx 43).trans_le hκ
  have hmul : (δ : ℝ) * x ≤ κ := by
    exact_mod_cast (Nat.mul_le_mul_right x hδ).trans (by simpa [← pow_succ] using hκ)
  have hr : ((κ : ℝ) + δ) / κ ≤ 1 + 1 / x := by
    rw [add_div, div_self hκR.ne', add_le_add_iff_left, div_le_div_iff₀ hκR hxR, one_mul]
    exact hmul
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < (κ : ℝ) + δ) hκR)
  rw [Real.log_div (by positivity : (κ : ℝ) + δ ≠ 0) hκR.ne'] at hlog
  push_cast
  linarith

/-- For a base weight at most `b`, the lift weights through index `2m` are at most `2b`
when `b` dominates the shift scale. The lift at index `j` uses shift index `2j`. -/
theorem liftWeight_le_two_mul {x m r j κ b : ℕ} (hx : 3 ^ 8 ≤ x)
    (hm : m ^ 2 ≤ 4 * x) (hr : r ≤ 3 * x ^ 5) (hj : j ≤ 2 * m)
    (hκ : κ ≤ b) (hb : x ^ 42 ≤ b) : κ + (2 * j + 1) * r ^ 8 ≤ 2 * b := by
  have h := (shiftedWeight_mem_Icc (κ := κ) hx hm hr (i := 2 * j) (by omega)).2
  exact h.trans (by simpa [two_mul] using Nat.add_le_add hκ hb)

end TauCeti.OneSidedBound
