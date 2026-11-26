/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import TauCeti.Combinatorics.Additive.NoRelation

/-!
# Quantitative modular Behrend sets

Choose the side length in Behrend's digit construction to obtain many exponents avoiding
weighted means modulo a prescribed order. The estimate controls the loss of cardinality when
these exponents are used to select points in a cyclic orbit. For `1 ≤ L`, `L^n ≤ W`, and
`W ≤ o`, the box with side `H` and base `L * H` fits below `o` if `H^n ≤ o / W`;
the inequality `o / W < (2H)^n` bounds the rounding loss.

The size estimate follows the parameter choice in `New.Parameters.exists_isSparse`,
`grh/src/New/Reduction/Data/Existence.lean` in lsernau/grh-lean (`72fead1`), rounding the side
length to an integer rather than to a power of two.
-/

public section

open scoped Finset

namespace TauCeti

/-- A large set of exponents in `[0, o)` avoiding nonconstant mean relations of total weight at
most `L` modulo `o`. Here `n` is the digit dimension, while `W` bounds the size of the weights
raised to `n` and controls the loss of cardinality. -/
theorem exists_large_modular_behrend_set {n L o : ℕ} {W : ℝ} (hn : n ≠ 0)
    (hL : (L : ℝ) ^ n ≤ W) (ho : (o : ℝ) ≤ W ^ (n + 1)) :
    ∃ S : Finset ℕ, (∀ e ∈ S, e < o) ∧ (o : ℝ) ≤ #S * ((n : ℝ) * 2 ^ n * W ^ 3) ∧
      ∀ e₁ ∈ S, ∀ e₂ ∈ S, ∀ e₃ ∈ S, ∀ α α' : ℕ, 0 < α → 0 < α' → α + α' ≤ L →
        (α + α') * e₂ ≡ α * e₁ + α' * e₃ [MOD o] → e₁ = e₂ ∧ e₂ = e₃ := by
  by_cases ho₀ : o = 0
  · exact ⟨∅, by simp, by simp [ho₀], by simp⟩
  have hW₀ : 0 ≤ W := (pow_nonneg (Nat.cast_nonneg _) _).trans hL
  have hW : 1 ≤ W := (one_le_pow_iff_of_nonneg hW₀ (Nat.succ_ne_zero n)).mp
    ((by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ho₀ : (1 : ℝ) ≤ o).trans ho)
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  by_cases hWo : W ≤ o
  · let H := Nat.nthRoot n ⌊(o : ℝ) / W⌋₊
    have hH : (H : ℝ) ^ n ≤ o / W := by
      rw [← Nat.cast_pow]
      exact (Nat.cast_le.mpr (Nat.pow_nthRoot_le (.inl hn))).trans (Nat.floor_le (by positivity))
    have hH₁ : 1 ≤ H := (Nat.le_nthRoot_iff hn).mpr (by
      rwa [one_pow, Nat.le_floor_iff' one_ne_zero, Nat.cast_one,
        le_div_iff₀ (by positivity), one_mul])
    have hH₂ : (H : ℝ) ≤ W := (pow_le_pow_iff_left₀ (by positivity) hW₀ hn).mp
      (hH.trans ((div_le_iff₀ (by positivity)).mpr (by simpa only [pow_succ] using ho)))
    have hlo : (o : ℝ) / W < ((2 * H : ℕ) : ℝ) ^ n := by
      rw [← Nat.cast_pow, ← Nat.floor_lt' (by positivity)]
      exact (Nat.lt_pow_nthRoot_add_one hn _).trans_le (Nat.pow_le_pow_left (by omega) _)
    let B := max 1 L
    have hBW : (B : ℝ) ^ n ≤ W := by
      simpa only [B, Nat.cast_max, Nat.cast_one,
        max_pow_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) (Nat.cast_nonneg L) n, one_pow] using
        max_le hW hL
    have hfit : (B * H) ^ n ≤ o := by
      exact_mod_cast calc
        ((B : ℝ) * H) ^ n = (B : ℝ) ^ n * (H : ℝ) ^ n := mul_pow ..
        _ ≤ W * ((o : ℝ) / W) := by gcongr
        _ = o := mul_div_cancel₀ _ (by positivity)
    obtain ⟨S, hS, hcard, hmean⟩ := exists_eq_and_eq_of_add_mul_modEq (n := n)
      (H := H) (L := B) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)) hfit
    have hh : (H : ℝ) ^ n ≤ #S * ((n : ℝ) * (H : ℝ) ^ 2) :=
      (div_le_iff₀ (by positivity)).mp (by exact_mod_cast hcard)
    refine ⟨S, hS, ?_, fun e₁ h₁ e₂ h₂ e₃ h₃ α α' hα hα' hαL ↦
      hmean e₁ h₁ e₂ h₂ e₃ h₃ α α' hα hα' (hαL.trans (le_max_right ..))⟩
    calc
      (o : ℝ) ≤ ((2 * H : ℕ) : ℝ) ^ n * W := ((div_lt_iff₀ (by positivity)).mp hlo).le
      _ = (2 : ℝ) ^ n * (H : ℝ) ^ n * W := by rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow]
      _ ≤ (2 : ℝ) ^ n * (#S * ((n : ℝ) * W ^ 2)) * W := by
        gcongr
        exact hh.trans (by gcongr)
      _ = _ := by ring
  · refine ⟨{0}, by simpa using Nat.pos_of_ne_zero ho₀, ?_, ?_⟩
    · simp only [Finset.card_singleton, Nat.cast_one, one_mul]
      refine (le_of_not_ge hWo).trans ?_
      have ht : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      calc
        W = 1 * 1 * W ^ 1 := by simp
        _ ≤ (n : ℝ) * 2 ^ n * W ^ 3 := by gcongr; norm_num
    · simp

end TauCeti
