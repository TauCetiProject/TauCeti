/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.Codimension
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Dimension of the ramified source of a theta lift

The ramification conditions are the kernels of the cyclic sums of the level-prime translations.
Given the fixed-space bound for one translation, intersecting the conditions loses at most a
fraction `f / (N - 1)` of the source dimension, where `f` bounds the number of places involved.
The separation of the level prime from the prime-sum scale bounds this fraction by `b⁻⁸`.

The bounds are those of `New.Data.le_finrank_ramifiedSourceForms` and
`New.Data.f_div_N_sub_one_le` in `grh/src/New/UpperBound/Size/ShortColumns.lean` of
lsernau/grh-lean (`72fead1`).
-/

public section

open Module

namespace TauCeti.OneSidedBound

/-- The simultaneous cyclic norm conditions at the level prime leave at least the indicated
fraction of the source. Here `f` is an upper bound on the number of local conditions. -/
theorem le_finrank_ramifiedSourceForms {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] (z : ι → Module.End K V) {N f : ℕ} (hN : 1 ≤ N) (hf : Fintype.card ι ≤ f)
    (hz : ∀ w, z w ^ (N - 1) = 1)
    (hfix : ∀ w, (N - 1) * finrank K (z w).fixedSubmodule ≤ finrank K V) :
    (1 - (f : ℝ) / (N - 1)) * finrank K V ≤
      (finrank K (↥(⨅ w, LinearMap.ker (∑ i ∈ Finset.range (N - 1), z w ^ i)) : Type _) : ℝ) := by
  obtain rfl | hN' := hN.eq_or_lt
  · have htop : (⨅ w, LinearMap.ker (∑ i ∈ Finset.range (1 - 1), z w ^ i)) = ⊤ := by simp
    rw [htop, finrank_top]
    simp
  have hpos : 0 < (N : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hN')
  have hdim := LinearMap.mul_finrank_iInf_ker_sum_pow_ge z hz hfix
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by simpa using Nat.cast_sub (R := ℝ) hN
  have hmul : (N - 1 - f) * finrank K V ≤ (N - 1) *
      finrank K (↥(⨅ w, LinearMap.ker (∑ i ∈ Finset.range (N - 1), z w ^ i)) : Type _) :=
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hf _)).trans hdim
  by_cases h : f ≤ N - 1
  · have hone : 1 - (f : ℝ) / (N - 1) = ((N : ℝ) - 1 - f) / (N - 1) := by
      rw [sub_div, div_self hpos.ne']
    rw [hone, div_mul_eq_mul_div]
    -- The denominator is positive, so the natural-number estimate can be cast directly.
    apply (div_le_iff₀ hpos).2
    simpa only [Nat.cast_mul, Nat.cast_sub h, hcast, mul_comm] using
      (Nat.cast_le (α := ℝ)).mpr hmul
  · have h' : (N : ℝ) - 1 ≤ f := by
      rw [← hcast]
      exact_mod_cast (Nat.le_of_not_ge h)
    have : 1 ≤ (f : ℝ) / (N - 1) := by rwa [le_div_iff₀ hpos, one_mul]
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr this) (Nat.cast_nonneg _)).trans
      (Nat.cast_nonneg _)

/-- For a scale `b` dominating the number of places, level `N ≥ b ^ 10` makes the fractional
loss at most `1 / b ^ 8`. -/
theorem f_div_N_sub_one_le {f b N : ℕ} (hf : f ≤ b) (hN : b ^ 10 ≤ N) :
    (f : ℝ) / (N - 1) ≤ 1 / (b : ℝ) ^ 8 := by
  by_cases hb : 2 ≤ b
  · have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have hf' : (f : ℝ) ≤ b := by exact_mod_cast hf
    have hN' : (b : ℝ) ^ 10 ≤ N := by exact_mod_cast hN
    have hpow : 1 ≤ (b : ℝ) ^ 9 := one_le_pow₀ (by linarith)
    have hle : (b : ℝ) ^ 9 + 1 ≤ N := calc
      _ ≤ 2 * (b : ℝ) ^ 9 := by linarith
      _ ≤ (b : ℝ) * (b : ℝ) ^ 9 := mul_le_mul_of_nonneg_right hb' (by positivity)
      _ = (b : ℝ) ^ 10 := (pow_succ' _ 9).symm
      _ ≤ N := hN'
    rw [div_le_div_iff₀ (by linarith) (pow_pos (by linarith) _), one_mul]
    calc
      (f : ℝ) * (b : ℝ) ^ 8 ≤ (b : ℝ) * (b : ℝ) ^ 8 :=
        mul_le_mul_of_nonneg_right hf' (by positivity)
      _ = (b : ℝ) ^ 9 := (pow_succ' _ 8).symm
      _ ≤ (N : ℝ) - 1 := by linarith
  · have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · simp [Nat.eq_zero_of_le_zero hf]
    · by_cases h : N = 1
      · simp [h]
      have hN' : (2 : ℕ) ≤ N := by simp at hN; omega
      have hle : (f : ℝ) ≤ 1 := by exact_mod_cast hf
      have hle' : (2 : ℝ) ≤ N := by exact_mod_cast hN'
      simp only [Nat.cast_one, one_pow, div_one]
      rw [div_le_iff₀ (by linarith : 0 < (N : ℝ) - 1)]
      linarith

end TauCeti.OneSidedBound
