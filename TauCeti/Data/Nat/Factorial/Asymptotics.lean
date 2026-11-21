/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Falling factorials of proportional sequences

A fixed shift of a natural count and each of the fixed offsets in its falling factorial have
vanishing effect after scaling by a denominator tending to infinity. This also applies when
the ratio tends to zero and the numerator itself may stay bounded.
-/

public section

open Filter
open scoped Topology

/-- If `p i / n i → y` and `n i → ∞`, the order-`k` falling factorial of `p i - r`, divided
by `(n i)^k`, tends to `y^k` for each fixed shift `r` and order `k`. -/
theorem Filter.Tendsto.natCast_descFactorial_sub_div_pow {ι : Type*} {l : Filter ι}
    {p n : ι → ℕ} {y : ℝ} (hn : Tendsto n l atTop)
    (hy : Tendsto (fun i ↦ (p i : ℝ) / n i) l (𝓝 y)) (r k : ℕ) :
    Tendsto (fun i ↦ ((p i - r).descFactorial k : ℝ) / (n i : ℝ) ^ k) l (𝓝 (y ^ k)) := by
  have hnR : Tendsto (fun i ↦ (n i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hn
  have hoffset (s : ℕ) : Tendsto (fun i ↦ ((p i - s : ℕ) : ℝ) / n i) l (𝓝 y) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun i ↦ (p i : ℝ) / n i - (s : ℝ) / n i) ?_ hy ?_ ?_
    · simpa only [sub_zero] using hy.sub (hnR.const_div_atTop (s : ℝ))
    · intro i
      dsimp only
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      by_cases hs : s ≤ p i
      · rw [Nat.cast_sub hs]
      · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, sub_nonpos]
        exact_mod_cast (by omega : p i ≤ s)
    · intro i
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) (Nat.cast_nonneg _)
  induction k with
  | zero => simpa only [Nat.descFactorial_zero, Nat.cast_one, pow_zero, div_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℝ)) l (𝓝 1))
  | succ k ih =>
    simp only [Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul, pow_succ' _ k,
      ← div_mul_div_comm]
    exact (hoffset (r + k)).mul ih
