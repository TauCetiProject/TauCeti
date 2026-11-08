/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Squared deviations from a finite mean

The sum of squared deviations splits into the sum at the mean and the squared excess.
-/

public section

namespace Finset

/-- The sum of squared deviations from `c` equals the sum at the mean plus the excess.
This also holds for the empty set, where the mean is defined as zero. -/
theorem sum_sq_sub_mean {ι : Type*} (s : Finset ι) (t : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, (t i - c) ^ 2) =
      (∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2) +
        s.card * (c - (∑ j ∈ s, t j) / s.card) ^ 2 := by
  by_cases hs : s.Nonempty
  · let a : ℝ := (∑ i ∈ s, t i) / s.card
    have hcard : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hs)
    have hsum : ∑ i ∈ s, t i = (s.card : ℝ) * a := by
      dsimp [a]
      field_simp [hcard]
    have hsum_centered : ∑ i ∈ s, (t i - a) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum]
      ring
    change (∑ i ∈ s, (t i - c) ^ 2) =
      (∑ i ∈ s, (t i - a) ^ 2) + s.card * (c - a) ^ 2
    calc
      (∑ i ∈ s, (t i - c) ^ 2) =
          ∑ i ∈ s, ((t i - a) ^ 2 + (c - a) ^ 2 - 2 * (t i - a) * (c - a)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i ∈ s, (t i - a) ^ 2) + s.card * (c - a) ^ 2 -
            2 * (∑ i ∈ s, (t i - a)) * (c - a) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul]
        have hcross : (∑ i ∈ s, 2 * (t i - a) * (c - a)) =
            2 * (∑ i ∈ s, (t i - a)) * (c - a) := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
        rw [hcross]
      _ = (∑ i ∈ s, (t i - a) ^ 2) + s.card * (c - a) ^ 2 := by
        rw [hsum_centered]
        ring
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

/-- The mean minimizes the sum of squared deviations, even for an empty set. -/
theorem sum_sq_sub_mean_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2) ≤
      ∑ i ∈ s, (t i - c) ^ 2 := by
  calc
    (∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2) ≤
        (∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2) +
          s.card * (c - (∑ j ∈ s, t j) / s.card) ^ 2 :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = ∑ i ∈ s, (t i - c) ^ 2 := (sum_sq_sub_mean s t c).symm

/-- On a nonempty set, equality with the minimum holds only at the mean. -/
theorem sum_sq_sub_mean_eq_iff {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (hs : s.Nonempty) (c : ℝ) :
    (∑ i ∈ s, (t i - c) ^ 2) =
        (∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2) ↔
      c = (∑ j ∈ s, t j) / s.card := by
  rw [sum_sq_sub_mean, add_eq_left]
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  rw [mul_eq_zero, or_iff_right hcard, sq_eq_zero_iff, sub_eq_zero]

end Finset
