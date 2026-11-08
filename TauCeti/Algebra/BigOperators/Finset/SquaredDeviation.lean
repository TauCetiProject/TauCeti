/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.WeightedVariance
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
  · let w : ℝ := 1 / s.card
    have hcard : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hs)
    have hw : ∑ i ∈ s, w = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp [w]
      field_simp
    have h := Finset.sum_mul_sub_sq_eq s (w := fun _ => w) hw c t
    simp only [← Finset.mul_sum] at h
    have hmean : w * ∑ i ∈ s, t i = (∑ i ∈ s, t i) / s.card := by
      dsimp [w]
      ring
    rw [hmean] at h
    have hreverse (a : ℝ) : (∑ i ∈ s, (a - t i) ^ 2) =
        ∑ i ∈ s, (t i - a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hreverse c, hreverse ((∑ i ∈ s, t i) / s.card)] at h
    have hscale : (s.card : ℝ) * w = 1 := by
      dsimp [w]
      field_simp
    have hscaled := congrArg (fun x : ℝ => (s.card : ℝ) * x) h
    simp only [mul_add, ← mul_assoc, hscale, one_mul] at hscaled
    simpa only [add_comm] using hscaled
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
