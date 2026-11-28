/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.WeightedVariance
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Squared deviations from a finite mean

The sum of squared deviations splits into the sum at the mean and the squared excess, over any
field of characteristic zero. Over `ℝ` the mean therefore minimizes the sum of squared deviations,
and on a nonempty set only the mean does.
-/

public section

namespace Finset

/-- The sum of squared deviations from `c` equals the sum at the mean plus the excess, over any
field of characteristic zero. This also holds for the empty set, where the mean is defined as
zero. -/
theorem sum_sq_sub_mean {ι R : Type*} [Field R] [CharZero R] (s : Finset ι) (t : ι → R) (c : R) :
    (∑ i ∈ s, (t i - c) ^ 2) =
      (∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2) +
        s.card * (c - (∑ j ∈ s, t j) / s.card) ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hcard : (s.card : R) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero.2 hs)
  -- The weighted identity with the uniform weights `1 / card s`, scaled by `card s`.
  have h := sum_mul_sub_sq_eq s (w := fun _ ↦ (s.card : R)⁻¹) (by simp [hcard]) c t
  simp only [← mul_sum, ← div_eq_inv_mul (∑ i ∈ s, t i)] at h
  have hflip (a : R) : ∑ i ∈ s, (a - t i) ^ 2 = ∑ i ∈ s, (t i - a) ^ 2 :=
    sum_congr rfl fun i _ ↦ by ring
  rw [hflip, hflip] at h
  have hscaled := congrArg ((s.card : R) * ·) h
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul] at hscaled
  rw [hscaled, add_comm]

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
    exact_mod_cast (card_ne_zero.mpr hs)
  rw [mul_eq_zero, or_iff_right hcard, sq_eq_zero_iff, sub_eq_zero]

end Finset
