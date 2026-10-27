/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring

/-!
# Geometric series in seminormed rings and normed fields

The norms of the powers of an element in the open unit ball form a summable series, even when
the seminorm is not normalized. The same holds after multiplication by bounded coefficients.
Completeness then gives summability in the ring itself.

Over a normed field, the evaluations below specialize Mathlib's binomial geometric-series
formula to linear and quadratic coefficients, without requiring completeness or an ultrametric norm.
-/

public section

namespace TauCeti

/-- The norms of the powers of an element in the open unit ball are summable in a seminormed
ring, without requiring a normalized seminorm. -/
theorem summable_norm_pow_of_norm_lt_one {K : Type*} [SeminormedRing K]
    {q : K} (hq : ‖q‖ < 1) : Summable (fun n : ℕ ↦ ‖q ^ n‖) := by
  -- The positive-degree estimate does not require any bound on the seminorm of one.
  rw [← summable_nat_add_iff 1]
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_pow_le' q n.succ_pos)
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq))

/-- A geometric series with bounded coefficients is absolutely summable in a seminormed ring
when the parameter belongs to the open unit ball. -/
theorem summable_norm_mul_pow_of_norm_le {K : Type*} [SeminormedRing K]
    {b : ℕ → K} {C : ℝ} (hb : ∀ n, ‖b n‖ ≤ C) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖b n * q ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_norm_pow_of_norm_lt_one hq).mul_left C)
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))

/-- A geometric series with bounded coefficients is summable in a complete seminormed ring
when the parameter belongs to the open unit ball. -/
theorem summable_mul_pow_of_norm_le {K : Type*} [SeminormedRing K] [CompleteSpace K]
    {b : ℕ → K} {C : ℝ} (hb : ∀ n, ‖b n‖ ≤ C) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ b n * q ^ n) :=
  (summable_norm_mul_pow_of_norm_le hb hq).of_norm

variable {K : Type*} [NormedField K]

/-- The geometric series with coefficient and exponent both shifted by one. -/
theorem tsum_natCast_succ_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, ((d + 1 : ℕ) : K) * r ^ (d + 1)) = r / (1 - r) ^ 2 := by
  calc
    _ = r * ∑' d : ℕ, (((d + 1).choose 1 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      simp only [Nat.choose_one_right, pow_succ]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 1 hr]; ring

/-- The shifted geometric series weighted by `choose (d + 1) 2`. -/
theorem tsum_choose_two_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, (((d + 1).choose 2 : ℕ) : K) * r ^ (d + 1)) = r ^ 2 / (1 - r) ^ 3 := by
  have ht : Summable (fun d : ℕ ↦ (((d + 1 + 1).choose 2 : ℕ) : K) * r ^ (d + 1 + 1)) := by
    refine ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).summable.mul_right (r ^ 2)).congr ?_
    intro d
    rw [Nat.add_assoc, pow_add]
    ring
  rw [tsum_eq_zero_add' (f := fun d : ℕ ↦ (((d + 1).choose 2 : ℕ) : K) * r ^ (d + 1)) ht]
  simp only [Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.cast_zero, zero_mul, zero_add]
  calc
    _ = r ^ 2 * ∑' d : ℕ, (((d + 2).choose 2 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      rw [Nat.add_assoc, pow_add]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hr]; ring

/-- The shifted geometric series weighted by `-choose (d + 2) 2`. -/
theorem tsum_neg_choose_two_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, -((((d + 1 + 1).choose 2 : ℕ) : K)) * r ^ (d + 1)) =
      -r / (1 - r) ^ 3 := by
  calc
    _ = -r * ∑' d : ℕ, (((d + 2).choose 2 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      rw [Nat.add_assoc, pow_succ]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hr]; ring

end TauCeti

end
