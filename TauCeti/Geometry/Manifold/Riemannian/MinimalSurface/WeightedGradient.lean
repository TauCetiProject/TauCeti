/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# A completed square for weighted gradient combinations

Two cleared scalar identities yield an exact square for a weighted combination of two vectors.
The square identity allows either scalar weight to vanish. When both weights and the combination
coefficient are positive, discarding the square gives the corresponding sharp lower bound.
Separate bounds at vanishing weights extend it to nonnegative weights with positive combination.
The coefficient one third in the reaction polynomial gives the constant six fifths.

This is the algebraic part of the Bochner–Simons argument for positive Jacobi fields on minimal
surfaces in S. Lynch, *The Cheng–Yau gradient estimate for Jacobi fields*, Proposition 4.1 and
the subsequent one-third specialization in §4, [arXiv:2611.12758v1](https://arxiv.org/abs/2611.12758v1).
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Cleared scalar identities give an exact completed square for their weighted combination. -/
theorem weighted_gradient_cleared_identity (c q s a b : ℝ) (u v w : V)
    (hu : ‖u‖ ^ 2 = q)
    (hB : q * a = ‖v‖ ^ 2 + 2 * s * inner ℝ u v - 2 * q * inner ℝ u w +
      q * (2 * q ^ 2 + 3 * q * s + 2 * s ^ 2))
    (hS : s * b = ‖w‖ ^ 2 - 2 * s ^ 3) (hc : c ≠ 0) :
    c * s * q * ((q + c * s) * (a + c * b) - ‖v + c • w‖ ^ 2 -
      (q + c * s) * (2 * q ^ 2 + (3 - 1 / c) * q * s + (1 - 2 * c) * s ^ 2)) =
      ‖(c * s) • v - (c * q) • w + (s * (q + c * s)) • u‖ ^ 2 := by
  have hP : c * (2 * q ^ 2 + (3 - 1 / c) * q * s + (1 - 2 * c) * s ^ 2) =
      c * (2 * q ^ 2 + 3 * q * s + (2 - 2 * c) * s ^ 2) - s * (q + c * s) := by
    field_simp [hc]
    ring
  simp only [norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, real_inner_smul_left, real_inner_smul_right, inner_sub_left]
  rw [hu, real_inner_comm u v, real_inner_comm u w]
  linear_combination c * s * (q + c * s) * hB +
    c ^ 2 * q * (q + c * s) * hS - s * q * (q + c * s) * hP

/-- Positive weights turn the completed square into a lower bound for the combination. -/
theorem weighted_gradient_combination_le (c q s a b : ℝ) (u v w : V)
    (hu : ‖u‖ ^ 2 = q)
    (hB : q * a = ‖v‖ ^ 2 + 2 * s * inner ℝ u v - 2 * q * inner ℝ u w +
      q * (2 * q ^ 2 + 3 * q * s + 2 * s ^ 2))
    (hS : s * b = ‖w‖ ^ 2 - 2 * s ^ 3)
    (hc : 0 < c) (hq : 0 < q) (hs : 0 < s) :
    ‖v + c • w‖ ^ 2 / (q + c * s) +
      (2 * q ^ 2 + (3 - 1 / c) * q * s + (1 - 2 * c) * s ^ 2) ≤ a + c * b := by
  have hQ : 0 < q + c * s := add_pos hq (mul_pos hc hs)
  have hpos : 0 < c * s * q := mul_pos (mul_pos hc hs) hq
  have hsq := weighted_gradient_cleared_identity c q s a b u v w hu hB hS hc.ne'
  have hnonneg : 0 ≤ c * s * q * ((q + c * s) * (a + c * b) - ‖v + c • w‖ ^ 2 -
      (q + c * s) * (2 * q ^ 2 + (3 - 1 / c) * q * s + (1 - 2 * c) * s ^ 2)) := by
    rw [hsq]
    exact sq_nonneg _
  have hgap := (mul_nonneg_iff_of_pos_left hpos).mp hnonneg
  rw [← le_sub_iff_add_le, div_le_iff₀ hQ]
  nlinarith only [hgap]

omit [InnerProductSpace ℝ V] in
/-- When the left weight vanishes, a lower bound for its scalar term controls the combination. -/
theorem weighted_gradient_combination_le_zero_left [NormedSpace ℝ V] (c s a b : ℝ) (w : V)
    (hc : 0 < c) (hs : 0 < s) (ha : s ^ 2 ≤ a)
    (hS : s * b = ‖w‖ ^ 2 - 2 * s ^ 3) :
    ‖c • w‖ ^ 2 / (c * s) + (1 - 2 * c) * s ^ 2 ≤ a + c * b := by
  have hnorm : ‖w‖ ^ 2 = s * b + 2 * s ^ 3 := by linarith only [hS]
  rw [← le_sub_iff_add_le, div_le_iff₀ (mul_pos hc hs)]
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hnorm]
  have hnonneg := mul_nonneg (mul_pos hc hs).le (sub_nonneg.mpr ha)
  nlinarith only [hnonneg]

omit [InnerProductSpace ℝ V] in
/-- When the right weight vanishes, a nonnegative scalar term preserves the combination bound. -/
theorem weighted_gradient_combination_le_zero_right (c q a b : ℝ) (v : V)
    (hc : 0 ≤ c) (hq : q ≠ 0)
    (hB : q * a = ‖v‖ ^ 2 + 2 * q ^ 3) (hb : 0 ≤ b) :
    ‖v‖ ^ 2 / q + 2 * q ^ 2 ≤ a + c * b := by
  have hnorm : ‖v‖ ^ 2 = q * a - 2 * q ^ 3 := by linarith only [hB]
  have heq : ‖v‖ ^ 2 / q + 2 * q ^ 2 = a := by
    rw [hnorm]
    field_simp [hq]
    ring
  rw [heq]
  exact le_add_of_nonneg_right (mul_nonneg hc hb)

/-- Nonnegative weights give the same bound when the vanishing cases are controlled separately. -/
theorem weighted_gradient_combination_le_of_nonneg (c q s a b : ℝ) (u v w : V)
    (hu : ‖u‖ ^ 2 = q)
    (hB : q * a = ‖v‖ ^ 2 + 2 * s * inner ℝ u v - 2 * q * inner ℝ u w +
      q * (2 * q ^ 2 + 3 * q * s + 2 * s ^ 2))
    (hS : s * b = ‖w‖ ^ 2 - 2 * s ^ 3)
    (hc : 0 < c) (hs : 0 ≤ s) (hQ : 0 < q + c * s)
    (hqzero : q = 0 → v = 0 ∧ s ^ 2 ≤ a) (hszero : s = 0 → w = 0 ∧ 0 ≤ b) :
    ‖v + c • w‖ ^ 2 / (q + c * s) +
      (2 * q ^ 2 + (3 - 1 / c) * q * s + (1 - 2 * c) * s ^ 2) ≤ a + c * b := by
  have hq : 0 ≤ q := hu ▸ sq_nonneg ‖u‖
  by_cases hq0 : q = 0
  · obtain ⟨hv, ha⟩ := hqzero hq0
    have hspos : 0 < s := by
      have hcs : 0 < c * s := by simpa only [hq0, zero_add] using hQ
      exact (mul_pos_iff_of_pos_left hc).mp hcs
    have hle := weighted_gradient_combination_le_zero_left c s a b w hc hspos ha hS
    simpa only [hq0, hv, zero_add, zero_mul, mul_zero, pow_two, add_zero] using hle
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    by_cases hs0 : s = 0
    · obtain ⟨hw, hb⟩ := hszero hs0
      have hB0 : q * a = ‖v‖ ^ 2 + 2 * q ^ 3 := by
        simp only [hs0, hw, inner_zero_right, zero_mul, mul_zero, sub_zero,
          pow_two, add_zero] at hB
        linear_combination hB
      have hle := weighted_gradient_combination_le_zero_right c q a b v hc.le hqpos.ne' hB0 hb
      simpa only [hs0, hw, smul_zero, add_zero, zero_mul, mul_zero, pow_two] using hle
    · exact weighted_gradient_combination_le c q s a b u v w hu hB hS hc hqpos
        (lt_of_le_of_ne hs (Ne.symm hs0))

/-- The one-third reaction differs from six fifths of the square by a scalar square. -/
theorem weighted_gradient_reaction_one_third_identity (q s : ℝ) :
    2 * q ^ 2 + (1 / 3 : ℝ) * s ^ 2 - (6 / 5 : ℝ) * (q + s / 3) ^ 2 =
      (2 * q - s) ^ 2 / 5 := by
  ring

/-- The one-third reaction bounds six fifths of the combined square, sharply. -/
theorem weighted_gradient_reaction_one_third_le (q s : ℝ) :
    (6 / 5 : ℝ) * (q + s / 3) ^ 2 ≤ 2 * q ^ 2 + (1 / 3 : ℝ) * s ^ 2 := by
  rw [← sub_nonneg, weighted_gradient_reaction_one_third_identity]
  exact div_nonneg (sq_nonneg _) (by norm_num)

end TauCeti
