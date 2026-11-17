/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# A Lipschitz estimate for the radial map onto the unit ball

Mathlib's `OpenPartialHomeomorph.univUnitBall` sends a vector `x` of a real seminormed space to
`(√(1 + ‖x‖²))⁻¹ • x`, a point of the open unit ball. This file proves that it is Lipschitz with a
constant that improves far from the origin:

`‖univUnitBall x - univUnitBall y‖ ≤ 2 ‖x - y‖ / √(1 + ‖x‖²)`

(`OpenPartialHomeomorph.norm_univUnitBall_sub_le`). The gain `1 / √(1 + ‖x‖²)` is what makes the
map useful for comparing functions with polynomial growth: if `‖f - g‖ ≤ δ (1 + ‖g‖)` everywhere,
then `univUnitBall ∘ f` and `univUnitBall ∘ g` are uniformly within `4 δ`
(`OpenPartialHomeomorph.norm_univUnitBall_sub_le_of_norm_sub_le`). The estimate rests on
the fact that `t ↦ √(1 + t²)` is `1`-Lipschitz on the real line
(`TauCeti.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le`).

For `f` a complex polynomial, `univUnitBall ∘ f` is the section `exp(u₀) f` of the background
amplitude `u₀ = -log (1 + ‖f‖²) / 2` used to construct plane vortices with prescribed zeros.
-/

public section

open Metric

namespace TauCeti

/-- The function `t ↦ √(1 + t²)` is `1`-Lipschitz on the real line. -/
theorem abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le (a b : ℝ) :
    |√(1 + a ^ 2) - √(1 + b ^ 2)| ≤ |a - b| := by
  have hA := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + a ^ 2)
  have hB := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + b ^ 2)
  have hA0 := Real.sqrt_nonneg (1 + a ^ 2)
  have hB0 := Real.sqrt_nonneg (1 + b ^ 2)
  -- `|√(1 + a²)| ≥ |a|` and `|√(1 + b²)| ≥ |b|`, so the sum of the roots dominates `|a + b|`.
  have ha : |a| ≤ √(1 + a ^ 2) := Real.abs_le_sqrt (by nlinarith)
  have hb : |b| ≤ √(1 + b ^ 2) := Real.abs_le_sqrt (by nlinarith)
  have hab : |a + b| ≤ √(1 + a ^ 2) + √(1 + b ^ 2) := (abs_add_le a b).trans (add_le_add ha hb)
  -- `(√(1 + a²) - √(1 + b²)) (√(1 + a²) + √(1 + b²)) = (a - b) (a + b)`.
  have hprod : |√(1 + a ^ 2) - √(1 + b ^ 2)| * (√(1 + a ^ 2) + √(1 + b ^ 2)) =
      |a - b| * |a + b| := by
    rw [← abs_of_nonneg (add_nonneg hA0 hB0), ← abs_mul, ← abs_mul]
    congr 1
    linear_combination hA - hB
  rcases (add_nonneg hA0 hB0).eq_or_lt with h | h
  · nlinarith [Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + a ^ 2)]
  · refine le_of_mul_le_mul_right ?_ h
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hab (abs_nonneg _)

end TauCeti

namespace OpenPartialHomeomorph

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- `univUnitBall` takes values in the closed unit ball. -/
theorem norm_univUnitBall_le (x : E) : ‖univUnitBall x‖ ≤ 1 :=
  (mem_ball_zero_iff.1 (univUnitBall.map_source (Set.mem_univ x))).le

/-- **A Lipschitz estimate for `univUnitBall`.** The radial map
`x ↦ (√(1 + ‖x‖²))⁻¹ • x` onto the open unit ball satisfies
`‖univUnitBall x - univUnitBall y‖ ≤ 2 ‖x - y‖ / √(1 + ‖x‖²)`. -/
theorem norm_univUnitBall_sub_le (x y : E) :
    ‖univUnitBall x - univUnitBall y‖ ≤ 2 * ‖x - y‖ / √(1 + ‖x‖ ^ 2) := by
  set A := √(1 + ‖x‖ ^ 2)
  set B := √(1 + ‖y‖ ^ 2)
  have hA : 0 < A := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < B := Real.sqrt_pos.2 (by positivity)
  have hyB : ‖y‖ ≤ B := Real.le_sqrt_of_sq_le (by linarith)
  -- `|B - A| ≤ |‖y‖ - ‖x‖| ≤ ‖x - y‖`.
  have hBA : |B - A| ≤ ‖x - y‖ :=
    (TauCeti.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le _ _).trans
      (by rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y)
  have hsplit : univUnitBall x - univUnitBall y = A⁻¹ • (x - y) + (A⁻¹ - B⁻¹) • y := by
    simp only [univUnitBall_apply, A, B]
    module
  have hcoef : |A⁻¹ - B⁻¹| * ‖y‖ ≤ ‖x - y‖ / A := by
    rw [inv_sub_inv hA.ne' hB.ne', abs_div, abs_of_pos (mul_pos hA hB), div_mul_eq_mul_div,
      div_le_div_iff₀ (mul_pos hA hB) hA]
    have := mul_le_mul hBA hyB (norm_nonneg y) (norm_nonneg _)
    nlinarith [abs_nonneg (B - A)]
  rw [hsplit]
  calc ‖A⁻¹ • (x - y) + (A⁻¹ - B⁻¹) • y‖ ≤ ‖A⁻¹ • (x - y)‖ + ‖(A⁻¹ - B⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x - y‖ / A + |A⁻¹ - B⁻¹| * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hA,
        inv_mul_eq_div]
    _ ≤ ‖x - y‖ / A + ‖x - y‖ / A := add_le_add le_rfl hcoef
    _ = 2 * ‖x - y‖ / A := by ring

/-- **Uniform closeness under `univUnitBall`.** If `‖x - y‖ ≤ δ (1 + ‖y‖)`, then
`‖univUnitBall x - univUnitBall y‖ ≤ 4 δ`: an error that grows at most like `y` becomes uniformly
small after the radial map onto the unit ball. -/
theorem norm_univUnitBall_sub_le_of_norm_sub_le {x y : E} {δ : ℝ}
    (h : ‖x - y‖ ≤ δ * (1 + ‖y‖)) : ‖univUnitBall x - univUnitBall y‖ ≤ 4 * δ := by
  have hB : 0 < √(1 + ‖y‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hδ : 0 ≤ δ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (by positivity)
  rw [norm_sub_rev]
  refine (norm_univUnitBall_sub_le y x).trans ?_
  have hy : (1 + ‖y‖) / 2 ≤ √(1 + ‖y‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (‖y‖ - 1)])
  rw [div_le_iff₀ hB, norm_sub_rev]
  nlinarith

end OpenPartialHomeomorph
