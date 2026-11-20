/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Inequalities between quadratic penalties over `ℝ`

## Main results

* `Real.le_add_sq_div_two_mul_of_sq_div_le`: if `m ≤ b + d² / (2σ)` and the penalty `δ₀² / (2τ)`
  beats `c' - m + δ₀² / (2σ)` with `0 < τ ≤ σ`, then `c' ≤ b + d² / (2τ)` for every `d ≥ δ₀ ≥ 0`.
* `Real.abs_le_max_of_mul_sq_sub_mul_lt`: for `a > 0`, the solutions of `a x² - b x < c` satisfy
  `|x| ≤ max 1 ((|b| + |c|) / a)`.
-/

public section

namespace Real

/-- A quadratic penalty inequality: if `m ≤ b + d² / (2σ)` and the penalty
`δ₀² / (2τ)` already beats `c' - m + δ₀² / (2σ)` with `τ ≤ σ`, then every point at distance
`d ≥ δ₀` satisfies `c' ≤ b + d² / (2τ)`. -/
theorem le_add_sq_div_two_mul_of_sq_div_le {δ₀ d τ σ m b c' : ℝ} (hδ₀ : 0 ≤ δ₀) (hdδ : δ₀ ≤ d)
    (hτ₀ : 0 < τ) (hτσ : τ ≤ σ)
    (hτK : c' - m + δ₀ ^ 2 / (2 * σ) ≤ δ₀ ^ 2 / 2 * τ⁻¹) (h : m ≤ b + d ^ 2 / (2 * σ)) :
    c' ≤ b + d ^ 2 / (2 * τ) := by
  have hw : 0 ≤ 1 / (2 * τ) - 1 / (2 * σ) := by
    rw [sub_nonneg]
    gcongr
  have hsq : δ₀ ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hδ₀ hdδ 2
  have key : δ₀ ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) ≤ d ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) :=
    mul_le_mul_of_nonneg_right hsq hw
  have e₁ : δ₀ ^ 2 / 2 * τ⁻¹ = δ₀ ^ 2 / (2 * τ) := by field_simp
  have e₂ : d ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) = d ^ 2 / (2 * τ) - d ^ 2 / (2 * σ) := by ring
  have e₃ : δ₀ ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) = δ₀ ^ 2 / (2 * τ) - δ₀ ^ 2 / (2 * σ) := by
    ring
  linarith

/-- **The sublevel sets of an upward parabola are bounded.** For `a > 0`, every solution of
`a x² - b x < c` satisfies `|x| ≤ max 1 ((|b| + |c|) / a)`. -/
theorem abs_le_max_of_mul_sq_sub_mul_lt {a b c x : ℝ} (ha : 0 < a) (h : a * x ^ 2 - b * x < c) :
    |x| ≤ max 1 ((|b| + |c|) / a) := by
  rcases le_or_gt |x| 1 with hx | hx
  · exact le_max_of_le_left hx
  -- For `|x| > 1`, `a |x|² < |b| |x| + |c| ≤ (|b| + |c|) |x|`.
  refine le_max_of_le_right ((le_div_iff₀ ha).2 ?_)
  have hbx : b * x ≤ |b| * |x| := by rw [← abs_mul]; exact le_abs_self _
  have hc : c ≤ |c| * |x| := (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) hx.le)
  have hsq : x ^ 2 = |x| * |x| := by rw [← sq_abs, sq]
  nlinarith

end Real
