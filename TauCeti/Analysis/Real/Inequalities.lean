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
  beats `c' - m + δ₀² / (2σ)` with `0 < τ < σ`, then `c' ≤ b + d² / (2τ)` for every `d ≥ δ₀ ≥ 0`.
-/

public section

namespace Real

/-- A quadratic penalty inequality: if `m ≤ b + d² / (2σ)` and the penalty
`δ₀² / (2τ)` already beats `c' - m + δ₀² / (2σ)` with `τ < σ`, then every point at distance
`d ≥ δ₀` satisfies `c' ≤ b + d² / (2τ)`. -/
theorem le_add_sq_div_two_mul_of_sq_div_le {δ₀ d τ σ m b c' : ℝ} (hδ₀ : 0 ≤ δ₀) (hdδ : δ₀ ≤ d)
    (hτ₀ : 0 < τ) (hτσ : τ < σ)
    (hτK : c' - m + δ₀ ^ 2 / (2 * σ) ≤ δ₀ ^ 2 / 2 * τ⁻¹) (h : m ≤ b + d ^ 2 / (2 * σ)) :
    c' ≤ b + d ^ 2 / (2 * τ) := by
  have hσ₀ : 0 < σ := hτ₀.trans hτσ
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

end Real
