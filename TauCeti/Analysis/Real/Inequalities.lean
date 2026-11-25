/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real inequalities

## Main results

* `Real.le_add_sq_div_two_mul_of_sq_div_le`: if `m ≤ b + d² / (2σ)` and the penalty `δ₀² / (2τ)`
  beats `c' - m + δ₀² / (2σ)` with `0 < τ ≤ σ`, then `c' ≤ b + d² / (2τ)` for every `d ≥ δ₀ ≥ 0`.
* `Real.abs_le_abs_add_of_mem_Icc`: a bound on the absolute value of a point in a centered interval.
-/

public section

namespace Real

/-- A point in a centered interval has absolute value at most the center's absolute value plus
the radius. -/
theorem abs_le_abs_add_of_mem_Icc (a y r : ℝ) (hy : y ∈ Set.Icc (a - r) (a + r)) :
    |y| ≤ |a| + r := by
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le a, hy.1]
  · linarith [le_abs_self a, hy.2]

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

end Real
