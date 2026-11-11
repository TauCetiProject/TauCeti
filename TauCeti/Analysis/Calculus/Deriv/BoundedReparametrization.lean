/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A bounded analytic reparametrization of the real line

For every `ε > 0` there is an analytic function `φ : ℝ → ℝ` with `φ 0 = 0`, `φ'(0) = 1` and
`|φ| ≤ ε` everywhere (`TauCeti.exists_contDiff_hasDerivAt_abs_le`); one choice is
`t ↦ ε sin (t / ε)`.

Composing a line `t ↦ t • v` with `φ` gives a curve with the same velocity at `0` that stays in
the ball of radius `ε ‖v‖`. This turns a direction at a point of an open set, or of a chart
domain, into a curve defined on the whole real line with that velocity.
-/

public section

namespace TauCeti

/-- A bounded analytic reparametrization of the line with unit velocity at `0`: for `ε > 0` there
is an analytic `φ : ℝ → ℝ` with `φ 0 = 0`, `φ'(0) = 1` and `|φ t| ≤ ε` for every `t`. -/
theorem exists_contDiff_hasDerivAt_abs_le {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ ∧ φ 0 = 0 ∧ HasDerivAt φ 1 0 ∧ ∀ t, |φ t| ≤ ε := by
  refine ⟨fun t => ε * Real.sin (t / ε),
    contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ε)), by simp, ?_,
    fun t => ?_⟩
  · have := ((Real.hasDerivAt_sin (0 / ε)).comp 0 ((hasDerivAt_id 0).div_const ε)).const_mul ε
    simpa [hε.ne'] using this
  · rw [abs_mul, abs_of_pos hε]
    exact mul_le_of_le_one_right hε.le (Real.abs_sin_le_one _)

end TauCeti
