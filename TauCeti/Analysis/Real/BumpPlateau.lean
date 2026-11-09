/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A continuous bump with a plateau on its support

For `l : ℝ` and `δ > 0` there are continuous functions `k` and `h` on `ℝ` with `k l = 1`, `h`
equal to one on the support of `k`, and `|x h(x)| ≤ |l| + 2δ` for all `x`. Concretely `k` is the
tent `max 0 (1 - |x - l| / δ)`, supported in `[l - δ, l + δ]`, and `h` is the trapezoid
`max 0 (min 1 (2 - |x - l| / δ))`, equal to one on `[l - δ, l + δ]`, supported in
`[l - 2δ, l + 2δ]` and bounded by one.

Applied through the continuous functional calculus, `k` localises an operator near a spectral
value `l`, and `x ↦ x h(x)` is a function of norm at most `|l| + 2δ` that agrees with `x ↦ x` on
the support of `k`. This is the real-variable input of the spectral gap of a self-adjoint operator
with closed range.
-/

public section

namespace Real

/-- A continuous bump `k` at `l` with `k l = 1` and a continuous plateau `h` equal to one on the
support of `k`, such that `|x h(x)| ≤ |l| + 2δ` everywhere. -/
theorem exists_bump_plateau (l : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k h : ℝ → ℝ, Continuous k ∧ Continuous h ∧ k l = 1 ∧ (∀ x, h x * k x = k x) ∧
      ∀ x, ‖x * h x‖ ≤ |l| + 2 * δ := by
  refine ⟨fun x ↦ max 0 (1 - |x - l| / δ), fun x ↦ max 0 (min 1 (2 - |x - l| / δ)),
    by fun_prop, by fun_prop, by simp, fun x ↦ ?_, fun x ↦ ?_⟩
  · rcases le_or_gt δ |x - l| with hx | hx
    · have : 1 - |x - l| / δ ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hδ]; linarith
      simp [max_eq_left this]
    · have : 1 ≤ 2 - |x - l| / δ := by rw [le_sub_comm, div_le_iff₀ hδ]; linarith
      simp [min_eq_left this]
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_or_gt (2 * δ) |x - l| with hx | hx
    · have : 2 - |x - l| / δ ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hδ]; linarith
      simp only [min_eq_right (this.trans zero_le_one), max_eq_left this, abs_zero, mul_zero]
      positivity
    · have h0 : 0 ≤ max 0 (min 1 (2 - |x - l| / δ)) := le_max_left _ _
      have h1 : max 0 (min 1 (2 - |x - l| / δ)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hx' : |x| ≤ |l| + 2 * δ := by have := abs_sub_abs_le_abs_sub x l; linarith
      rw [abs_of_nonneg h0]
      nlinarith [abs_nonneg x]

end Real
