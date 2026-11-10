/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Radial vector fields

For a scalar profile `c`, the radial field `y ↦ c (‖y - x₀‖ ^ 2) • (y - x₀)` has Fréchet derivative
`c (‖x - x₀‖ ^ 2) • id + (c' • 2 • innerSL ℝ (x - x₀)).smulRight (x - x₀)`, where `c'` is the
derivative of `c` at `‖x - x₀‖ ^ 2` (`HasDerivAt.hasFDerivAt_smul_sub_norm_sq`). If `c` and its
derivative function `c'` are bounded and vanish beyond the squared radius `R ^ 2`, then the field
and this derivative are bounded in norm (`TauCeti.norm_smul_sub_le_of_eq_zero_of_sq_lt`,
`TauCeti.norm_smul_id_add_smulRight_le_of_eq_zero_of_sq_lt`).
-/

public section

/-- The Fréchet derivative of the radial field `y ↦ c (‖y - x₀‖ ^ 2) • (y - x₀)`, for `c` with
derivative `c'` at `‖x - x₀‖ ^ 2`. -/
theorem _root_.HasDerivAt.hasFDerivAt_smul_sub_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c : ℝ → ℝ} {c' : ℝ} (x₀ x : E)
    (hcd : HasDerivAt c c' (‖x - x₀‖ ^ 2)) :
    HasFDerivAt (fun y => c (‖y - x₀‖ ^ 2) • (y - x₀))
      (c (‖x - x₀‖ ^ 2) • ContinuousLinearMap.id ℝ E +
        (c' • 2 • innerSL ℝ (x - x₀)).smulRight (x - x₀)) x := by
  exact (hcd.comp_hasFDerivAt x (TauCeti.hasFDerivAt_norm_sq_sub x₀ x)).smul
    ((hasFDerivAt_id x).sub_const x₀)

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- Norm bound for a radial vector field `c (‖y - x₀‖ ^ 2) • (y - x₀)` with `c` bounded by `a` and
vanishing beyond the squared radius `R ^ 2`. -/
theorem norm_smul_sub_le_of_eq_zero_of_sq_lt [NormedSpace ℝ E] {c : ℝ → ℝ} {a R : ℝ}
    (hc : ∀ τ, |c τ| ≤ a) (hc0 : ∀ τ, R ^ 2 < τ → c τ = 0) (hR : 0 ≤ R) (x₀ x : E) :
    ‖c (‖x - x₀‖ ^ 2) • (x - x₀)‖ ≤ a * R := by
  rw [norm_smul, Real.norm_eq_abs]
  rcases le_or_gt ‖x - x₀‖ R with hx | hx
  · exact mul_le_mul (hc _) hx (norm_nonneg _) ((abs_nonneg _).trans (hc 0))
  · rw [hc0 _ (pow_lt_pow_left₀ hx hR two_ne_zero), abs_zero, zero_mul]
    exact mul_nonneg ((abs_nonneg _).trans (hc 0)) hR

/-- Norm bound for the operator `c (‖x - x₀‖ ^ 2) • id + (c' (‖x - x₀‖ ^ 2) • 2 • innerSL ℝ
(x - x₀)).smulRight (x - x₀)`, the derivative of a radial vector field, with `c` and `c'` bounded
by `a` and `b` and vanishing beyond the squared radius `R ^ 2`. -/
theorem norm_smul_id_add_smulRight_le_of_eq_zero_of_sq_lt [InnerProductSpace ℝ E]
    {c c' : ℝ → ℝ} {a b R : ℝ} (hc : ∀ τ, |c τ| ≤ a) (hc' : ∀ τ, |c' τ| ≤ b)
    (hc0 : ∀ τ, R ^ 2 < τ → c τ = 0) (hc'0 : ∀ τ, R ^ 2 < τ → c' τ = 0) (hR : 0 ≤ R) (x₀ x : E) :
    ‖c (‖x - x₀‖ ^ 2) • ContinuousLinearMap.id ℝ E +
      (c' (‖x - x₀‖ ^ 2) • 2 • innerSL ℝ (x - x₀)).smulRight (x - x₀)‖ ≤ a + 2 * b * R ^ 2 := by
  have ha := (abs_nonneg _).trans (hc 0)
  have hb := (abs_nonneg _).trans (hc' 0)
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul,
    innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs]
  have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  rcases le_or_gt ‖x - x₀‖ R with hx | hx
  · calc |c (‖x - x₀‖ ^ 2)| * ‖ContinuousLinearMap.id ℝ E‖ +
          |c' (‖x - x₀‖ ^ 2)| * (‖((2 : ℕ) : ℝ)‖ * ‖x - x₀‖) * ‖x - x₀‖
        ≤ a * 1 + b * (2 * R) * R := by
          gcongr
          · exact hc _
          · exact hc' _
          · norm_num
      _ = a + 2 * b * R ^ 2 := by ring
  · have h2 : R ^ 2 < ‖x - x₀‖ ^ 2 := pow_lt_pow_left₀ hx hR two_ne_zero
    rw [hc0 _ h2, hc'0 _ h2, abs_zero, zero_mul, zero_mul, zero_mul, zero_add]
    positivity

end TauCeti
