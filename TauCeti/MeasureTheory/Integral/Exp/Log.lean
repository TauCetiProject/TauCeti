/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Monotonicity of the log-integral-exponential functional

For a nonzero measure `ν` and a real-valued function `f` such that `exp ∘ f` is integrable, the
log-partition function `f ↦ log ∫ exp (f x) ∂ν` is monotone and shifts additively under constants:
if `f₁ ≤ f₂ + δ` almost everywhere, then `log ∫ exp (f₁ x) ∂ν ≤ log ∫ exp (f₂ x) ∂ν + δ`.

Scaling by a positive temperature `ε > 0` gives the corresponding softmin / soft-maximum bound
`ε * log ∫ exp (g₁ x / ε) ∂ν ≤ ε * log ∫ exp (g₂ x / ε) ∂ν + δ` whenever `g₁ ≤ g₂ + δ` almost
everywhere, which is used to establish uniform bounds and Lipschitz regularity of Schrödinger
potentials in entropic optimal transport.

## Main results

* `TauCeti.log_integral_exp_le_add_of_ae_le`: `log ∫ exp f₁ dν ≤ log ∫ exp f₂ dν + δ` whenever
  `f₁ ≤ f₂ + δ` almost everywhere against a nonzero measure `ν`.
* `TauCeti.mul_log_integral_exp_div_le_add_of_ae_le`: temperature-scaled form
  `ε * log ∫ exp (g₁ / ε) dν ≤ ε * log ∫ exp (g₂ / ε) dν + δ` for `ε > 0`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- If `f₁ ≤ f₂ + δ` almost everywhere against a nonzero measure `ν` and both `exp ∘ f₁` and
`exp ∘ f₂` are integrable, then `log ∫ exp f₁ dν ≤ log ∫ exp f₂ dν + δ`. -/
theorem log_integral_exp_le_add_of_ae_le [NeZero ν] {f₁ f₂ : α → ℝ} {δ : ℝ}
    (hf₁ : Integrable (fun x ↦ Real.exp (f₁ x)) ν)
    (hf₂ : Integrable (fun x ↦ Real.exp (f₂ x)) ν) (hle : ∀ᵐ x ∂ν, f₁ x ≤ f₂ x + δ) :
    Real.log (∫ x, Real.exp (f₁ x) ∂ν) ≤ Real.log (∫ x, Real.exp (f₂ x) ∂ν) + δ := by
  have hZ₁ : 0 < ∫ x, Real.exp (f₁ x) ∂ν := integral_exp_pos hf₁
  have hZ₂ : 0 < ∫ x, Real.exp (f₂ x) ∂ν := integral_exp_pos hf₂
  have hint_le : ∫ x, Real.exp (f₁ x) ∂ν ≤ Real.exp δ * ∫ x, Real.exp (f₂ x) ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae hf₁ (hf₂.const_mul _) ?_
    filter_upwards [hle] with x hx
    rw [← Real.exp_add, Real.exp_le_exp]
    exact hx.trans_eq (add_comm _ _)
  have hlog := Real.log_le_log hZ₁ hint_le
  rw [Real.log_mul (Real.exp_pos _).ne' hZ₂.ne', Real.log_exp, add_comm] at hlog
  exact hlog

/-- Temperature-scaled monotonicity of the log-integral-exponential functional: for `ε > 0`, if
`g₁ ≤ g₂ + δ` almost everywhere against a nonzero measure `ν` and both `exp (g₁ / ε)` and
`exp (g₂ / ε)` are integrable, then
`ε * log ∫ exp (g₁ / ε) dν ≤ ε * log ∫ exp (g₂ / ε) dν + δ`. -/
theorem mul_log_integral_exp_div_le_add_of_ae_le [NeZero ν] {ε : ℝ} (hε : 0 < ε)
    {g₁ g₂ : α → ℝ} {δ : ℝ} (hg₁ : Integrable (fun x ↦ Real.exp (g₁ x / ε)) ν)
    (hg₂ : Integrable (fun x ↦ Real.exp (g₂ x / ε)) ν) (hle : ∀ᵐ x ∂ν, g₁ x ≤ g₂ x + δ) :
    ε * Real.log (∫ x, Real.exp (g₁ x / ε) ∂ν) ≤
      ε * Real.log (∫ x, Real.exp (g₂ x / ε) ∂ν) + δ := by
  have hlog := log_integral_exp_le_add_of_ae_le hg₁ hg₂ (δ := δ / ε) <| by
    filter_upwards [hle] with x hx
    rw [← add_div]
    exact div_le_div_of_nonneg_right hx hε.le
  calc ε * Real.log (∫ x, Real.exp (g₁ x / ε) ∂ν)
      ≤ ε * (Real.log (∫ x, Real.exp (g₂ x / ε) ∂ν) + δ / ε) :=
        mul_le_mul_of_nonneg_left hlog hε.le
    _ = ε * Real.log (∫ x, Real.exp (g₂ x / ε) ∂ν) + δ := by
        rw [mul_add, mul_div_cancel₀ _ hε.ne']

end TauCeti
