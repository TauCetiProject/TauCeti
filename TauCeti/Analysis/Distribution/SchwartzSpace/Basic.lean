/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Weighted integrability of Schwartz functions

A Schwartz function is bounded and decays faster than any power, so `‖x‖ ^ k ‖f x‖²` is
integrable against any measure of temperate growth. This is the integrability input for weighted
`L²` estimates such as the weighted Plancherel identity.

## Main declarations

* `SchwartzMap.integrable_norm_pow_mul_norm_sq`: `‖x‖ ^ k ‖f x‖²` is integrable.
* `SchwartzMap.integrable_inner`: the pointwise inner product of two Schwartz functions is
  integrable.
* `SchwartzMap.integral_norm_sq_eq_zero_iff`: a Schwartz function vanishes exactly when the
  integral of its squared norm does, for a measure charging every nonempty open set.
-/

public section

open MeasureTheory

namespace SchwartzMap

open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.HasTemperateGrowth]

/-- For a Schwartz function `f`, the function `‖x‖ ^ k ‖f x‖²` is integrable. -/
theorem integrable_norm_pow_mul_norm_sq (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖ ^ 2) μ := by
  refine ((f.integrable_pow_mul μ k).const_mul (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    (by fun_prop) (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), sq, ← mul_assoc, mul_comm _ ‖f x‖]
  gcongr
  exact f.norm_le_seminorm ℝ x

/-- A Schwartz function vanishes if and only if the integral of its squared norm does, against a
measure of temperate growth that charges every nonempty open set. -/
theorem integral_norm_sq_eq_zero_iff [μ.IsOpenPosMeasure] {f : 𝓢(E, F)} :
    ∫ x, ‖f x‖ ^ 2 ∂μ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    simpa using f.integrable_norm_pow_mul_norm_sq (μ := μ) 0
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖) hint).mp h
  have hcont : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have := (hcont.ae_eq_iff_eq μ continuous_zero).mp hae
  exact SchwartzMap.ext fun x => by simpa using congrFun this x

open scoped RealInnerProductSpace in
/-- The pointwise inner product of two Schwartz functions is integrable. -/
theorem integrable_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f g : 𝓢(E, F)) : Integrable (fun x => ⟪f x, g x⟫) μ :=
  -- The pairing of `f` and `g` under `innerSL ℝ` is the Schwartz function `x ↦ ⟪f x, g x⟫`.
  (pairing (innerSL ℝ) f g).integrable

end SchwartzMap
