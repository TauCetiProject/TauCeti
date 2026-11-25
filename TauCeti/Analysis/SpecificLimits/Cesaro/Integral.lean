/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Continuous-time Cesàro means

Facts about the limits of the Cesàro means `T⁻¹ ∫₀ᵀ φ t dt` of real functions `φ` as `T → ∞`.

## Main results

* `TauCeti.tendsto_average_of_forall_le`: if a nonnegative function is bounded, up to an
  arbitrarily small additive constant, by functions whose Cesàro means tend to `0`, its Cesàro
  means tend to `0`;
* `TauCeti.tendsto_average_add`: Cesàro means of a sum converge to the sum of the limits.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

/-- If a nonnegative function `φ` is bounded, up to an arbitrarily small additive constant, by
functions whose Cesàro means tend to `0`, its Cesàro means tend to `0`. -/
theorem tendsto_average_of_forall_le {φ : ℝ → ℝ} (hφ : ∀ T, IntervalIntegrable φ volume 0 T)
    (h0 : ∀ t, 0 ≤ φ t)
    (h : ∀ ε > 0, ∃ ψ : ℝ → ℝ, (∀ T, IntervalIntegrable ψ volume 0 T) ∧
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t) atTop (𝓝 0) ∧ ∀ t, φ t ≤ ψ t + ε) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, φ t) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ψ, hψi, hψ, hφψ⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.1 hψ (ε / 2) (half_pos hε)
  refine ⟨max T₀ 1, fun T hTmax => ?_⟩
  have hT : 0 < T := lt_of_lt_of_le one_pos (le_of_max_le_right hTmax)
  have hψT := hT₀ T (le_of_max_le_left hTmax)
  rw [Real.dist_eq, sub_zero] at hψT ⊢
  have hint : ∫ t in (0 : ℝ)..T, φ t ≤ ∫ t in (0 : ℝ)..T, (ψ t + ε / 2) :=
    intervalIntegral.integral_mono_on hT.le (hφ T) ((hψi T).add intervalIntegrable_const)
      fun t _ => hφψ t
  rw [intervalIntegral.integral_add (hψi T) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  have hnonneg : 0 ≤ T⁻¹ * ∫ t in (0 : ℝ)..T, φ t :=
    mul_nonneg (inv_nonneg.2 hT.le) (intervalIntegral.integral_nonneg hT.le fun t _ => h0 t)
  rw [abs_of_nonneg hnonneg]
  have hle : T⁻¹ * ∫ t in (0 : ℝ)..T, φ t ≤ (T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t) + ε / 2 := by
    calc T⁻¹ * ∫ t in (0 : ℝ)..T, φ t
        ≤ T⁻¹ * ((∫ t in (0 : ℝ)..T, ψ t) + T * (ε / 2)) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hT.le)
      _ = (T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t) + ε / 2 := by
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul]
  linarith [le_abs_self (T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t)]

/-- If the Cesàro means of `ψ₁` and `ψ₂` tend to `a₁` and `a₂`, those of `ψ₁ + ψ₂` tend to
`a₁ + a₂`. -/
theorem tendsto_average_add {ψ₁ ψ₂ : ℝ → ℝ} {a₁ a₂ : ℝ}
    (h₁i : ∀ T, IntervalIntegrable ψ₁ volume 0 T) (h₂i : ∀ T, IntervalIntegrable ψ₂ volume 0 T)
    (h₁ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ψ₁ t) atTop (𝓝 a₁))
    (h₂ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ψ₂ t) atTop (𝓝 a₂)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, (ψ₁ t + ψ₂ t)) atTop (𝓝 (a₁ + a₂)) := by
  simpa [intervalIntegral.integral_add (h₁i _) (h₂i _), mul_add] using h₁.add h₂

end TauCeti
