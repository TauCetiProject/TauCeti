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
* `TauCeti.tendsto_average_add`: Cesàro means of a sum converge to the sum of the limits;
* `TauCeti.tendsto_average_norm_apply_add`, `TauCeti.isClosed_setOf_tendsto_average_norm`: for a
  continuous family `φ x` additive in `x`, the `x` for which the Cesàro means of `‖φ x t‖` tend
  to `0` are closed under addition, and form a closed set when `‖φ x t‖ ≤ C ‖x‖`.
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

section Family

variable {H E : Type*} [NormedAddCommGroup H] [NormedAddCommGroup E] {φ : H → ℝ → E}

/-- For a continuous family `φ` additive in `x`, the `x` for which the Cesàro means of `‖φ x t‖`
tend to `0` are closed under addition. -/
theorem tendsto_average_norm_apply_add (hc : ∀ x, Continuous (φ x))
    (hadd : ∀ x y t, φ (x + y) t = φ x t + φ y t) {x y : H}
    (hx : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖φ x t‖) atTop (𝓝 0))
    (hy : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖φ y t‖) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖φ (x + y) t‖) atTop (𝓝 0) := by
  have hxy := tendsto_average_add (fun T => (hc x).norm.intervalIntegrable 0 T)
    (fun T => (hc y).norm.intervalIntegrable 0 T) hx hy
  rw [add_zero] at hxy
  refine tendsto_average_of_forall_le (fun T => (hc _).norm.intervalIntegrable 0 T)
    (fun _ => norm_nonneg _) fun ε hε => ⟨fun t => ‖φ x t‖ + ‖φ y t‖,
      fun T => ((hc x).norm.add (hc y).norm).intervalIntegrable 0 T, hxy, fun t => ?_⟩
  dsimp only
  rw [hadd]
  linarith [norm_add_le (φ x t) (φ y t)]

/-- For a continuous family `φ` additive in `x` with `‖φ x t‖ ≤ C ‖x‖`, the `x` for which the
Cesàro means of `‖φ x t‖` tend to `0` form a closed set. -/
theorem isClosed_setOf_tendsto_average_norm (hc : ∀ x, Continuous (φ x))
    (hadd : ∀ x y t, φ (x + y) t = φ x t + φ y t) {C : ℝ} (hC : ∀ x t, ‖φ x t‖ ≤ C * ‖x‖) :
    IsClosed {x | Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖φ x t‖) atTop (𝓝 0)} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  refine tendsto_average_of_forall_le (fun T => (hc x).norm.intervalIntegrable 0 T)
    (fun _ => norm_nonneg _) fun ε hε => ?_
  have hC' : 0 < |C| + 1 := by positivity
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / (|C| + 1)) (div_pos hε hC')
  refine ⟨fun t => ‖φ y t‖, fun T => (hc y).norm.intervalIntegrable 0 T, hy, fun t => ?_⟩
  have hsplit : φ x t = φ y t + φ (x - y) t := by
    rw [← hadd, add_sub_cancel]
  have hbound : ‖φ (x - y) t‖ ≤ ε :=
    calc ‖φ (x - y) t‖ ≤ C * dist x y := by
          rw [dist_eq_norm]
          exact hC _ _
      _ ≤ (|C| + 1) * dist x y :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) dist_nonneg
      _ ≤ ε := by
          rw [lt_div_iff₀ hC'] at hxy
          linarith
  dsimp only
  rw [hsplit]
  linarith [norm_add_le (φ y t) (φ (x - y) t)]

end Family

end TauCeti
