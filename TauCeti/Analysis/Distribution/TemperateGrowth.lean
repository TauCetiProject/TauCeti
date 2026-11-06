/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Derivatives of functions of temperate growth

A function of temperate growth is smooth with polynomially bounded derivatives
(`Function.HasTemperateGrowth`). Its derivative, and each of its directional derivatives
`x ↦ f' x v`, then have temperate growth too. These are the multipliers that appear when the
Leibniz rule is applied to multiplication by a function of temperate growth on Schwartz functions
and tempered distributions. A smooth function with bounded derivatives has temperate growth.

## Main results

* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le`: a smooth function whose derivatives
  of every order are bounded has temperate growth.
* `Function.HasTemperateGrowth.fderiv`: the derivative of a function of temperate growth has
  temperate growth.
* `Function.HasTemperateGrowth.fderiv_apply`: so does each directional derivative.
-/

public section

open scoped ContDiff

namespace Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A smooth function whose derivatives of every order are bounded has temperate growth. -/
theorem HasTemperateGrowth.of_norm_iteratedFDeriv_le {f : E → F} (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : f.HasTemperateGrowth := by
  refine ⟨hf, fun n ↦ ?_⟩
  obtain ⟨C, hC⟩ := h n
  exact ⟨0, C, fun x ↦ by simpa using hC x⟩

/-- The derivative of a function of temperate growth has temperate growth. -/
theorem HasTemperateGrowth.fderiv {f : E → F} (hf : f.HasTemperateGrowth) :
    (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right le_rfl, fun n ↦ ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x ↦ by simpa only [norm_iteratedFDeriv_fderiv] using h x⟩

/-- A directional derivative `x ↦ f' x v` of a function of temperate growth has temperate
growth. -/
theorem HasTemperateGrowth.fderiv_apply {f : E → F} (hf : f.HasTemperateGrowth) (v : E) :
    (fun x ↦ _root_.fderiv ℝ f x v).HasTemperateGrowth :=
  ((ContinuousLinearMap.apply ℝ F v).hasTemperateGrowth).comp hf.fderiv

end Function
