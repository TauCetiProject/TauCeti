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

A smooth function whose iterated derivatives are all bounded has temperate growth. Typical examples
are smooth functions which outside a ball agree with a homogeneous function of degree at most `0`.

The derivative `Df` of a function `f` of temperate growth has temperate growth, since the iterated
derivatives of `Df` are those of `f` shifted by one order. So does each directional derivative
`x ↦ Df(x) v`. These are the coefficients that appear when the Leibniz rule is applied to the
product of a Schwartz function or a tempered distribution with `f`.

A measure of temperate growth is finite on compact sets.

## Main results

* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le`: bounded derivatives give temperate
  growth.
* `Function.HasTemperateGrowth.fderiv`: `Df` has temperate growth.
* `Function.HasTemperateGrowth.fderiv_apply`: `x ↦ Df(x) v` has temperate growth.
* `MeasureTheory.Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts`: a measure of temperate
  growth is finite on compact sets.
-/

public section

open scoped ContDiff

namespace Function.HasTemperateGrowth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F}

/-- A smooth function all of whose iterated derivatives are bounded has temperate growth. -/
theorem of_norm_iteratedFDeriv_le (hf : ContDiff ℝ ∞ f)
    (hbd : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : f.HasTemperateGrowth :=
  ⟨hf, fun n ↦ ⟨0, (hbd n).imp fun C hC x ↦ by simpa using hC x⟩⟩

/-- The derivative of a function of temperate growth has temperate growth. -/
theorem fderiv (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right le_rfl, fun n ↦ ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x ↦ by simpa only [norm_iteratedFDeriv_fderiv] using h x⟩

/-- A directional derivative `x ↦ Df(x) v` of a function of temperate growth has temperate
growth. -/
theorem fderiv_apply (hf : f.HasTemperateGrowth) (v : E) :
    (fun x ↦ _root_.fderiv ℝ f x v).HasTemperateGrowth :=
  (ContinuousLinearMap.apply ℝ F v).hasTemperateGrowth.comp hf.fderiv

end Function.HasTemperateGrowth

open MeasureTheory

/-- A measure of temperate growth is finite on compact sets: `(1 + ‖x‖) ^ (-n)` is integrable and
bounded below by a positive constant on any bounded set. -/
theorem MeasureTheory.Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (μ : Measure E)
    [h : μ.HasTemperateGrowth] : IsFiniteMeasureOnCompacts μ := by
  obtain ⟨n, hn⟩ := h.exists_integrable
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  have hε : 0 < (1 + max R 0) ^ (-(n : ℝ)) := by positivity
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hn.measure_norm_ge_lt_top hε)
  have hx' : ‖x‖ ≤ max R 0 := by simpa using (hR hx).trans (le_max_left R 0)
  rw [Set.mem_ofPred_eq, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
