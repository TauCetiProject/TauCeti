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

## Main results

* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le`: bounded derivatives give temperate
  growth.
* `Function.HasTemperateGrowth.fderiv`: `Df` has temperate growth.
* `Function.HasTemperateGrowth.fderiv_apply`: `x ↦ Df(x) v` has temperate growth.
* `Function.HasTemperateGrowth.norm_sq`: `x ↦ ‖f x‖ ^ 2` has temperate growth for `f` of
  temperate growth with values in a real inner product space, so that `fun_prop` handles
  multipliers such as `y ↦ (-‖x - y‖ ^ 2) ^ N`.
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

/-- The squared norm of a function of temperate growth with values in a real inner product space
has temperate growth. -/
@[fun_prop]
theorem norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {g : E → H}
    (hg : g.HasTemperateGrowth) : (fun x ↦ ‖g x‖ ^ 2).HasTemperateGrowth :=
  (hasTemperateGrowth_norm_sq H).comp hg

end Function.HasTemperateGrowth
