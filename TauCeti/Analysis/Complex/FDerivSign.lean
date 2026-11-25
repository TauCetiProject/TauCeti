/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Complex.OperatorNorm

/-!
# The sign of a derivative across a horizontal line in `ℂ`

Let `F : ℂ → ℝ` vanish near `x₀` on the horizontal line through `x₀`. Then its derivative at `x₀`
vanishes on `1` (`TauCeti.Complex.fderiv_apply_one_eq_zero`). If moreover `F` is positive near `x₀`
above that line and its derivative at `x₀` is nonzero, then the derivative is positive on `I`
(`TauCeti.Complex.fderiv_apply_I_pos`): it is nonnegative on `I` by the one-sided slope, and a
real-linear form vanishing on `1` and nonzero somewhere does not vanish on `I`. This is the sign
test for a defining function of a curve read in a chart where the curve is horizontal.

## Main results

* `TauCeti.Complex.fderiv_apply_one_eq_zero`: the tangential part of the derivative vanishes.
* `TauCeti.Complex.fderiv_apply_I_pos`: the normal part has the sign of the function above the
  line.
-/

public section

open Filter Topology Complex

namespace TauCeti.Complex

variable {F : ℂ → ℝ} {x₀ : ℂ}

/-- A function `F : ℂ → ℝ` vanishing near `x₀` on the horizontal line through `x₀` has derivative
zero on `1` at `x₀`. -/
theorem fderiv_apply_one_eq_zero (hreal : ∀ᶠ w in 𝓝 x₀, w.im = x₀.im → F w = 0) :
    fderiv ℝ F x₀ 1 = 0 := by
  by_cases hd : DifferentiableAt ℝ F x₀
  · have hγ : HasDerivAt (fun t : ℝ ↦ x₀ + t) 1 0 := by
      simpa only [ofRealCLM_apply, ofReal_one] using
        (ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add x₀
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
    have hev : (F ∘ fun t : ℝ ↦ x₀ + t) =ᶠ[𝓝 0] fun _ ↦ 0 := by
      have ht : Tendsto (fun t : ℝ ↦ x₀ + t) (𝓝 0) (𝓝 x₀) := by
        simpa using hγ.continuousAt.tendsto
      filter_upwards [ht.eventually hreal] with t ht
      exact ht (by simp)
    exact h.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)
  · rw [fderiv_zero_of_not_differentiableAt hd, zero_apply]

/-- **The sign test across a horizontal line.** Let `F : ℂ → ℝ` have nonzero derivative at `x₀`,
vanish near `x₀` on the horizontal line through `x₀`, and be positive near `x₀` above it. Then its
derivative at `x₀` is positive on `I`. -/
theorem fderiv_apply_I_pos {v : ℂ} (hne : fderiv ℝ F x₀ v ≠ 0)
    (hreal : ∀ᶠ w in 𝓝 x₀, w.im = x₀.im → F w = 0)
    (hpos : ∀ᶠ w in 𝓝 x₀, x₀.im < w.im → 0 < F w) :
    0 < fderiv ℝ F x₀ I := by
  have hd : DifferentiableAt ℝ F x₀ := by
    by_contra hnd
    exact hne (by rw [fderiv_zero_of_not_differentiableAt hnd, zero_apply])
  have hF0 : F x₀ = 0 := hreal.self_of_nhds rfl
  -- Along `I` the function is positive for positive times, so its derivative on `I` is `≥ 0`.
  have hI : 0 ≤ fderiv ℝ F x₀ I := by
    have hγ : HasDerivAt (fun t : ℝ ↦ x₀ + t * I) I 0 := by
      simpa only [ofRealCLM_apply, ofReal_one, one_mul] using
        ((ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).const_add x₀
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
    have ht : Tendsto (fun t : ℝ ↦ x₀ + t * I) (𝓝 0) (𝓝 x₀) := by
      simpa using hγ.continuousAt.tendsto
    refine ge_of_tendsto h.tendsto_slope_zero_right ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ht.eventually hpos)] with t ht0 ht
    have hFt := ht (by simpa using ht0)
    simp only [zero_add, Function.comp_apply, ofReal_zero, zero_mul, add_zero, hF0, sub_zero,
      smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 (le_of_lt ht0)) hFt.le
  exact lt_of_le_of_ne hI (ContinuousLinearMap.apply_I_ne_zero_of_apply_one_eq_zero
    (fderiv_apply_one_eq_zero hreal) hne).symm

end TauCeti.Complex
