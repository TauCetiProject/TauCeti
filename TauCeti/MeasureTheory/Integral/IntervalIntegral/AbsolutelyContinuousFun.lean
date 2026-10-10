/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The chain rule for absolutely continuous curves

Mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` is the fundamental theorem of
calculus for an absolutely continuous real function. This file composes it with a `C¹` function:
if `γ : ℝ → F` is an absolutely continuous curve in a normed space with derivative `V t` at almost
every time and `φ : F → ℝ` is `C¹`, then `∫_a^b φ'(γ t) (V t) dt = φ (γ b) - φ (γ a)`.

## Main results

* `AbsolutelyContinuousOnInterval.integral_fderiv_apply_eq_sub`: the fundamental theorem of
  calculus for the composition of a `C¹` function with an absolutely continuous curve.
-/

public section

open Set

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {γ V : ℝ → F} {a b : ℝ}

/-- *Fundamental theorem of calculus* along an absolutely continuous curve: if `γ` is absolutely
continuous on `uIcc a b` with derivative `V t` at almost every `t ∈ uIoc a b` and `φ` is `C¹`, then
`∫ t in a..b, fderiv ℝ φ (γ t) (V t) = φ (γ b) - φ (γ a)`. The composition `φ ∘ γ` is absolutely
continuous because `φ` is Lipschitz on the compact image `γ '' uIcc a b`. -/
theorem integral_fderiv_apply_eq_sub (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) {φ : F → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ t in a..b, fderiv ℝ φ (γ t) (V t) = φ (γ b) - φ (γ a) := by
  obtain ⟨K, hK⟩ := hφ.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn)
  refine Eq.trans (intervalIntegral.integral_congr_ae ?_)
    (hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ).integral_deriv_eq_sub
  filter_upwards [hV] with t ht hmem
  exact (HasFDerivAt.comp_hasDerivAt t (hφ.differentiable one_ne_zero (γ t)).hasFDerivAt
    (ht hmem)).deriv.symm

end AbsolutelyContinuousOnInterval
