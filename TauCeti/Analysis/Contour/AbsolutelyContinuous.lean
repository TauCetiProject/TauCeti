/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolute continuity of curves from an integrable logarithmic derivative

For a continuous complex curve differentiable outside a countable set, integrability of an
off-curve logarithmic derivative suffices for absolute continuity. Piecewise `C¹` curves are
absolutely continuous by `TauCeti.IsPiecewiseC1On.absolutelyContinuousOnInterval`.
-/

public section

namespace TauCeti.Contour

open MeasureTheory Set

variable {a b : ℝ} {γ : ℝ → ℂ}

/-- A continuous complex curve differentiable off a countable set is absolutely continuous
if its logarithmic derivative about an avoided point is interval integrable. -/
theorem _root_.ContinuousOn.absolutelyContinuousOnInterval_of_intervalIntegrable_inv_sub_mul_deriv
    {w : ℂ} {P : Set ℝ} (hγ : ContinuousOn γ (uIcc a b)) (hP : P.Countable)
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (havoid : ∀ t ∈ uIcc a b, γ t ≠ w)
    (hi : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    AbsolutelyContinuousOnInterval γ a b := by
  have hderiv : IntervalIntegrable (deriv γ) volume a b := by
    refine (hi.continuousOn_mul (hγ.sub (continuousOn_const (c := w)))).congr (fun t ht ↦ ?_)
    dsimp
    rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (havoid t (uIoc_subset_uIcc ht))), one_mul]
  exact hγ.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
    (fun t ht ↦ (hd t ht).hasDerivAt) hderiv

end TauCeti.Contour
