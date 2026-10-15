/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The winding integral for absolutely continuous curves

Off the compact trace of an absolutely continuous curve, the existing generalized winding
number is its ordinary winding integral, and the winding integrand is interval integrable.

These results extend the contour index API beyond piecewise `C¹` curves.
-/

public section

open MeasureTheory Set

namespace TauCeti.Contour

/-- The off-curve winding integrand of an absolutely continuous curve is interval integrable. -/
theorem _root_.AbsolutelyContinuousOnInterval.intervalIntegrable_inv_sub_mul_deriv
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hz : z ∉ γ '' uIcc a b) :
    IntervalIntegrable (fun t ↦ (γ t - z)⁻¹ * deriv γ t) volume a b := by
  exact TauCeti.Contour.intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn
    (fun t ht htz ↦ hz ⟨t, ht, htz⟩) hγ.intervalIntegrable_deriv_of_finiteDimensional

/-- The existing winding number agrees with the ordinary winding integral for an absolutely
continuous curve away from its trace, in either orientation of the parameter interval. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_integral
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hz : z ∉ γ '' uIcc a b) :
    windingNumber γ a b z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ t in a..b, (γ t - z)⁻¹ * deriv γ t :=
  windingNumber_eq_integral_of_avoidance hγ.continuousOn
    (fun t ht htz ↦ hz ⟨t, ht, htz⟩)
    (hγ.intervalIntegrable_inv_sub_mul_deriv hz)

end TauCeti.Contour
