/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Curve integrability using the ordinary derivative

The derivative within the unit interval in `curveIntegralFun` agrees almost everywhere with
the ordinary derivative of `Path.extend`. Consequently curve integrability can be checked
using this ordinary derivative, just as the value of the curve integral can be computed with it.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- Curve integrability is equivalent to interval integrability of the ordinary velocity
paired with the 1-form. The endpoint derivative values do not affect integrability. -/
theorem curveIntegrable_iff_intervalIntegrable_deriv {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p q : E}
    (ω : E → E →L[𝕜] F) (γ : Path p q) :
    CurveIntegrable ω γ ↔
      IntervalIntegrable (fun t ↦ ω (γ.extend t) (deriv γ.extend t)) volume 0 1 := by
  apply intervalIntegrable_congr_ae
  rw [Filter.EventuallyEq, uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

end TauCeti
