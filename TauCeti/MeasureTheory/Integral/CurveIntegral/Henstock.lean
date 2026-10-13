/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.Oriented.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Agreement of Henstock and Bochner curve integrals

Mathlib's `CurveIntegrable` supplies genuine Bochner integrability of `curveIntegralFun`.
Its Henstock integral therefore has the same value as Mathlib's `curveIntegral`, by the
oriented interval compatibility theorem. The comparison retains the integrability hypothesis.
-/

public section

open MeasureTheory

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {a b : E} {ω : E → E →L[𝕜] F} {γ : Path a b}

/-- A Bochner-integrable one-form along a path has its actual curve-integral value as a
Henstock integral of Mathlib's curve integrand on the unit parameter interval. -/
theorem CurveIntegrable.hasHenstockIntervalIntegral (h : CurveIntegrable ω γ) :
    let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral (curveIntegralFun ω γ) 0 1
      (curveIntegral ω γ) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def]
  exact IntervalIntegrable.hasHenstockIntervalIntegral h

/-- Under genuine curve integrability, any Henstock value of Mathlib's curve integrand
agrees with its Bochner curve integral. -/
theorem TauCeti.BoxIntegral.HasHenstockIntervalIntegral.eq_curveIntegral {y : F}
    (h : letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
      TauCeti.BoxIntegral.HasHenstockIntervalIntegral (curveIntegralFun ω γ) 0 1 y)
    (hω : CurveIntegrable ω γ) : y = curveIntegral ω γ := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  exact h.unique hω.hasHenstockIntervalIntegral
