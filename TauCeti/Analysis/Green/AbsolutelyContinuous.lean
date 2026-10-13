/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Basic
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Circulation along absolutely continuous curves

Continuous planar fields have integrable circulation along an absolutely continuous curve.
The orientation is that of the existing `intervalIntegral`.

These results supply boundary integrability for Green's theorem along absolutely continuous curves.
-/

public section

open MeasureTheory Set

namespace TauCeti.Green

/-- A continuous planar field has interval-integrable circulation along an absolutely
continuous curve. -/
theorem _root_.AbsolutelyContinuousOnInterval.intervalIntegrable_circulationFun
    {γ : ℝ → ℂ} {a b : ℝ} {P Q : ℂ → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hP : ContinuousOn P (γ '' uIcc a b)) (hQ : ContinuousOn Q (γ '' uIcc a b)) :
    IntervalIntegrable (circulationFun P Q γ) volume a b := by
  have hd := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hr : IntervalIntegrable (fun t ↦ (deriv γ t).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hd.1, Complex.reCLM.integrable_comp hd.2⟩
  have hi : IntervalIntegrable (fun t ↦ (deriv γ t).im) volume a b :=
    ⟨Complex.imCLM.integrable_comp hd.1, Complex.imCLM.integrable_comp hd.2⟩
  have hPc := hP.comp hγ.continuousOn (mapsTo_image _ _)
  have hQc := hQ.comp hγ.continuousOn (mapsTo_image _ _)
  change IntervalIntegrable
    (fun t ↦ P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) volume a b
  simpa only [Function.comp_apply] using
    (hr.continuousOn_mul hPc).add (hi.continuousOn_mul hQc)

/-- A continuous planar 1-form is curve integrable along a path whose extension is absolutely
continuous on `[0, 1]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.curveIntegrable_oneForm
    {p q : ℂ} {γ : Path p q} {P Q : ℂ → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ.extend 0 1)
    (hP : ContinuousOn P (γ.extend '' Icc 0 1))
    (hQ : ContinuousOn Q (γ.extend '' Icc 0 1)) :
    CurveIntegrable (oneForm P Q) γ := by
  rw [curveIntegrable_iff_intervalIntegrable_deriv]
  simpa only [← circulationFun_eq_oneForm] using
    hγ.intervalIntegrable_circulationFun (by simpa using hP) (by simpa using hQ)

end TauCeti.Green
