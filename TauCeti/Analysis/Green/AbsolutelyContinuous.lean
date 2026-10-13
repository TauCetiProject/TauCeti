/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Basic
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Circulation along absolutely continuous curves

Continuous planar fields have integrable circulation along an absolutely continuous curve.
Absolute continuity, rather than a countable exceptional set of differentiability, supplies
the integrable velocity. The orientation is that of the existing `intervalIntegral`.

These results supply boundary integrability for Green's theorem along absolutely continuous curves.
-/

public section

open MeasureTheory Set

namespace TauCeti.Green

/-- A continuous planar field has interval-integrable circulation along an absolutely
continuous curve. Boundary integrability follows from these hypotheses. -/
theorem circulationFun_intervalIntegrable {γ : ℝ → ℂ} {a b : ℝ} {P Q : ℂ → ℝ}
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
  simpa only [Function.comp_apply, ← circulationFun_def] using
    (hr.continuousOn_mul hPc).add (hi.continuousOn_mul hQc)

/-- A continuous planar 1-form is curve integrable along a path whose extension is absolutely
continuous on `[0, 1]`. -/
theorem curveIntegrable_oneForm {p q : ℂ} {γ : Path p q} {P Q : ℂ → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ.extend 0 1)
    (hP : ContinuousOn P (γ.extend '' Icc 0 1))
    (hQ : ContinuousOn Q (γ.extend '' Icc 0 1)) :
    CurveIntegrable (oneForm P Q) γ := by
  have hc := circulationFun_intervalIntegrable hγ
    (by simpa using hP) (by simpa using hQ)
  apply hc.congr_ae
  rw [Filter.EventuallyEq, uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  exact circulationFun_eq_oneForm P Q γ.extend t

end TauCeti.Green
