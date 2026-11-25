/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
public import TauCeti.Analysis.Green.Basic
public import TauCeti.Analysis.Green.WindingWeight.Basic
public import TauCeti.LinearAlgebra.Trace.Complex
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.Green.Winding

/-!
# Green's theorem and flux for simple closed absolutely continuous curves

Combining the Jordan index theorem (`TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan`)
with the winding-weighted Green theorem (`TauCeti.Green.green_ac_winding`) yields Green's curl and
flux-divergence formulas for an arbitrary simple closed absolutely continuous curve `γ` on `[a, b]`
(`a < b`, `γ a = γ b`, `InjOn γ (Ico a b)`), with **no supplied index hypothesis**: the orientation
sign `TauCeti.Contour.jordanSign γ a b ∈ {1, -1}` is a conclusion of simplicity.

## Main results

* `AbsolutelyContinuousOnInterval.windingWeight_eq_indicator_jordanSign`: the winding weight of a
  simple closed AC curve is the indicator of `filledHull C \ C` times `jordanSign γ a b`.
* `TauCeti.Green.green_ac_jordan`: circulation around a simple closed AC curve equals
  `jordanSign γ a b` times the integral of `curl P Q` over `filledHull C \ C`, with both
  integrabilities deduced automatically.
* `TauCeti.Green.green_ac_flux_jordan`: flux-divergence form for a simple closed AC curve.
* `AbsolutelyContinuousOnInterval.integrableOn_filledHull_sdiff_trace_fderiv`,
  `AbsolutelyContinuousOnInterval.intervalIntegrable_inner_jordanSign_smul_I_mul_deriv`, and
  `AbsolutelyContinuousOnInterval.setIntegral_filledHull_sdiff_trace_fderiv_eq`: trace-divergence
  and normal-flux form of Green's theorem for a `C¹` vector field `φ : ℂ → ℂ`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- For a simple closed absolutely continuous curve on `[a, b]` (`a < b`), the winding weight is
`Contour.jordanSign γ a b` times the indicator of the bounded inside
`filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingWeight_eq_indicator_jordanSign
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    windingWeight γ a b =
      (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).indicator
        (fun _ ↦ (Contour.jordanSign γ a b : ℝ)) :=
  hγ.windingWeight_eq_indicator_of_index hclosed (Contour.jordanSign γ a b) fun _ hz ↦
    hγ.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff hab hclosed hinj hz

/-- **Green's theorem for a simple closed absolutely continuous curve:** with no supplied index
hypothesis, both the boundary circulation and the interior curl are integrable and the circulation
equals `Contour.jordanSign γ a b ∈ {1, -1}` times the integral of `curl P Q` over the bounded inside
`filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`. -/
theorem green_ac_jordan {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} {P Q : ℂ → ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hU : IsOpen U) (hregion : filledHull (γ '' uIcc a b) ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      IntegrableOn (curl P Q) (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        (Contour.jordanSign γ a b : ℝ) *
          ∫ z in filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), curl P Q z := by
  let D := filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)
  let σ : ℝ := Contour.jordanSign γ a b
  have hD : MeasurableSet D :=
    (IsClosed.isOpen_filledHull_sdiff
      (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isClosed).measurableSet
  have hDU : D ⊆ U := sdiff_subset.trans hregion
  have hzero (z) (hz : z ∉ U) : Contour.windingNumber γ a b z = 0 :=
    hγ.windingNumber_eq_zero_of_notMem_filledHull hclosed (mt (hregion ·) hz)
  have h := green_ac_winding hab hγ hclosed hU (subset_filledHull.trans hregion) hP hQ hzero
  have hw : (fun z ↦ windingWeight γ a b z * curl P Q z) =
      D.indicator (fun z ↦ σ * curl P Q z) := by
    rw [hγ.windingWeight_eq_indicator_jordanSign hab hclosed hinj]
    ext z
    by_cases hz : z ∈ D <;> simp [D, σ, hz]
  have hintσ : IntegrableOn (fun z ↦ σ * curl P Q z) D :=
    (h.2.1.mono_set hDU).congr_fun (fun z hz ↦ by rw [hw, indicator_of_mem hz]) hD
  have hσsq : σ * σ = 1 := by
    rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with hσ | hσ <;> simp [σ, hσ]
  have hint : IntegrableOn (curl P Q) D := by
    simpa only [IntegrableOn, ← mul_assoc, hσsq, one_mul] using Integrable.const_mul hintσ σ
  refine ⟨h.1, hint, ?_⟩
  rw [h.2.2, hw, setIntegral_indicator hD, inter_eq_right.mpr hDU, integral_const_mul]

/-- **Flux-divergence form of Green's theorem for a simple closed absolutely continuous curve:**
the boundary integral of `X dy - Y dx` equals `Contour.jordanSign γ a b ∈ {1, -1}` times the
divergence integral over `filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`. -/
theorem green_ac_flux_jordan {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} {X Y : ℂ → ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hU : IsOpen U) (hregion : filledHull (γ '' uIcc a b) ⊆ U)
    (hX : ContDiffOn ℝ 1 X U) (hY : ContDiffOn ℝ 1 Y U) :
    IntervalIntegrable
      (fun t ↦ X (γ t) * (deriv γ t).im - Y (γ t) * (deriv γ t).re) volume a b ∧
      IntegrableOn (fun z ↦ fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I)
        (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) ∧
      (∫ t in a..b, X (γ t) * (deriv γ t).im - Y (γ t) * (deriv γ t).re) =
        (Contour.jordanSign γ a b : ℝ) *
          ∫ z in filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
            fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I := by
  have h := green_ac_jordan hab hγ hclosed hinj hU hregion hY.neg hX
  have hc : circulationFun (fun z ↦ -Y z) X γ =
      fun t ↦ X (γ t) * (deriv γ t).im - Y (γ t) * (deriv γ t).re := by
    ext t
    rw [circulationFun]
    ring
  have hd : curl (fun z ↦ -Y z) X =
      fun z ↦ fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I := by
    ext z
    rw [curl]
    -- Pointwise negation `fun z ↦ -Y z` is definitionally `-Y`, exposing `fderiv_neg`.
    change fderiv ℝ X z 1 - fderiv ℝ (-Y) z Complex.I = _
    rw [fderiv_neg, neg_apply, sub_neg_eq_add]
  rwa [hc, hd] at h

end TauCeti.Green

namespace AbsolutelyContinuousOnInterval

open Complex
open scoped RealInnerProductSpace

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- Bundle of integrability and Green's divergence-flux identity on the bounded inside of a simple
closed absolutely continuous curve. -/
private theorem integrableOn_and_setIntegral_filledHull_sdiff_trace_fderiv {W : Set ℂ} {φ : ℂ → ℂ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hW : IsOpen W)
    (hregion : TauCeti.filledHull (γ '' uIcc a b) ⊆ W) (hφ : ContDiffOn ℝ 1 φ W) :
    IntegrableOn (fun z => LinearMap.trace ℝ ℂ (fderiv ℝ φ z).toLinearMap)
        (TauCeti.filledHull (γ '' uIcc a b) \ γ '' uIcc a b) ∧
      IntervalIntegrable
        (fun t => ⟪φ (γ t), -(TauCeti.Contour.jordanSign γ a b : ℝ) • (I * deriv γ t)⟫)
        volume a b ∧
      (∫ z in TauCeti.filledHull (γ '' uIcc a b) \ γ '' uIcc a b,
          LinearMap.trace ℝ ℂ (fderiv ℝ φ z).toLinearMap) =
        ∫ t in a..b,
          ⟪φ (γ t), -(TauCeti.Contour.jordanSign γ a b : ℝ) • (I * deriv γ t)⟫ := by
  set D := TauCeti.filledHull (γ '' uIcc a b) \ γ '' uIcc a b
  set σ : ℝ := (TauCeti.Contour.jordanSign γ a b : ℝ)
  have hD : MeasurableSet D :=
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isClosed.isOpen_filledHull_sdiff
      |>.measurableSet
  have hflux := TauCeti.Green.green_ac_flux_jordan hab hγ hclosed hinj hW hregion
    (Complex.reCLM.contDiff.comp_contDiffOn hφ) (Complex.imCLM.contDiff.comp_contDiffOn hφ)
  have htr : EqOn (fun z => fderiv ℝ (Complex.reCLM ∘ φ) z 1 + fderiv ℝ (Complex.imCLM ∘ φ) z I)
      (fun z => LinearMap.trace ℝ ℂ (fderiv ℝ φ z).toLinearMap) D := fun z hz => by
    dsimp only
    have hd : DifferentiableAt ℝ φ z :=
      (hφ.differentiableOn one_ne_zero z (sdiff_subset.trans hregion hz)).differentiableAt
        (hW.mem_nhds (sdiff_subset.trans hregion hz))
    rw [LinearMap.trace_complex_apply, (Complex.reCLM.hasFDerivAt.comp z hd.hasFDerivAt).fderiv,
      (Complex.imCLM.hasFDerivAt.comp z hd.hasFDerivAt).fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      ContinuousLinearMap.coe_coe]
  have hpt (t : ℝ) :
      ⟪φ (γ t), -σ • (I * deriv γ t)⟫ =
        σ * ((φ (γ t)).re * (deriv γ t).im - (φ (γ t)).im * (deriv γ t).re) := by
    simp [Complex.inner, mul_re, mul_im]
    ring
  have hσsq : σ * σ = 1 := by
    rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h <;> simp [σ, h]
  refine ⟨hflux.2.1.congr_fun htr hD, ?_, ?_⟩
  · simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hflux
    simpa only [hpt] using hflux.1.const_mul σ
  · simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hflux
    simp_rw [hpt, intervalIntegral.integral_const_mul]
    rw [← setIntegral_congr_fun hD htr, hflux.2.2, ← mul_assoc, hσsq, one_mul]

/-- The divergence `tr(Dφ)` of a `C¹` vector field on an open neighbourhood of
`filledHull (γ '' uIcc a b)` is integrable on `filledHull (γ '' uIcc a b) \ γ '' uIcc a b`. -/
theorem integrableOn_filledHull_sdiff_trace_fderiv {W : Set ℂ} {φ : ℂ → ℂ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hW : IsOpen W)
    (hregion : TauCeti.filledHull (γ '' uIcc a b) ⊆ W) (hφ : ContDiffOn ℝ 1 φ W) :
    IntegrableOn (fun z => LinearMap.trace ℝ ℂ (fderiv ℝ φ z).toLinearMap)
      (TauCeti.filledHull (γ '' uIcc a b) \ γ '' uIcc a b) :=
  (hγ.integrableOn_and_setIntegral_filledHull_sdiff_trace_fderiv hab hclosed hinj hW hregion hφ).1

/-- Along a simple closed absolutely continuous curve `γ`, the normal flux integrand
`⟪φ (γ t), -(jordanSign γ a b : ℝ) • (I * deriv γ t)⟫` is interval-integrable on `[a, b]` for any
`C¹` vector field `φ` on an open neighbourhood of `filledHull (γ '' uIcc a b)`. -/
theorem intervalIntegrable_inner_jordanSign_smul_I_mul_deriv {W : Set ℂ} {φ : ℂ → ℂ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hW : IsOpen W)
    (hregion : TauCeti.filledHull (γ '' uIcc a b) ⊆ W) (hφ : ContDiffOn ℝ 1 φ W) :
    IntervalIntegrable
      (fun t => ⟪φ (γ t), -(TauCeti.Contour.jordanSign γ a b : ℝ) • (I * deriv γ t)⟫)
      volume a b :=
  (hγ.integrableOn_and_setIntegral_filledHull_sdiff_trace_fderiv hab hclosed hinj hW hregion hφ).2.1

/-- **Divergence-flux form of Green's theorem for a simple closed absolutely continuous curve.**
For any `C¹` vector field `φ : ℂ → ℂ` on an open neighbourhood `W` of `filledHull (γ '' uIcc a b)`,
`∫_{filledHull C \ C} tr(Dφ) = ∫ₐᵇ ⟪φ (γ t), -(jordanSign γ a b : ℝ) • (I * deriv γ t)⟫`. -/
theorem setIntegral_filledHull_sdiff_trace_fderiv_eq {W : Set ℂ} {φ : ℂ → ℂ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hW : IsOpen W)
    (hregion : TauCeti.filledHull (γ '' uIcc a b) ⊆ W) (hφ : ContDiffOn ℝ 1 φ W) :
    (∫ z in TauCeti.filledHull (γ '' uIcc a b) \ γ '' uIcc a b,
        LinearMap.trace ℝ ℂ (fderiv ℝ φ z).toLinearMap) =
      ∫ t in a..b,
        ⟪φ (γ t), -(TauCeti.Contour.jordanSign γ a b : ℝ) • (I * deriv γ t)⟫ :=
  (hγ.integrableOn_and_setIntegral_filledHull_sdiff_trace_fderiv hab hclosed hinj hW hregion hφ).2.2

end AbsolutelyContinuousOnInterval
