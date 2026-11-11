/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
public import TauCeti.Analysis.Green.Basic
public import TauCeti.Analysis.Green.WindingWeight.Basic
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
