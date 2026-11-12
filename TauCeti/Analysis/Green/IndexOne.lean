/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Basic
public import TauCeti.Analysis.Green.WindingWeight.Basic
import TauCeti.Analysis.Green.Winding
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Green and flux for index-one AC curves

Index one on all bounded complementary components identifies the winding weight with the
indicator of the filled hull minus the trace. Green's theorem then gives the unweighted curl
formula without simplicity or a finite division. Substitution of `(-Y, X)` gives flux with
the outward sign `X dy − Y dx` and divergence `∂x X + ∂y Y`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The index-one AC Green theorem over the entire bounded complementary region.
Both integrabilities are conclusions, with no simplicity or finite-component hypothesis. -/
theorem green_ac_index_one {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} {P Q : ℂ → ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hU : IsOpen U) (hregion : filledHull (γ '' uIcc a b) ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      Contour.windingNumber γ a b z = 1) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      IntegrableOn (curl P Q) (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        ∫ z in filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), curl P Q z := by
  let D := filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)
  have hD : MeasurableSet D :=
    (IsClosed.isOpen_filledHull_sdiff
      (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isClosed).measurableSet
  have hDU : D ⊆ U := sdiff_subset.trans hregion
  have hzero (z) (hz : z ∉ U) : Contour.windingNumber γ a b z = 0 :=
    AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component
      hγ hclosed (fun h ↦ hz (hregion (mem_filledHull_iff.mpr h)))
  have h := green_ac_winding hab hγ hclosed hU (subset_filledHull.trans hregion) hP hQ hzero
  have hw : (fun z ↦ windingWeight γ a b z * curl P Q z) = D.indicator (curl P Q) := by
    rw [hγ.windingWeight_eq_indicator_of_index hclosed 1
      (fun z hz ↦ by simpa using hindex z hz)]
    ext z
    by_cases hz : z ∈ D
    · simp only [D, indicator_of_mem hz, Int.cast_one, one_mul]
    · simp only [D, indicator_of_notMem hz, zero_mul]
  refine ⟨h.1, (h.2.1.mono_set hDU).congr_fun (fun z hz ↦ ?_) hD, ?_⟩
  · rw [hw, indicator_of_mem hz]
  · rw [h.2.2, hw, setIntegral_indicator hD, inter_eq_right.mpr hDU]

/-- The flux form of index-one AC Green: the boundary sign is outward and no unit tangent
or nonzero speed is required. -/
theorem green_ac_flux {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} {X Y : ℂ → ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hU : IsOpen U) (hregion : filledHull (γ '' uIcc a b) ⊆ U)
    (hX : ContDiffOn ℝ 1 X U) (hY : ContDiffOn ℝ 1 Y U)
    (hindex : ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      Contour.windingNumber γ a b z = 1) :
    IntervalIntegrable
      (fun t ↦ X (γ t) * (deriv γ t).im - Y (γ t) * (deriv γ t).re) volume a b ∧
      IntegrableOn (fun z ↦ fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I)
        (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) ∧
      (∫ t in a..b, X (γ t) * (deriv γ t).im - Y (γ t) * (deriv γ t).re) =
        ∫ z in filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
          fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I := by
  have h := green_ac_index_one hab hγ hclosed hU hregion hY.neg hX hindex
  have hc : circulationFun (fun z ↦ -Y z) X γ =
      fun t ↦ X (γ t) * (deriv γ t).im - Y (γ t) * (deriv γ t).re := by
    ext t
    rw [circulationFun]
    ring
  have hd : curl (fun z ↦ -Y z) X =
      fun z ↦ fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I := by
    ext z
    rw [curl]
    -- Pointwise negation and the negation of the function have the same values.
    change fderiv ℝ X z 1 - fderiv ℝ (-Y) z Complex.I = _
    rw [fderiv_neg, neg_apply, sub_neg_eq_add]
  rwa [hc, hd] at h

end TauCeti.Green
