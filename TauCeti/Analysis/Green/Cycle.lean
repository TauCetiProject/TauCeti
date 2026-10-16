/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.FiniteSum
public import TauCeti.Analysis.Contour.Cycle.Winding
public import TauCeti.Analysis.Contour.Cycle.Trace
import TauCeti.Analysis.Green.AbsolutelyContinuous
import TauCeti.Analysis.Contour.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Winding-weighted Green for contour cycles

The canonical support and integer coefficients of an existing contour cycle give its circulation.
The area weight is the existing cycle winding number, set to zero on its null trace. Affine
normalization of each generator handles both orientations and constant parameter intervals.
-/

public section

noncomputable section

open MeasureTheory Set Function

namespace TauCeti.Green

private theorem normalized_ac {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (γ ∘ AffineMap.lineMap a b) 0 1 := by
  have hmap : MapsTo (AffineMap.lineMap a b) (uIcc (0 : ℝ) 1) (uIcc a b) := by
    rw [mapsTo_iff_image_subset, uIcc_of_le zero_le_one,
      ← segment_eq_image_lineMap, segment_eq_uIcc]
  rcases le_total a b with hab | hab
  · exact hγ.comp_monotoneOn
      ((lipschitzWith_lineMap a b).lipschitzOnWith.absolutelyContinuousOnInterval)
      ((AffineMap.lineMap_mono hab).monotoneOn _) hmap
  · exact hγ.comp_antitoneOn
      ((lipschitzWith_lineMap a b).lipschitzOnWith.absolutelyContinuousOnInterval)
      ((AffineMap.lineMap_anti hab).antitoneOn _) hmap

private theorem normalized_windingNumber {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hz : z ∉ γ '' uIcc a b) :
    Contour.windingNumber (γ ∘ AffineMap.lineMap a b) 0 1 z =
      Contour.windingNumber γ a b z := by
  have ho : MonotoneOn (AffineMap.lineMap a b) (Icc (0 : ℝ) 1) ∨
      AntitoneOn (AffineMap.lineMap a b) (Icc (0 : ℝ) 1) :=
    (le_total a b).imp
      (fun h ↦ (AffineMap.lineMap_mono h).monotoneOn _)
      (fun h ↦ (AffineMap.lineMap_anti h).antitoneOn _)
  have hγ' : AbsolutelyContinuousOnInterval γ
      (AffineMap.lineMap a b (0 : ℝ)) (AffineMap.lineMap a b (1 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hγ
  have hz' : z ∉ γ '' uIcc (AffineMap.lineMap a b (0 : ℝ)) (AffineMap.lineMap a b (1 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hz
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    AbsolutelyContinuousOnInterval.windingNumber_comp hγ'
      ((lipschitzWith_lineMap a b).lipschitzOnWith.absolutelyContinuousOnInterval)
      zero_le_one ho hz'

private theorem normalized_circulation {γ : ℝ → ℂ} {a b : ℝ} {P Q : ℂ → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hP : ContinuousOn P (γ '' uIcc a b)) (hQ : ContinuousOn Q (γ '' uIcc a b)) :
    (∫ t in (0 : ℝ)..1, circulationFun P Q (γ ∘ AffineMap.lineMap a b) t) =
      ∫ t in a..b, circulationFun P Q γ t := by
  have ho : MonotoneOn (AffineMap.lineMap a b) (Icc (0 : ℝ) 1) ∨
      AntitoneOn (AffineMap.lineMap a b) (Icc (0 : ℝ) 1) :=
    (le_total a b).imp
      (fun h ↦ (AffineMap.lineMap_mono h).monotoneOn _)
      (fun h ↦ (AffineMap.lineMap_anti h).antitoneOn _)
  have hγ' : AbsolutelyContinuousOnInterval γ
      (AffineMap.lineMap a b (0 : ℝ)) (AffineMap.lineMap a b (1 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hγ
  have hint : IntervalIntegrable (fun t ↦ oneForm P Q (γ t) (deriv γ t)) volume
      (AffineMap.lineMap a b (0 : ℝ)) (AffineMap.lineMap a b (1 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
      ← circulationFun_eq_oneForm]
      using hγ.intervalIntegrable_circulationFun hP hQ
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    ← circulationFun_eq_oneForm]
    using hγ'.integral_oneForm_comp
      ((lipschitzWith_lineMap a b).lipschitzOnWith.absolutelyContinuousOnInterval)
      zero_le_one ho hint

/-- Green's theorem for an existing contour cycle, with its actual total winding number.
The circulation uses the cycle's canonical support and coefficients. Only the total index must
vanish outside the field domain. -/
theorem _root_.TauCeti.Contour.Cycle.green_winding (C : Contour.Cycle) {U : Set ℂ} {P Q : ℂ → ℝ}
    (hU : IsOpen U) (htrace : Contour.Cycle.IsIn C U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : Contour.Cycle.IsNullHomologous C U) :
    (∀ γ ∈ FreeAbelianGroup.support C,
      IntervalIntegrable (circulationFun P Q γ) volume γ.a γ.b) ∧
      IntegrableOn (fun z ↦
        C.windingWeight z *
          curl P Q z) U ∧
      (∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, circulationFun P Q γ t) =
        ∫ z in U,
          C.windingWeight z *
            curl P Q z := by
  classical
  let η : Contour.PiecewiseC1ClosedCurve → ℝ → ℂ := fun γ ↦
    γ ∘ AffineMap.lineMap γ.a γ.b
  have hac (γ : Contour.PiecewiseC1ClosedCurve) :=
    γ.isPiecewiseC1On.absolutelyContinuousOnInterval
  have himage (γ : Contour.PiecewiseC1ClosedCurve) :
      η γ '' uIcc (0 : ℝ) 1 = γ '' uIcc γ.a γ.b := by
    change (γ ∘ AffineMap.lineMap γ.a γ.b) '' uIcc (0 : ℝ) 1 = _
    rw [image_comp, uIcc_of_le zero_le_one,
      ← segment_eq_image_lineMap, segment_eq_uIcc]
  have htr (γ : Contour.PiecewiseC1ClosedCurve) (hγ : γ ∈ FreeAbelianGroup.support C) :
      γ '' uIcc γ.a γ.b ⊆ U := by
    intro z hz
    exact (Contour.Cycle.isIn_iff.mp htrace)
      (Contour.Cycle.mem_trace_iff.mpr ⟨γ, hγ, hz⟩)
  have hidx : ∀ z ∉ U, ∑ γ ∈ FreeAbelianGroup.support C,
      (FreeAbelianGroup.coeff γ C : ℂ) * Contour.windingNumber (η γ) 0 1 z = 0 := by
    intro z hz
    have hh := Contour.Cycle.isNullHomologous_iff.mp hindex z hz
    rw [Contour.Cycle.windingNumber_eq_sum_support] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [normalized_windingNumber (hac γ) (fun hm ↦ hz (htr γ hγ hm))]
  have hcl (γ : Contour.PiecewiseC1ClosedCurve) : η γ 0 = η γ 1 := by
    simpa only [η, Function.comp_apply, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] using
      γ.source_eq_target
  obtain ⟨_, hi, heq⟩ := green_ac_winding_sum (s := FreeAbelianGroup.support C)
    (γ := η) (a := fun _ ↦ 0) (b := fun _ ↦ 1) (w := fun γ ↦ FreeAbelianGroup.coeff γ C)
    (fun _ _ ↦ zero_lt_one) (fun γ _ ↦ normalized_ac (hac γ)) (fun γ _ ↦ hcl γ)
    hU (fun γ hγ ↦ by rw [himage]; exact htr γ hγ) hP hQ hidx
  have hae : (fun z ↦ ∑ γ ∈ FreeAbelianGroup.support C,
      (FreeAbelianGroup.coeff γ C : ℝ) * windingWeight (η γ) 0 1 z) =ᵐ[volume]
      C.windingWeight := by
    have hnot : ∀ᵐ z ∂volume, z ∉ Contour.Cycle.trace C := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using Contour.Cycle.addHaar_trace_eq_zero C volume
    filter_upwards [hnot] with z hz
    rw [Contour.Cycle.windingWeight_eq_of_notMem C hz,
      Contour.Cycle.windingNumber_eq_sum_support, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hzγ : z ∉ γ '' uIcc γ.a γ.b := by
      exact fun hm ↦ hz (Contour.Cycle.mem_trace_iff.mpr ⟨γ, hγ, hm⟩)
    rw [windingWeight_eq_of_notMem (by rwa [himage]),
      normalized_windingNumber (hac γ) hzγ]
    simp
  have haeU : (fun z ↦ ∑ γ ∈ FreeAbelianGroup.support C,
      (FreeAbelianGroup.coeff γ C : ℝ) * windingWeight (η γ) 0 1 z) =ᵐ[volume.restrict U]
      C.windingWeight :=
    hae.filter_mono ae_restrict_le
  refine ⟨fun γ hγ ↦ AbsolutelyContinuousOnInterval.intervalIntegrable_circulationFun (hac γ)
    (hP.continuousOn.mono (htr γ hγ)) (hQ.continuousOn.mono (htr γ hγ)), ?_, ?_⟩
  · exact hi.congr (haeU.mono fun z hz ↦ congrArg (· * curl P Q z) hz)
  · have hbnd : (∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in (0 : ℝ)..1, circulationFun P Q (η γ) t) =
        ∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
          ∫ t in γ.a..γ.b, circulationFun P Q γ t := by
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [normalized_circulation (hac γ) (hP.continuousOn.mono (htr γ hγ))
        (hQ.continuousOn.mono (htr γ hγ))]
    rw [hbnd] at heq
    exact heq.trans (integral_congr_ae (haeU.mono fun z hz ↦ congrArg (· * curl P Q z) hz))

end TauCeti.Green
