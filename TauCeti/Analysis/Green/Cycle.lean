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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue

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

private def normalizeParameter (a b : ℝ) (t : ℝ) : ℝ := a + (b - a) * t

private theorem normalizeParameter_zero (a b : ℝ) : normalizeParameter a b 0 = a := by
  simp [normalizeParameter]

private theorem normalizeParameter_one (a b : ℝ) : normalizeParameter a b 1 = b := by
  simp [normalizeParameter]

private theorem normalizeParameter_order (a b : ℝ) :
    Monotone (normalizeParameter a b) ∨ Antitone (normalizeParameter a b) := by
  by_cases h : a ≤ b
  · left
    intro s t hst
    exact add_le_add_right (mul_le_mul_of_nonneg_left hst (sub_nonneg.mpr h)) a
  · right
    intro s t hst
    exact add_le_add_right (mul_le_mul_of_nonpos_left hst (sub_nonpos.mpr (le_of_not_ge h))) a

private theorem normalizeParameter_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval (normalizeParameter a b) 0 1 := by
  have hc : ContDiffOn ℝ 1 (normalizeParameter a b) (uIcc (0 : ℝ) 1) := by
    unfold normalizeParameter
    fun_prop
  exact hc.absolutelyContinuousOnInterval

private theorem image_normalizeParameter (a b : ℝ) :
    normalizeParameter a b '' uIcc (0 : ℝ) 1 = uIcc a b := by
  have hc := (normalizeParameter_ac a b).continuousOn
  rcases normalizeParameter_order a b with hm | hm
  · simpa only [normalizeParameter_zero, normalizeParameter_one] using
      hc.image_uIcc_of_monotoneOn (hm.monotoneOn _)
  · simpa only [normalizeParameter_zero, normalizeParameter_one] using
      hc.image_uIcc_of_antitoneOn (hm.antitoneOn _)

private theorem normalized_ac {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (γ ∘ normalizeParameter a b) 0 1 := by
  have hmap : MapsTo (normalizeParameter a b) (uIcc (0 : ℝ) 1) (uIcc a b) := by
    rw [mapsTo_iff_image_subset, image_normalizeParameter]
  rcases normalizeParameter_order a b with hm | hm
  · exact hγ.comp_monotoneOn (normalizeParameter_ac a b) (hm.monotoneOn _) hmap
  · exact hγ.comp_antitoneOn (normalizeParameter_ac a b) (hm.antitoneOn _) hmap

private theorem normalized_windingNumber {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hz : z ∉ γ '' uIcc a b) :
    Contour.windingNumber (γ ∘ normalizeParameter a b) 0 1 z =
      Contour.windingNumber γ a b z := by
  have ho : MonotoneOn (normalizeParameter a b) (Icc (0 : ℝ) 1) ∨
      AntitoneOn (normalizeParameter a b) (Icc (0 : ℝ) 1) :=
    (normalizeParameter_order a b).imp (fun h ↦ h.monotoneOn _) (fun h ↦ h.antitoneOn _)
  have hγ' : AbsolutelyContinuousOnInterval γ
      (normalizeParameter a b 0) (normalizeParameter a b 1) := by
    simpa only [normalizeParameter_zero, normalizeParameter_one] using hγ
  have hz' : z ∉ γ '' uIcc (normalizeParameter a b 0) (normalizeParameter a b 1) := by
    simpa only [normalizeParameter_zero, normalizeParameter_one] using hz
  simpa only [normalizeParameter_zero, normalizeParameter_one] using
    Contour.windingNumber_comp_of_absolutelyContinuousOnInterval hγ'
      (normalizeParameter_ac a b) zero_le_one ho hz'

private theorem normalized_circulation {γ : ℝ → ℂ} {a b : ℝ} {P Q : ℂ → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hP : ContinuousOn P (γ '' uIcc a b)) (hQ : ContinuousOn Q (γ '' uIcc a b)) :
    (∫ t in (0 : ℝ)..1, circulationFun P Q (γ ∘ normalizeParameter a b) t) =
      ∫ t in a..b, circulationFun P Q γ t := by
  have ho : MonotoneOn (normalizeParameter a b) (Icc (0 : ℝ) 1) ∨
      AntitoneOn (normalizeParameter a b) (Icc (0 : ℝ) 1) :=
    (normalizeParameter_order a b).imp (fun h ↦ h.monotoneOn _) (fun h ↦ h.antitoneOn _)
  have hγ' : AbsolutelyContinuousOnInterval γ
      (normalizeParameter a b 0) (normalizeParameter a b 1) := by
    simpa only [normalizeParameter_zero, normalizeParameter_one] using hγ
  have hint : IntervalIntegrable (fun t ↦ oneForm P Q (γ t) (deriv γ t)) volume
      (normalizeParameter a b 0) (normalizeParameter a b 1) := by
    simpa only [normalizeParameter_zero, normalizeParameter_one, ← circulationFun_eq_oneForm]
      using intervalIntegrable_circulationFun hγ hP hQ
  simpa only [normalizeParameter_zero, normalizeParameter_one, ← circulationFun_eq_oneForm]
    using hγ'.integral_oneForm_comp (normalizeParameter_ac a b) zero_le_one ho hint

open Classical in
/-- Green's theorem for an existing contour cycle, with its actual total winding number.
The circulation uses the cycle's canonical support and coefficients. Only the total index must
vanish outside the field domain. -/
theorem green_cycle_winding (C : Contour.Cycle) {U : Set ℂ} {P Q : ℂ → ℝ}
    (hU : IsOpen U) (htrace : Contour.Cycle.IsIn C U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : Contour.Cycle.IsNullHomologous C U) :
    (∀ γ ∈ FreeAbelianGroup.support C,
      IntervalIntegrable (circulationFun P Q γ) volume γ.a γ.b) ∧
      IntegrableOn (fun z ↦
        (if z ∈ Contour.Cycle.trace C then 0 else (Contour.Cycle.windingNumber z C).re) *
          curl P Q z) U ∧
      (∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, circulationFun P Q γ t) =
        ∫ z in U,
          (if z ∈ Contour.Cycle.trace C then 0 else (Contour.Cycle.windingNumber z C).re) *
            curl P Q z := by
  classical
  let η : Contour.PiecewiseC1ClosedCurve → ℝ → ℂ := fun γ ↦
    γ ∘ normalizeParameter γ.a γ.b
  have hac (γ : Contour.PiecewiseC1ClosedCurve) :=
    γ.isPiecewiseC1On.absolutelyContinuousOnInterval
  have himage (γ : Contour.PiecewiseC1ClosedCurve) :
      η γ '' uIcc (0 : ℝ) 1 = γ '' uIcc γ.a γ.b := by
    change (γ ∘ normalizeParameter γ.a γ.b) '' uIcc (0 : ℝ) 1 = _
    rw [image_comp, image_normalizeParameter]
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
    simpa only [η, Function.comp_apply, normalizeParameter_zero, normalizeParameter_one] using
      γ.source_eq_target
  obtain ⟨_, hi, heq⟩ := green_ac_winding_sum (s := FreeAbelianGroup.support C)
    (γ := η) (a := fun _ ↦ 0) (b := fun _ ↦ 1) (w := fun γ ↦ FreeAbelianGroup.coeff γ C)
    (fun _ _ ↦ zero_lt_one) (fun γ _ ↦ normalized_ac (hac γ)) (fun γ _ ↦ hcl γ)
    hU (fun γ hγ ↦ by rw [himage]; exact htr γ hγ) hP hQ hidx
  have hae : (fun z ↦ ∑ γ ∈ FreeAbelianGroup.support C,
      (FreeAbelianGroup.coeff γ C : ℝ) * windingWeight (η γ) 0 1 z) =ᵐ[volume]
      (fun z ↦ if z ∈ Contour.Cycle.trace C then 0 else
        (Contour.Cycle.windingNumber z C).re) := by
    have hnot : ∀ᵐ z ∂volume, z ∉ Contour.Cycle.trace C := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using Contour.Cycle.measure_trace_eq_zero C volume
    filter_upwards [hnot] with z hz
    rw [ite_eq_right hz, Contour.Cycle.windingNumber_eq_sum_support, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hzγ : z ∉ γ '' uIcc γ.a γ.b := by
      exact fun hm ↦ hz (Contour.Cycle.mem_trace_iff.mpr ⟨γ, hγ, hm⟩)
    rw [windingWeight_eq_of_notMem (by rwa [himage]),
      normalized_windingNumber (hac γ) hzγ]
    simp
  have haeU : (fun z ↦ ∑ γ ∈ FreeAbelianGroup.support C,
      (FreeAbelianGroup.coeff γ C : ℝ) * windingWeight (η γ) 0 1 z) =ᵐ[volume.restrict U]
      (fun z ↦ if z ∈ Contour.Cycle.trace C then 0 else
        (Contour.Cycle.windingNumber z C).re) := hae.filter_mono ae_restrict_le
  refine ⟨fun γ hγ ↦ intervalIntegrable_circulationFun (hac γ)
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
