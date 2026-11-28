/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.FiniteSum
public import TauCeti.Analysis.Green.WindingWeight.Cycle
public import TauCeti.Analysis.Contour.Cycle.Winding
public import TauCeti.Analysis.Contour.Cycle.Trace
import TauCeti.Analysis.Green.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
import TauCeti.Analysis.Convex.Segment

/-!
# Winding-weighted Green for contour cycles

The canonical support and integer coefficients of an existing contour cycle give its circulation.
The area weight is the existing cycle winding number, set to zero on its null trace. Affine
normalization of each generator handles both orientations and constant parameter intervals.

## Main results

* `TauCeti.Contour.Cycle.green_winding`: Green's theorem for an existing contour cycle with its
  trace-zero winding weight.
* `TauCeti.Contour.Cycle.re_integral_eq_sum_circulationFun` and
  `TauCeti.Contour.Cycle.im_integral_eq_sum_circulationFun`: the real and imaginary parts of
  `C.integral F` written as coefficient-weighted sums of planar circulations of `(Re F, -Im F)`
  and `(Im F, Re F)`.
-/

public section

noncomputable section

open MeasureTheory Set Function

namespace TauCeti.Green

/-- Green's theorem for an existing contour cycle, with its actual total winding number.
The circulation uses the cycle's canonical support and coefficients. Only the total index must
vanish outside the field domain. -/
theorem _root_.TauCeti.Contour.Cycle.green_winding (C : Contour.Cycle) {U : Set ℂ} {P Q : ℂ → ℝ}
    (hU : IsOpen U) (htrace : Contour.Cycle.IsIn C U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : Contour.Cycle.IsNullHomologous C U) :
    (∀ γ ∈ FreeAddCommGroup.support C,
      IntervalIntegrable (circulationFun P Q γ) volume γ.a γ.b) ∧
      IntegrableOn (fun z ↦
        C.windingWeight z *
          curl P Q z) U ∧
      (∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, circulationFun P Q γ t) =
        ∫ z in U,
          C.windingWeight z *
            curl P Q z := by
  classical
  let η : Contour.AbsolutelyContinuousClosedCurve → ℝ → ℂ := fun γ ↦
    γ ∘ AffineMap.lineMap γ.a γ.b
  have hac (γ : Contour.AbsolutelyContinuousClosedCurve) :=
    γ.absolutelyContinuousOnInterval
  have himage (γ : Contour.AbsolutelyContinuousClosedCurve) :
      η γ '' uIcc (0 : ℝ) 1 = γ '' uIcc γ.a γ.b :=
    Set.image_comp_lineMap_uIcc_zero_one γ γ.a γ.b
  have htr (γ : Contour.AbsolutelyContinuousClosedCurve) (hγ : γ ∈ FreeAddCommGroup.support C) :
      γ '' uIcc γ.a γ.b ⊆ U :=
    Set.mapsTo_iff_image_subset.mp (htrace.mapsTo_of_mem_support hγ)
  have hidx : ∀ z ∉ U, ∑ γ ∈ FreeAddCommGroup.support C,
      (FreeAddCommGroup.coeff γ C : ℂ) * Contour.windingNumber (η γ) 0 1 z = 0 := by
    intro z hz
    have hh := Contour.Cycle.isNullHomologous_iff.mp hindex z hz
    rw [Contour.Cycle.windingNumber_eq_sum_support] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [(hac γ).windingNumber_comp_lineMap (fun hm ↦ hz (htr γ hγ hm))]
  have hcl (γ : Contour.AbsolutelyContinuousClosedCurve) : η γ 0 = η γ 1 := by
    simpa only [η, Function.comp_apply, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] using
      γ.source_eq_target
  obtain ⟨_, hi, heq⟩ := green_ac_winding_sum (s := FreeAddCommGroup.support C)
    (γ := η) (a := fun _ ↦ 0) (b := fun _ ↦ 1) (w := fun γ ↦ FreeAddCommGroup.coeff γ C)
    (fun _ _ ↦ zero_lt_one) (fun γ _ ↦ absolutelyContinuousOnInterval_comp_lineMap_iff.2 (hac γ))
    (fun γ _ ↦ hcl γ)
    hU (fun γ hγ ↦ by rw [himage]; exact htr γ hγ) hP hQ hidx
  have haeU : (fun z ↦ ∑ γ ∈ FreeAddCommGroup.support C,
      (FreeAddCommGroup.coeff γ C : ℝ) * windingWeight (η γ) 0 1 z) =ᵐ[volume.restrict U]
      C.windingWeight :=
    (sum_windingWeight_comp_lineMap_ae C).filter_mono ae_restrict_le
  refine ⟨fun γ hγ ↦ AbsolutelyContinuousOnInterval.intervalIntegrable_circulationFun (hac γ)
    (hP.continuousOn.mono (htr γ hγ)) (hQ.continuousOn.mono (htr γ hγ)), ?_, ?_⟩
  · exact hi.congr (haeU.mono fun z hz ↦ congrArg (· * curl P Q z) hz)
  · simp only [η, integral_circulationFun_comp_lineMap] at heq
    exact heq.trans (integral_congr_ae (haeU.mono fun z hz ↦ congrArg (· * curl P Q z) hz))

private theorem clm_integral_eq_sum (C : Contour.Cycle) {F : ℂ → ℂ}
    (hF : ∀ γ ∈ FreeAddCommGroup.support C,
      IntervalIntegrable (fun t ↦ deriv γ t • F (γ t)) volume γ.a γ.b)
    (L : ℂ →L[ℝ] ℝ) {P Q : ℂ → ℝ}
    (hpt : ∀ γ t, L (deriv γ t * F (γ t)) = circulationFun P Q γ t) :
    L (C.integral F) =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, circulationFun P Q γ t := by
  rw [Contour.Cycle.integral_eq_sum_support, map_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [map_zsmul, zsmul_eq_mul, ← L.intervalIntegral_comp_comm (hF γ hγ)]
  exact congrArg _ (intervalIntegral.integral_congr fun t _ ↦ hpt γ t)

/-- When `t ↦ deriv γ t • F (γ t)` is interval-integrable along every curve `γ` in the support
of `C`, the real part of `C.integral F` equals the coefficient-weighted sum of the real
circulations of `(Re F, -Im F)` over the supported generators. -/
theorem _root_.TauCeti.Contour.Cycle.re_integral_eq_sum_circulationFun (C : Contour.Cycle)
    {F : ℂ → ℂ}
    (hF : ∀ γ ∈ FreeAddCommGroup.support C,
      IntervalIntegrable (fun t ↦ deriv γ t • F (γ t)) volume γ.a γ.b) :
    (C.integral F).re =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, circulationFun (fun z ↦ (F z).re) (fun z ↦ -(F z).im) γ t :=
  clm_integral_eq_sum C hF Complex.reCLM fun γ t ↦ re_deriv_mul_eq_circulationFun F γ t

/-- When `t ↦ deriv γ t • F (γ t)` is interval-integrable along every curve `γ` in the support
of `C`, the imaginary part of `C.integral F` equals the coefficient-weighted sum of the real
circulations of `(Im F, Re F)` over the supported generators. -/
theorem _root_.TauCeti.Contour.Cycle.im_integral_eq_sum_circulationFun (C : Contour.Cycle)
    {F : ℂ → ℂ}
    (hF : ∀ γ ∈ FreeAddCommGroup.support C,
      IntervalIntegrable (fun t ↦ deriv γ t • F (γ t)) volume γ.a γ.b) :
    (C.integral F).im =
      ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, circulationFun (fun z ↦ (F z).im) (fun z ↦ (F z).re) γ t :=
  clm_integral_eq_sum C hF Complex.imCLM fun γ t ↦ im_deriv_mul_eq_circulationFun F γ t

end TauCeti.Green
