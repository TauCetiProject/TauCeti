/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Green.Jordan
public import TauCeti.Analysis.Normed.Module.Alternating.Complex

/-!
# Stokes' formula for one-forms on Jordan domains

Let `γ` be a simple closed absolutely continuous curve in the plane, on a parameter interval
`[a, b]`, and let `ω` be a real one-form that is `C¹` on an open set containing the filled hull
of its trace. Then `ω` integrates around `γ` to the Jordan orientation sign
`TauCeti.Contour.jordanSign γ a b ∈ {1, -1}` times the integral of `dω` over the inside
`filledHull (γ '' [[a, b]]) \ γ '' [[a, b]]` of the curve, and both integrals exist
(`TauCeti.integral_oneForm_jordan`). This is the differential-form version of Green's theorem
`TauCeti.Green.green_ac_jordan`, and the Jordan-domain companion of the disc and annulus formulas
`TauCeti.integral_extDeriv_closedBall` and `TauCeti.integral_extDeriv_annulus`. No convexity,
smoothness of the boundary, or restriction on its corners is needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16.
-/

public section

noncomputable section

open Set MeasureTheory

namespace TauCeti

/-- **Stokes' formula on the inside of a simple closed absolutely continuous curve.** A real
one-form `ω`, `C¹` on an open set containing the filled hull of the trace of `γ`, integrates
around `γ` to `Contour.jordanSign γ a b` times the integral of `dω` on the positive basis
`(1, I)` over the inside `filledHull (γ '' [[a, b]]) \ γ '' [[a, b]]`. Both integrals exist. -/
theorem integral_oneForm_jordan {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {γ : ℝ → ℂ} {a b : ℝ}
    {U : Set ℂ} (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) (hU : IsOpen U)
    (hregion : filledHull (γ '' uIcc a b) ⊆ U) (hω : ContDiffOn ℝ 1 ω U) :
    IntervalIntegrable (fun t ↦ ω (γ t) fun _ ↦ deriv γ t) volume a b ∧
      IntegrableOn (fun z ↦ extDeriv ω z ![1, Complex.I])
        (filledHull (γ '' uIcc a b) \ γ '' uIcc a b) ∧
      (∫ t in a..b, ω (γ t) fun _ ↦ deriv γ t) =
        (Contour.jordanSign γ a b : ℝ) *
          ∫ z in filledHull (γ '' uIcc a b) \ γ '' uIcc a b, extDeriv ω z ![1, Complex.I] := by
  let P : ℂ → ℝ := fun z ↦ ω z fun _ ↦ 1
  let Q : ℂ → ℝ := fun z ↦ ω z fun _ ↦ Complex.I
  have hP : ContDiffOn ℝ 1 P U :=
    (ContinuousAlternatingMap.apply ℝ ℂ ℝ fun _ : Fin 1 ↦ (1 : ℂ)).contDiff.comp_contDiffOn hω
  have hQ : ContDiffOn ℝ 1 Q U :=
    (ContinuousAlternatingMap.apply ℝ ℂ ℝ fun _ : Fin 1 ↦ Complex.I).contDiff.comp_contDiffOn hω
  have h := Green.green_ac_jordan hab hγ hclosed hinj hU hregion hP hQ
  have hcirc : Green.circulationFun P Q γ = fun t ↦ ω (γ t) fun _ ↦ deriv γ t := by
    funext t
    rw [ContinuousAlternatingMap.apply_const_complex]
    simp [Green.circulationFun, P, Q, mul_comm]
  have hcurl (z : ℂ) (hz : z ∈ U) : Green.curl P Q z = extDeriv ω z ![1, Complex.I] :=
    (extDeriv_apply_pair_of_differentiableAt
      (((hω z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero) 1 Complex.I).symm
  have hD : MeasurableSet (filledHull (γ '' uIcc a b) \ γ '' uIcc a b) :=
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isClosed.isOpen_filledHull_sdiff
      |>.measurableSet
  rw [hcirc] at h
  refine ⟨h.1, h.2.1.congr_fun (fun z hz ↦ hcurl z (hregion hz.1)) hD, ?_⟩
  rw [h.2.2, setIntegral_congr_fun hD fun z hz ↦ hcurl z (hregion hz.1)]

end TauCeti
