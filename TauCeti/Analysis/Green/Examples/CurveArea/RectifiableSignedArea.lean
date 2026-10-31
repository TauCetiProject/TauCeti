/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.SignedArea
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Rectifiable

/-!
# Signed area of rectifiable plane curves

The signed area `TauCeti.signedArea γ a b = ½ ∫ₐᵇ (x y' - y x')` is computed from the derivative
of the parameter, so it is the right notion only for absolutely continuous curves: a circle
composed with the Cantor function is continuous, of bounded variation, and has zero derivative
almost everywhere, so its derivative integral vanishes.

The **geometric signed area** `TauCeti.rectifiableSignedArea γ a b` is instead the geometric
integral `TauCeti.rectifiableCurveIntegral` of the area form `(x dy - y dx) / 2` along `γ`.
It is computed along the natural (arclength) parameterization of `γ` on its length interval,
and it is meaningful for every continuous plane curve of bounded variation.

## Main results

* `TauCeti.rectifiableSignedArea_eq_signedArea_naturalParameterization`: the geometric signed
  area is the signed area of the natural parameterization on the length interval.
* `TauCeti.rectifiableSignedArea_eq_signedArea_of_eqOn_comp_variationOnFromTo`: it is the signed
  area of any curve through which `γ` factors by cumulative variation.
* `AbsolutelyContinuousOnInterval.rectifiableSignedArea_eq_signedArea`: agreement with
  `TauCeti.signedArea` for absolutely continuous curves.
* `TauCeti.rectifiableSignedArea_eq_signedArea_of_eqOn_comp`: independence of the
  factorization through an absolutely continuous curve and an increasing continuous map.
* `TauCeti.rectifiableSignedArea_comp_of_monotoneOn`,
  `TauCeti.rectifiableSignedArea_comp_of_antitoneOn`: invariance under increasing, and sign
  reversal under decreasing, continuous onto reparametrizations, which need not be absolutely
  continuous.

The isoperimetric inequality bounding the geometric signed area of a closed curve by its length
is in `TauCeti.Analysis.Fourier.AreaEnergy`.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti

variable {γ : ℝ → ℂ} {a b c d : ℝ}

/-- The **geometric signed area** of a plane curve `γ` on `[a, b]`: the geometric integral
`TauCeti.rectifiableCurveIntegral` of the area form `(x dy - y dx) / 2` along `γ`, computed along
the natural parameterization of `γ` on its length interval. For a continuous curve of bounded
variation it is invariant under increasing continuous reparametrizations, and it agrees with
`TauCeti.signedArea` for absolutely continuous curves
(`AbsolutelyContinuousOnInterval.rectifiableSignedArea_eq_signedArea`). It is zero for a curve of
infinite length on `[a, b]` and for `b < a`. -/
noncomputable def rectifiableSignedArea (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  rectifiableCurveIntegral (Green.oneForm Green.Examples.areaP Green.Examples.areaQ) γ a b

/-- The defining formula of `TauCeti.rectifiableSignedArea`. -/
theorem rectifiableSignedArea_def (γ : ℝ → ℂ) (a b : ℝ) :
    rectifiableSignedArea γ a b =
      rectifiableCurveIntegral (Green.oneForm Green.Examples.areaP Green.Examples.areaQ) γ a b :=
  (rfl)

/-- The geometric signed area of `γ` on `[a, b]` is the signed area of its natural
parameterization on the length interval `[0, L]`, where `L` is the total variation of `γ` on
`[a, b]`. -/
theorem rectifiableSignedArea_eq_signedArea_naturalParameterization (γ : ℝ → ℂ) (a b : ℝ) :
    rectifiableSignedArea γ a b =
      signedArea (naturalParameterization γ (Icc a b) a) 0 (eVariationOn γ (Icc a b)).toReal := by
  simp only [rectifiableSignedArea_def, rectifiableCurveIntegral_def,
    signedArea_eq_integral_circulationFun, Green.circulationFun_eq_oneForm]

/-- The geometric signed area of a continuous curve is the signed area, on the length interval,
of any curve `g` through which the curve factors by cumulative variation, such as the factor
given by `BoundedVariationOn.exists_arclength_factorization`. -/
theorem rectifiableSignedArea_eq_signedArea_of_eqOn_comp_variationOnFromTo
    (hcont : ContinuousOn γ (Icc a b)) {g : ℝ → ℂ}
    (hg : EqOn (g ∘ variationOnFromTo γ (Icc a b) a) γ (Icc a b)) :
    rectifiableSignedArea γ a b = signedArea g 0 (eVariationOn γ (Icc a b)).toReal := by
  simp only [rectifiableSignedArea_def, rectifiableCurveIntegral_eq_of_eqOn_comp_variationOnFromTo
    hcont hg, signedArea_eq_integral_circulationFun, Green.circulationFun_eq_oneForm]

/-- The geometric signed area only depends on the curve on `[a, b]`. -/
theorem rectifiableSignedArea_congr {γ' : ℝ → ℂ} (h : EqOn γ γ' (Icc a b)) :
    rectifiableSignedArea γ a b = rectifiableSignedArea γ' a b :=
  rectifiableCurveIntegral_congr h

/-- The geometric signed area of a curve of infinite length on `[a, b]` is zero. -/
theorem rectifiableSignedArea_of_not_boundedVariationOn (h : ¬BoundedVariationOn γ (Icc a b)) :
    rectifiableSignedArea γ a b = 0 :=
  rectifiableCurveIntegral_of_not_boundedVariationOn h

/-- The geometric signed area on `[a, b]` with `b < a` is zero. -/
theorem rectifiableSignedArea_of_lt (h : b < a) : rectifiableSignedArea γ a b = 0 :=
  rectifiableCurveIntegral_of_lt h

/-- The geometric signed area on a degenerate interval `[a, a]` is zero. -/
@[simp]
theorem rectifiableSignedArea_self : rectifiableSignedArea γ a a = 0 :=
  rectifiableCurveIntegral_self

/-- A constant curve has geometric signed area zero. -/
@[simp]
theorem rectifiableSignedArea_const (z : ℂ) (a b : ℝ) :
    rectifiableSignedArea (fun _ ↦ z) a b = 0 := by
  rw [rectifiableSignedArea_eq_signedArea_naturalParameterization,
    eVariationOn.constant_on ((subsingleton_singleton (a := z)).anti (image_subset_iff.2
      fun _ _ ↦ rfl)), ENNReal.toReal_zero, signedArea_self]

/-- **Agreement with the derivative integral.** For an absolutely continuous curve, the geometric
signed area is the signed area `½ ∫ₐᵇ (x y' - y x')` computed from the derivative of the
parameter. -/
theorem _root_.AbsolutelyContinuousOnInterval.rectifiableSignedArea_eq_signedArea
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    rectifiableSignedArea γ a b = signedArea γ a b := by
  rw [rectifiableSignedArea_def, hγ.rectifiableCurveIntegral_eq_intervalIntegral_deriv hab
    Green.Examples.continuous_oneForm_area.continuousOn, signedArea_eq_integral_circulationFun]
  simp only [Green.circulationFun_eq_oneForm]

/-- **Independence of the factorization.** If a curve factors on `[a, b]` as an absolutely
continuous curve `η` on `[c, d]` composed with a continuous increasing map of `[a, b]` onto
`[c, d]`, then its geometric signed area is the signed area of `η` on `[c, d]`. -/
theorem rectifiableSignedArea_eq_signedArea_of_eqOn_comp {η : ℝ → ℂ} {ψ : ℝ → ℝ}
    (hη : AbsolutelyContinuousOnInterval η c d) (hab : a ≤ b) (hψ : ContinuousOn ψ (Icc a b))
    (hψm : MonotoneOn ψ (Icc a b)) (hψa : ψ a = c) (hψb : ψ b = d)
    (h : EqOn (η ∘ ψ) γ (Icc a b)) :
    rectifiableSignedArea γ a b = signedArea η c d := by
  rw [rectifiableSignedArea_def, rectifiableCurveIntegral_eq_of_eqOn_comp hη hab hψ hψm hψa hψb h
    Green.Examples.continuous_oneForm_area.continuousOn, signedArea_eq_integral_circulationFun]
  simp only [Green.circulationFun_eq_oneForm]

/-- The geometric signed area is invariant under increasing continuous reparametrizations of
`[c, d]` onto `[a, b]`. The reparametrization need not be absolutely continuous. -/
theorem rectifiableSignedArea_comp_of_monotoneOn (hcont : ContinuousOn γ (Icc a b)) {φ : ℝ → ℝ}
    (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hφm : MonotoneOn φ (Icc c d)) (hφc : φ c = a) (hφd : φ d = b) :
    rectifiableSignedArea (γ ∘ φ) c d = rectifiableSignedArea γ a b :=
  rectifiableCurveIntegral_comp_of_monotoneOn hcont hcd hφ hφm hφc hφd

/-- The geometric signed area changes sign under decreasing continuous reparametrizations of
`[c, d]` onto `[a, b]`. The reparametrization need not be absolutely continuous. -/
theorem rectifiableSignedArea_comp_of_antitoneOn (hcont : ContinuousOn γ (Icc a b)) {φ : ℝ → ℝ}
    (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hφm : AntitoneOn φ (Icc c d)) (hφc : φ c = b) (hφd : φ d = a) :
    rectifiableSignedArea (γ ∘ φ) c d = -rectifiableSignedArea γ a b :=
  rectifiableCurveIntegral_comp_of_antitoneOn hcont hcd hφ hφm hφc hφd

/-- A circle of radius `R`, traversed once counterclockwise from any initial angle `θ`, has
geometric signed area `π R²`. -/
@[simp]
theorem rectifiableSignedArea_circleMap (c : ℂ) (R θ : ℝ) :
    rectifiableSignedArea (circleMap c R) θ (θ + 2 * π) = π * R ^ 2 := by
  rw [(lipschitzWith_circleMap c R).lipschitzOnWith.absolutelyContinuousOnInterval
    |>.rectifiableSignedArea_eq_signedArea (le_add_of_nonneg_right Real.two_pi_pos.le),
    signedArea_circleMap]

end TauCeti
