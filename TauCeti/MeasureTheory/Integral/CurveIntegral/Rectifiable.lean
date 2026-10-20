/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Analysis.ConstantSpeed
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Convergence
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Reparam
public import TauCeti.Topology.MetricSpace.Arclength.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Integrals of 1-forms along rectifiable curves

The integral `∫ t in a..b, ω (γ t) (deriv γ t)` of a 1-form `ω` against the derivative of a
parameter is the right notion only for absolutely continuous curves. A continuous curve of
bounded variation can have zero derivative almost everywhere while tracing a circle: compose
the circle with the Cantor function. Its derivative integral then vanishes for every 1-form.

The geometric integral `TauCeti.rectifiableCurveIntegral ω γ a b` of a 1-form `ω` along a
curve `γ` on `[a, b]` is instead computed along Mathlib's natural parameterization
`naturalParameterization γ (Icc a b) a` on the length interval `[0, L]`, where
`L = eVariationOn γ (Icc a b)`. For a continuous curve of bounded variation this parametrization
is 1-Lipschitz, hence absolutely continuous, and it traces the same points with the same
multiplicity: `γ` factors as the natural parameterization composed with cumulative variation.

The main results are:

* `BoundedVariationOn.eqOn_naturalParameterization`: the arclength factor is unique on the
  length interval, and `BoundedVariationOn.image_naturalParameterization`: it has the same trace.
* `TauCeti.rectifiableCurveIntegral_congr`: the integral only depends on the curve on `[a, b]`.
* `TauCeti.rectifiableCurveIntegral_comp_of_monotoneOn`: invariance under increasing continuous
  onto reparametrizations, which need not be absolutely continuous.
* `TauCeti.rectifiableCurveIntegral_comp_of_antitoneOn`: sign reversal under decreasing ones.
* `AbsolutelyContinuousOnInterval.rectifiableCurveIntegral_eq_intervalIntegral_deriv`: for an
  absolutely continuous curve and a 1-form continuous on its trace, the geometric integral is the
  derivative integral `∫ t in a..b, ω (γ t) (deriv γ t)`;
  `Path.rectifiableCurveIntegral_extend_eq_curveIntegral` compares it with Mathlib's
  `curveIntegral`.
* `TauCeti.rectifiableCurveIntegral_eq_of_eqOn_comp`: independence of the factorization. If
  `γ = η ∘ ψ` on `[a, b]` with `η` absolutely continuous and `ψ` continuous and increasing, the
  geometric integral is the derivative integral of `η`.

The comparison with absolutely continuous curves uses the absolute continuity of cumulative
variation and the reparametrization formula `AbsolutelyContinuousOnInterval.integral_oneForm_comp`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows*, second edition, §1.1
  (arclength parametrization of metric curves).
-/

public section

open MeasureTheory Set

namespace BoundedVariationOn

variable {X : Type*} [MetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- The arclength factor of a continuous rectifiable curve is unique on its length interval:
a curve `g` with `g ∘ variationOnFromTo γ (Icc a b) a = γ` on `[a, b]` agrees there with the
natural parameterization. -/
theorem eqOn_naturalParameterization (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) {g : ℝ → X}
    (hg : EqOn (g ∘ variationOnFromTo γ (Icc a b) a) γ (Icc a b)) :
    EqOn g (naturalParameterization γ (Icc a b) a) (Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
  rw [← hγ.image_variationOnFromTo_Icc hcont hab]
  rintro _ ⟨t, ht, rfl⟩
  have hN :=
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) ht
  exact (hg ht).trans hN.symm

/-- The natural parameterization of a continuous rectifiable curve on its length interval traces
the same set as the curve. -/
theorem image_naturalParameterization (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) :
    naturalParameterization γ (Icc a b) a '' Icc 0 (eVariationOn γ (Icc a b)).toReal =
      γ '' Icc a b := by
  rw [← hγ.image_variationOnFromTo_Icc hcont hab, image_image]
  exact image_congr fun t ht ↦
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) ht

end BoundedVariationOn

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : E → E →L[ℝ] F} {γ : ℝ → E} {a b c d : ℝ}

/-- The geometric integral of a 1-form `ω` along a curve `γ` on `[a, b]`: the integral
`∫ u in 0..L, ω (η u) (deriv η u)` along the natural parameterization `η` of `γ` on its length
interval, where `L` is the total variation of `γ` on `[a, b]`. It is meaningful for continuous
curves of bounded variation with `a ≤ b`; it then counts the trace with its traversal multiplicity
and orientation. -/
noncomputable def rectifiableCurveIntegral (ω : E → E →L[ℝ] F) (γ : ℝ → E) (a b : ℝ) : F :=
  ∫ u in 0..(eVariationOn γ (Icc a b)).toReal,
    ω (naturalParameterization γ (Icc a b) a u) (deriv (naturalParameterization γ (Icc a b) a) u)

/-- The defining formula of `TauCeti.rectifiableCurveIntegral`. -/
theorem rectifiableCurveIntegral_def (ω : E → E →L[ℝ] F) (γ : ℝ → E) (a b : ℝ) :
    rectifiableCurveIntegral ω γ a b =
      ∫ u in 0..(eVariationOn γ (Icc a b)).toReal,
        ω (naturalParameterization γ (Icc a b) a u)
          (deriv (naturalParameterization γ (Icc a b) a) u) :=
  (rfl)

/-- The integral `∫ u in c..d, ω (f u) (deriv f u)` of a 1-form along a curve only depends on
the curve on `[c, d]`. -/
theorem integral_oneForm_congr {f g : ℝ → E} (hcd : c ≤ d) (h : EqOn f g (Icc c d)) :
    ∫ u in c..d, ω (f u) (deriv f u) = ∫ u in c..d, ω (g u) (deriv g u) := by
  have hderiv := (h.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume d] with u hud hu
  rw [uIoc_of_le hcd] at hu
  have hu' : u ∈ Ioo c d := ⟨hu.1, lt_of_le_of_ne hu.2 hud⟩
  rw [h (Ioo_subset_Icc_self hu'), hderiv hu']

/-- The geometric integral along a continuous rectifiable curve is the integral along any curve
`g` through which the curve factors by cumulative variation. -/
private theorem rectifiableCurveIntegral_eq_of_eqOn_comp_variationOnFromTo
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    {g : ℝ → E} (hg : EqOn (g ∘ variationOnFromTo γ (Icc a b) a) γ (Icc a b)) :
    rectifiableCurveIntegral ω γ a b =
      ∫ u in 0..(eVariationOn γ (Icc a b)).toReal, ω (g u) (deriv g u) :=
  integral_oneForm_congr ENNReal.toReal_nonneg (hγ.eqOn_naturalParameterization hcont hab hg).symm

/-- The geometric integral only depends on the curve on `[a, b]`. -/
theorem rectifiableCurveIntegral_congr {γ' : ℝ → E} (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) (h : EqOn γ γ' (Icc a b)) :
    rectifiableCurveIntegral ω γ' a b = rectifiableCurveIntegral ω γ a b := by
  have hL : eVariationOn γ' (Icc a b) = eVariationOn γ (Icc a b) := eVariationOn.eq_of_eqOn h.symm
  have hγ' : BoundedVariationOn γ' (Icc a b) := by rwa [BoundedVariationOn, hL]
  rw [rectifiableCurveIntegral_eq_of_eqOn_comp_variationOnFromTo hγ' (hcont.congr h.symm) hab
    (g := naturalParameterization γ (Icc a b) a), hL, rectifiableCurveIntegral_def]
  intro t ht
  rw [Function.comp_apply, variationOnFromTo.eq_of_le _ _ ht.1,
    eVariationOn.eq_of_eqOn (h.symm.mono inter_subset_left), ← variationOnFromTo.eq_of_le _ _ ht.1,
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) ht,
    h ht]

/-- The geometric integral is invariant under increasing continuous reparametrizations of
`[c, d]` onto `[a, b]`. The reparametrization need not be absolutely continuous. -/
theorem rectifiableCurveIntegral_comp_of_monotoneOn (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) {φ : ℝ → ℝ} (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hφm : MonotoneOn φ (Icc c d)) (hφc : φ c = a) (hφd : φ d = b) :
    rectifiableCurveIntegral ω (γ ∘ φ) c d = rectifiableCurveIntegral ω γ a b := by
  have hab : a ≤ b := hφc ▸ hφd ▸ hφm (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd
  have himage : φ '' Icc c d = Icc a b := by
    rw [hφ.image_Icc_of_monotoneOn hcd hφm, hφc, hφd]
  have hL : eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) := by
    rw [eVariationOn.comp_eq_of_monotoneOn _ _ hφm, himage]
  have hγφ : BoundedVariationOn (γ ∘ φ) (Icc c d) := by rwa [BoundedVariationOn, hL]
  have hcontφ : ContinuousOn (γ ∘ φ) (Icc c d) :=
    hcont.comp hφ (himage ▸ mapsTo_image φ (Icc c d))
  rw [rectifiableCurveIntegral_eq_of_eqOn_comp_variationOnFromTo hγφ hcontφ hcd
    (g := naturalParameterization γ (Icc a b) a), hL, rectifiableCurveIntegral_def]
  intro t ht
  have hφt : φ t ∈ Icc a b := himage ▸ mem_image_of_mem φ ht
  rw [Function.comp_apply, variationOnFromTo.comp_eq_of_monotoneOn γ φ hφm (left_mem_Icc.2 hcd) ht,
    himage, hφc,
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) hφt,
    Function.comp_apply]

/-- The geometric integral changes sign under decreasing continuous reparametrizations of
`[c, d]` onto `[a, b]`. The reparametrization need not be absolutely continuous. -/
theorem rectifiableCurveIntegral_comp_of_antitoneOn (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) {φ : ℝ → ℝ} (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hφm : AntitoneOn φ (Icc c d)) (hφc : φ c = b) (hφd : φ d = a) :
    rectifiableCurveIntegral ω (γ ∘ φ) c d = -rectifiableCurveIntegral ω γ a b := by
  have hab : a ≤ b := hφc ▸ hφd ▸ hφm (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd
  have himage : φ '' Icc c d = Icc a b := by
    rw [hφ.image_Icc_of_antitoneOn hcd hφm, hφc, hφd]
  have hL : eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) := by
    rw [eVariationOn.comp_eq_of_antitoneOn _ _ hφm, himage]
  have hγφ : BoundedVariationOn (γ ∘ φ) (Icc c d) := by rwa [BoundedVariationOn, hL]
  have hcontφ : ContinuousOn (γ ∘ φ) (Icc c d) :=
    hcont.comp hφ (himage ▸ mapsTo_image φ (Icc c d))
  set L := (eVariationOn γ (Icc a b)).toReal
  set η := naturalParameterization γ (Icc a b) a
  -- The reversed curve `u ↦ η (L - u)` is the arclength factor of `γ ∘ φ`.
  rw [rectifiableCurveIntegral_eq_of_eqOn_comp_variationOnFromTo hγφ hcontφ hcd
    (g := fun u ↦ η (L - u)), hL, rectifiableCurveIntegral_def]
  · simp only [deriv_comp_const_sub, map_neg, intervalIntegral.integral_neg]
    rw [intervalIntegral.integral_comp_sub_left (fun v ↦ ω (η v) (deriv η v)) L, sub_self,
      sub_zero]
  intro t ht
  have hφt : φ t ∈ Icc a b := himage ▸ mem_image_of_mem φ ht
  have hsub : Icc (φ t) b ⊆ Icc a b := Icc_subset_Icc_left hφt.1
  -- Cumulative variation of `γ ∘ φ` up to `t` is the variation of `γ` on `[φ t, b]`.
  have hvar : variationOnFromTo (γ ∘ φ) (Icc c d) c t =
      L - variationOnFromTo γ (Icc a b) a (φ t) := by
    have hct : Icc c d ∩ Icc c t = Icc c t := inter_eq_right.2 (Icc_subset_Icc_right ht.2)
    have himage' : φ '' Icc c t = Icc (φ t) b := by
      rw [(hφ.mono (Icc_subset_Icc_right ht.2)).image_Icc_of_antitoneOn ht.1
        (hφm.mono (Icc_subset_Icc_right ht.2)), hφc]
    have hLab : L = variationOnFromTo γ (Icc a b) a b := by
      rw [variationOnFromTo.eq_of_le _ _ hab, inter_self]
    rw [variationOnFromTo.eq_of_le _ _ ht.1, hct,
      eVariationOn.comp_eq_of_antitoneOn _ _ (hφm.mono (Icc_subset_Icc_right ht.2)), himage', hLab,
      variationOnFromTo.sub_right hγ.locallyBoundedVariationOn (left_mem_Icc.2 hab)
        (right_mem_Icc.2 hab) hφt,
      variationOnFromTo.eq_of_le _ _ hφt.2, inter_eq_right.2 hsub]
  rw [Function.comp_apply, hvar, sub_sub_cancel]
  exact
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) hφt

end TauCeti

namespace AbsolutelyContinuousOnInterval

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ω : E → E →L[ℝ] F} {γ : ℝ → E} {a b : ℝ}

/-- For an absolutely continuous curve and a 1-form continuous on its trace, the geometric
integral is the integral `∫ t in a..b, ω (γ t) (deriv γ t)` against the derivative of the
parameter. -/
theorem rectifiableCurveIntegral_eq_intervalIntegral_deriv
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b)
    (hω : ContinuousOn ω (γ '' Icc a b)) :
    rectifiableCurveIntegral ω γ a b = ∫ t in a..b, ω (γ t) (deriv γ t) := by
  have hBV : BoundedVariationOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.boundedVariationOn
  have hcont : ContinuousOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.continuousOn
  set θ := variationOnFromTo γ (Icc a b) a
  set η := naturalParameterization γ (Icc a b) a
  have hθa : θ a = 0 := variationOnFromTo.self _ _ _
  have hθb : θ b = (eVariationOn γ (Icc a b)).toReal := by
    simp only [θ, variationOnFromTo.eq_of_le _ _ hab, inter_self]
  have hθ : AbsolutelyContinuousOnInterval θ a b := by
    simpa only [θ, uIcc_of_le hab] using hγ.absolutelyContinuousOnInterval_variationOnFromTo
  have hθm : MonotoneOn θ (Icc a b) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn (left_mem_Icc.2 hab)
  have hfactor : EqOn (η ∘ θ) γ (Icc a b) := fun t ht ↦
    hBV.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) ht
  -- The natural parameterization is 1-Lipschitz on the length interval `[θ a, θ b]`.
  have hlength : uIcc (θ a) (θ b) = θ '' Icc a b := by
    rw [hθa, hθb, uIcc_of_le ENNReal.toReal_nonneg, hBV.image_variationOnFromTo_Icc hcont hab]
  have hη : AbsolutelyContinuousOnInterval η (θ a) (θ b) := by
    refine LipschitzOnWith.absolutelyContinuousOnInterval (K := 1) ?_
    rw [hlength]
    exact HasConstantSpeedOnWith.lipschitzOnWith
      (has_unit_speed_naturalParameterization γ hBV.locallyBoundedVariationOn (left_mem_Icc.2 hab))
  have hωη : ContinuousOn ω (η '' uIcc (θ a) (θ b)) := by
    rwa [hθa, hθb, uIcc_of_le ENNReal.toReal_nonneg, hBV.image_naturalParameterization hcont hab]
  rw [← integral_oneForm_congr hab hfactor, integral_oneForm_comp hη hθ hab (Or.inl hθm)
    (hη.intervalIntegrable_oneForm_of_continuousOn hωη), hθa, hθb, rectifiableCurveIntegral_def]

end AbsolutelyContinuousOnInterval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ω : E → E →L[ℝ] F} {γ : ℝ → E} {a b c d : ℝ}

/-- **Independence of the factorization.** If a curve factors on `[a, b]` as an absolutely
continuous curve `η` on `[c, d]` composed with a continuous increasing map of `[a, b]` onto
`[c, d]`, then its geometric integral against a 1-form continuous on its trace is the integral
along `η` against the derivative of `η`. -/
theorem rectifiableCurveIntegral_eq_of_eqOn_comp {η : ℝ → E} {ψ : ℝ → ℝ}
    (hη : AbsolutelyContinuousOnInterval η c d) (hab : a ≤ b) (hψ : ContinuousOn ψ (Icc a b))
    (hψm : MonotoneOn ψ (Icc a b)) (hψa : ψ a = c) (hψb : ψ b = d)
    (h : EqOn (η ∘ ψ) γ (Icc a b)) (hω : ContinuousOn ω (γ '' Icc a b)) :
    rectifiableCurveIntegral ω γ a b = ∫ u in c..d, ω (η u) (deriv η u) := by
  have hcd : c ≤ d := hψa ▸ hψb ▸ hψm (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  have himage : ψ '' Icc a b = Icc c d := by
    rw [hψ.image_Icc_of_monotoneOn hab hψm, hψa, hψb]
  have hBV : BoundedVariationOn η (Icc c d) := uIcc_of_le hcd ▸ hη.boundedVariationOn
  have hcont : ContinuousOn η (Icc c d) := uIcc_of_le hcd ▸ hη.continuousOn
  have hcomp : rectifiableCurveIntegral ω (η ∘ ψ) a b = rectifiableCurveIntegral ω η c d :=
    rectifiableCurveIntegral_comp_of_monotoneOn hBV hcont hab hψ hψm hψa hψb
  have hBVψ : BoundedVariationOn (η ∘ ψ) (Icc a b) := by
    rw [BoundedVariationOn, eVariationOn.comp_eq_of_monotoneOn _ _ hψm, himage]
    exact hBV
  have hcontψ : ContinuousOn (η ∘ ψ) (Icc a b) :=
    hcont.comp hψ (himage ▸ mapsTo_image ψ (Icc a b))
  have htrace : η '' Icc c d = γ '' Icc a b := by
    rw [← himage, image_image]
    exact image_congr fun t ht ↦ h ht
  rw [rectifiableCurveIntegral_congr hBVψ hcontψ hab h, hcomp,
    hη.rectifiableCurveIntegral_eq_intervalIntegral_deriv hcd (htrace ▸ hω)]

/-- For a path whose extension is absolutely continuous on `[0, 1]` and a 1-form continuous on
its range, the geometric integral is Mathlib's `curveIntegral`. -/
theorem _root_.Path.rectifiableCurveIntegral_extend_eq_curveIntegral {x y : E} (γ : Path x y)
    (hγ : AbsolutelyContinuousOnInterval γ.extend 0 1) (hω : ContinuousOn ω (range γ)) :
    rectifiableCurveIntegral ω γ.extend 0 1 = ∫ᶜ z in γ, ω z := by
  rw [curveIntegral_eq_intervalIntegral_deriv,
    hγ.rectifiableCurveIntegral_eq_intervalIntegral_deriv zero_le_one
      (by rwa [γ.image_extend_of_subset subset_rfl])]

end TauCeti
