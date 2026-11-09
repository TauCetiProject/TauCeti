/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
public import TauCeti.Analysis.Green.Examples.CurveArea.RectifiableSignedArea
public import TauCeti.Analysis.Green.Examples.CurveArea.Winding

/-!
# Signed area of simple closed curves

For a simple closed plane curve `γ` on `[a, b]`, with trace `C` and bounded inside
`Ω = filledHull C \ C`, the signed boundary area is the orientation sign `σ ∈ {1, -1}` of the
curve times the Lebesgue area of `Ω`. Hence the absolute value of the signed area is the
actual area enclosed by the curve, whatever its orientation.

For an absolutely continuous curve the signed area is the derivative integral
`TauCeti.signedArea γ a b = ½ ∫ₐᵇ (x y' - y x')` and `σ = TauCeti.Contour.jordanSign γ a b`
(`AbsolutelyContinuousOnInterval.signedArea_eq_jordanSign_mul_volume_real`). This is the
constant-index case `TauCeti.signedArea_eq_intCast_mul_volume_real_of_windingNumber_eq` of Green's
winding-weighted area identity, with the constant index supplied by the Jordan index theorem
`AbsolutelyContinuousOnInterval.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff`.

For a continuous curve of bounded variation, which need not be absolutely continuous, the signed
area is the geometric signed area `TauCeti.rectifiableSignedArea γ a b`, and `σ` is the
orientation sign of the arclength parametrization `naturalParameterization γ (Icc a b) a`
(`BoundedVariationOn.rectifiableSignedArea_eq_jordanSign_mul_volume_real`). The arclength
parametrization is a simple closed absolutely continuous curve with the same trace, so the
absolutely continuous case applies to it.

## Main results

* `AbsolutelyContinuousOnInterval.signedArea_eq_jordanSign_mul_volume_real` and
  `AbsolutelyContinuousOnInterval.abs_signedArea_eq_volume_real`: the signed area of a simple
  closed absolutely continuous curve is `σ` times the area of its inside, so its absolute value is
  that area.
* `BoundedVariationOn.rectifiableSignedArea_eq_jordanSign_mul_volume_real` and
  `BoundedVariationOn.abs_rectifiableSignedArea_eq_volume_real`: the same for the geometric signed
  area of a rectifiable simple closed curve.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2, for the index of a simple closed curve.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **Signed area of a simple closed absolutely continuous curve.** For a simple closed
absolutely continuous curve on `[a, b]` (`a < b`), the signed area `½ ∫ₐᵇ (x y' - y x')` is the
orientation sign `TauCeti.Contour.jordanSign γ a b ∈ {1, -1}` times the Lebesgue area of the
inside `filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`. -/
theorem signedArea_eq_jordanSign_mul_volume_real (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) :
    TauCeti.signedArea γ a b = (TauCeti.Contour.jordanSign γ a b : ℝ) *
      volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) :=
  TauCeti.signedArea_eq_intCast_mul_volume_real_of_windingNumber_eq hab hγ hclosed _
    fun _ hz ↦ hγ.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff hab hclosed hinj hz

/-- **The signed area of a simple closed absolutely continuous curve is the enclosed area up to
sign.** For a simple closed absolutely continuous curve on `[a, b]` (`a < b`), the absolute value
of the signed area `½ ∫ₐᵇ (x y' - y x')` is the Lebesgue area of the inside
`filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`. -/
theorem abs_signedArea_eq_volume_real (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    |TauCeti.signedArea γ a b| =
      volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) := by
  rw [hγ.signedArea_eq_jordanSign_mul_volume_real hab hclosed hinj, abs_mul,
    abs_of_nonneg measureReal_nonneg]
  rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h <;> simp [h]

end AbsolutelyContinuousOnInterval

namespace BoundedVariationOn

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **Geometric signed area of a rectifiable simple closed curve.** For a continuous simple
closed curve of bounded variation on `[a, b]` (`a < b`), the geometric signed area is the
orientation sign `σ ∈ {1, -1}` of its arclength parametrization times the Lebesgue area of the
inside `filledHull (γ '' Icc a b) \ (γ '' Icc a b)`. The curve need not be absolutely
continuous. -/
theorem rectifiableSignedArea_eq_jordanSign_mul_volume_real (hab : a < b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    TauCeti.rectifiableSignedArea γ a b =
      (TauCeti.Contour.jordanSign (naturalParameterization γ (Icc a b) a) 0
          (eVariationOn γ (Icc a b)).toReal : ℝ) *
        volume.real (TauCeti.filledHull (γ '' Icc a b) \ (γ '' Icc a b)) := by
  have himage : naturalParameterization γ (Icc a b) a ''
      uIcc 0 (eVariationOn γ (Icc a b)).toReal = γ '' Icc a b := by
    rw [uIcc_of_le ENNReal.toReal_nonneg, hγ.image_naturalParameterization_Icc hcont hab.le]
  rw [TauCeti.rectifiableSignedArea_eq_signedArea_naturalParameterization, ← himage]
  exact (hγ.absolutelyContinuousOnInterval_naturalParameterization hcont
      hab.le).signedArea_eq_jordanSign_mul_volume_real
    (hγ.toReal_eVariationOn_pos_of_injOn_Ioo hab (hinj.mono Ioo_subset_Ico_self))
    (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab.le hclosed)
    (hγ.injOn_naturalParameterization_Ico hcont hinj hab.le)

/-- **The geometric signed area of a rectifiable simple closed curve is the enclosed area up to
sign.** For a continuous simple closed curve of bounded variation on `[a, b]` (`a < b`), the
absolute value of the geometric signed area is the Lebesgue area of the inside
`filledHull (γ '' Icc a b) \ (γ '' Icc a b)`. The curve need not be absolutely continuous. -/
theorem abs_rectifiableSignedArea_eq_volume_real (hab : a < b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    |TauCeti.rectifiableSignedArea γ a b| =
      volume.real (TauCeti.filledHull (γ '' Icc a b) \ (γ '' Icc a b)) := by
  rw [hγ.rectifiableSignedArea_eq_jordanSign_mul_volume_real hab hcont hclosed hinj, abs_mul,
    abs_of_nonneg measureReal_nonneg]
  rcases hγ.jordanSign_naturalParameterization_eq_one_or_neg_one hab hcont hclosed hinj with
    h | h <;> simp [h]

end BoundedVariationOn
