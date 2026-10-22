/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.SignedArea
public import TauCeti.Analysis.Green.Winding

/-!
# Signed area and winding number

The signed boundary area of a closed absolutely continuous plane curve is the integral of its
winding weight over the plane (`TauCeti.signedArea_eq_integral_windingWeight`). Consequently,
if the winding number is a fixed integer `n` throughout the bounded complementary region, the
signed area is `n` times that region's Lebesgue area
(`TauCeti.signedArea_eq_intCast_mul_volume_real_of_windingNumber_eq`).

These statements connect the boundary-integral definition of signed area to geometric area.
The winding-weighted identity applies to self-intersecting and multiply traversed curves; the
geometric specialization applies whenever the index is constant on the bounded region.

## Main results

* `TauCeti.signedArea_eq_integral_windingWeight`: Green's winding-weighted area identity.
* `TauCeti.signedArea_eq_intCast_mul_volume_real_of_windingNumber_eq`: the constant-index
  specialization to the intrinsic bounded complementary region.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- The signed boundary area of a closed absolutely continuous plane curve equals the integral
of its winding weight over the plane. The winding weight is zero on the trace, so no boundary
nullity hypothesis is needed. -/
theorem signedArea_eq_integral_windingWeight (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) :
    signedArea γ a b = ∫ z : ℂ, Green.windingWeight γ a b z := by
  rw [signedArea_eq_integral_circulationFun]
  simpa only [Green.Examples.curl_area, mul_one] using
    (Green.green_ac hab hγ hclosed (Green.Examples.contDiff_areaP (n := 1))
      (Green.Examples.contDiff_areaQ (n := 1))).2.2

/-- If a closed absolutely continuous curve has constant integer winding number `n` throughout
the filled hull away from its trace, then its signed area is `n` times the Lebesgue area of that
region. In particular, `n = 1` and `n = -1` give the two orientations of a Jordan curve once its
index theorem is known. -/
theorem signedArea_eq_intCast_mul_volume_real_of_windingNumber_eq (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) (n : ℤ)
    (hindex : ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      Contour.windingNumber γ a b z = n) :
    signedArea γ a b =
      (n : ℝ) * volume.real (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) := by
  let D := filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)
  have hK : IsCompact (γ '' uIcc a b) :=
    isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  have hD : MeasurableSet D :=
    (IsClosed.isOpen_filledHull_sdiff hK.isClosed).measurableSet
  rw [signedArea_eq_integral_windingWeight hab hγ hclosed,
    hγ.windingWeight_eq_indicator_of_index hclosed n hindex,
    integral_indicator_const (n : ℝ) hD]
  simp only [Measure.real, smul_eq_mul, D]
  rw [mul_comm]

end TauCeti
