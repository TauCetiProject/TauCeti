/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.Number.Concat

/-!
# Concatenation of winding numbers for absolutely continuous curves

For an absolutely continuous curve avoiding a point `z` on two intervals sharing an endpoint, the
winding number over the combined interval is the sum of the winding numbers on the two pieces, in
either orientation.
-/

public section

open Set TauCeti.Contour

namespace AbsolutelyContinuousOnInterval

/-- Off-trace additivity of the winding number over adjacent parameter intervals for an absolutely
continuous curve, in either orientation. -/
theorem windingNumber_concat {γ : ℝ → ℂ} {a b c : ℝ} {z : ℂ}
    (h_ab : AbsolutelyContinuousOnInterval γ a b) (h_bc : AbsolutelyContinuousOnInterval γ b c)
    (hz_ab : z ∉ γ '' uIcc a b) (hz_bc : z ∉ γ '' uIcc b c) :
    windingNumber γ a c z = windingNumber γ a b z + windingNumber γ b c z :=
  TauCeti.Contour.windingNumber_concat
    (cauchyPVExistsAt_of_avoidance h_ab.continuousOn (fun t ht heq ↦ hz_ab ⟨t, ht, heq⟩)
      (h_ab.intervalIntegrable_inv_sub_mul_deriv hz_ab))
    (cauchyPVExistsAt_of_avoidance h_bc.continuousOn (fun t ht heq ↦ hz_bc ⟨t, ht, heq⟩)
      (h_bc.intervalIntegrable_inv_sub_mul_deriv hz_bc))

end AbsolutelyContinuousOnInterval
