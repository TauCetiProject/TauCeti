/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Negative powers in `Lᵖ` near the origin and shifted interval powers

On an interval `(0, c)`, the power `t ↦ t ^ (-a)` is in `Lᵖ` for every finite exponent `p` with
`a p < 1` (`TauCeti.memLp_rpow_neg_restrict_Ioo`). This is the `Lᵖ` form of Mathlib's
`intervalIntegral.integrableOn_Ioo_rpow_iff`. For `a = 1 / 2` it shows that the derivative
`(2 √t)⁻¹` of `t ↦ √t` is in `Lᵖ(0, c)` for `p < 2`. Translating `(0, b - a)` to `(a, b)` also
gives the shifted integrability criterion `TauCeti.integrableOn_Ioo_sub_rpow_iff`: for `a < b`,
`t ↦ (t - a) ^ s` is integrable on `(a, b)` if and only if `-1 < s`.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- On `(0, c)`, the power `t ↦ t ^ (-a)` is in `Lᵖ` for every finite exponent `p` with
`a p < 1`. -/
theorem memLp_rpow_neg_restrict_Ioo {a c : ℝ} {p : ENNReal} (hc : 0 < c) (hp : p ≠ ⊤)
    (hap : a * p.toReal < 1) : MemLp (fun t : ℝ => t ^ (-a)) p (volume.restrict (Ioo 0 c)) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-a)) (volume.restrict (Ioo 0 c)) :=
    (by fun_prop : Measurable fun t : ℝ => t ^ (-a)).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hmeas
  refine (integrable_norm_rpow_iff hmeas hp0 hp).1 ?_
  refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioo).1
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hc).2 (by linarith : -1 < -a * p.toReal))
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _), ← Real.rpow_mul ht.1.le]

/-- On `(a, b)` with `a < b`, the shifted power `t ↦ (t - a) ^ s` is integrable if and only if
`-1 < s`. -/
theorem integrableOn_Ioo_sub_rpow_iff {a b s : ℝ} (hab : a < b) :
    IntegrableOn (fun t : ℝ ↦ (t - a) ^ s) (Ioo a b) ↔ -1 < s := by
  have heq : (fun x : ℝ ↦ x + a) '' Ioo 0 (b - a) = Ioo a b := by
    rw [image_add_const_Ioo, zero_add, sub_add_cancel]
  rw [← heq, (measurePreserving_add_right volume a).integrableOn_image
    (measurableEmbedding_addRight a)]
  simpa [Function.comp_def, add_sub_cancel_right] using
    intervalIntegral.integrableOn_Ioo_rpow_iff (sub_pos.mpr hab)

end TauCeti
