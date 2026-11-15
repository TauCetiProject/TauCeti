/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Negative powers in `Lᵖ` near the origin

On an interval `(0, c)`, the power `t ↦ t ^ (-a)` is in `Lᵖ` for every finite exponent `p` with
`a p < 1` (`TauCeti.memLp_rpow_neg_restrict_Ioo`). This is the `Lᵖ` form of Mathlib's
`intervalIntegral.integrableOn_Ioo_rpow_iff`. For `a = 1 / 2` it shows that the derivative
`(2 √t)⁻¹` of `t ↦ √t` is in `Lᵖ(0, c)` for `p < 2`.
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

end TauCeti
