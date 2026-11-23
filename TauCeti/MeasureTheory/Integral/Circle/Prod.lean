/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Fubini's theorem for circle averages

Let `F : ℂ → ℂ → E` be a function whose pullback
`(θ, φ) ↦ F (circleMap c R θ) (circleMap c' R' φ)` along the two angle parametrizations is
integrable on `(0, 2π] × (0, 2π]`. Then the inner circle average
`z ↦ circleAverage (F z) c' R'` is circle integrable, and the two iterated circle averages agree:

`circleAverage (fun z ↦ circleAverage (F z) c' R') c R =`
`circleAverage (fun w ↦ circleAverage (fun z ↦ F z w) c R) c' R'`.

The integrability hypothesis holds in particular when `F` is jointly continuous on the product of
circles `sphere c |R| ×ˢ sphere c' |R'|`.

Iterated circle averages of this kind arise when a kernel representation over one circle is
averaged over a second circle, as in Cartan's formula for the proximity function and in the
estimate of the proximity function of a logarithmic derivative.

## Main results

* `MeasureTheory.IntegrableOn.circleIntegrable_circleAverage`: the inner circle average is circle
  integrable.
* `TauCeti.circleAverage_circleAverage_swap`: the order of two circle averages can be exchanged.
* `ContinuousOn.integrableOn_uncurry_circleMap`: joint continuity on a product of circles gives the
  integrability hypothesis of both results.

## Implementation notes

The statements reduce to the marginal integrability `MeasureTheory.Integrable.integral_prod_left`
and Fubini's theorem for interval integrals, `MeasureTheory.intervalIntegral_intervalIntegral_swap`.
-/

public section

open MeasureTheory Metric Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℂ → ℂ → E} {c c' : ℂ}
  {R R' : ℝ}

namespace MeasureTheory.IntegrableOn

/-- If the pullback of `F` along the two angle parametrizations is integrable on
`(0, 2π] × (0, 2π]`, then the inner circle average `z ↦ circleAverage (F z) c' R'` is circle
integrable over `sphere c |R|`. -/
theorem circleIntegrable_circleAverage
    (hF : IntegrableOn (Function.uncurry fun θ φ ↦ F (circleMap c R θ) (circleMap c' R' φ))
      (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π))) :
    CircleIntegrable (fun z ↦ circleAverage (F z) c' R') c R := by
  rw [uIoc_of_le two_pi_pos.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    at hF
  -- Each inner circle average is a normalized set integral over `(0, 2π]`.
  have h_avg : ∀ θ, circleAverage (F (circleMap c R θ)) c' R' =
      (2 * π)⁻¹ • ∫ φ in Ioc 0 (2 * π), F (circleMap c R θ) (circleMap c' R' φ) := by
    intro θ
    rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le]
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
  exact IntegrableOn.congr_fun (hF.integral_prod_left.smul (2 * π)⁻¹)
    (fun θ _ ↦ (h_avg θ).symm) measurableSet_Ioc

end MeasureTheory.IntegrableOn

namespace TauCeti

/-- **Fubini's theorem for circle averages.** If the pullback of `F` along the two angle
parametrizations is integrable on `(0, 2π] × (0, 2π]`, then the two iterated circle averages of
`F` agree. -/
theorem circleAverage_circleAverage_swap
    (hF : IntegrableOn (Function.uncurry fun θ φ ↦ F (circleMap c R θ) (circleMap c' R' φ))
      (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π))) :
    circleAverage (fun z ↦ circleAverage (F z) c' R') c R =
      circleAverage (fun w ↦ circleAverage (fun z ↦ F z w) c R) c' R' := by
  simp only [circleAverage_def, intervalIntegral.integral_smul]
  rw [intervalIntegral_intervalIntegral_swap hF]

end TauCeti

namespace ContinuousOn

omit [NormedSpace ℝ E] in
/-- If `F` is jointly continuous on `sphere c |R| ×ˢ sphere c' |R'|`, then its pullback along the
two angle parametrizations is integrable on `(0, 2π] × (0, 2π]`. -/
theorem integrableOn_uncurry_circleMap
    (hF : ContinuousOn (Function.uncurry F) (sphere c |R| ×ˢ sphere c' |R'|)) :
    IntegrableOn (Function.uncurry fun θ φ ↦ F (circleMap c R θ) (circleMap c' R' φ))
      (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π)) :=
  (hF.continuous_uncurry_circleMap.continuousOn.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc)).mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

end ContinuousOn
