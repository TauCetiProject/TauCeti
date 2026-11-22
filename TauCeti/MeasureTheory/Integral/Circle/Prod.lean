/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini's theorem for circle averages

For a function `F : ℂ → ℂ → E` that is jointly continuous on the product of two circles
`sphere c |R| ×ˢ sphere c' |R'|`, the inner circle average `z ↦ circleAverage (F z) c' R'` is
circle integrable, and the two iterated circle averages agree:

`circleAverage (fun z ↦ circleAverage (F z) c' R') c R =`
`circleAverage (fun w ↦ circleAverage (fun z ↦ F z w) c R) c' R'`.

Iterated circle averages of this kind arise when a kernel representation over one circle is
averaged over a second, concentric circle, as in the estimate of the proximity function of a
logarithmic derivative.

## Main results

* `Real.circleIntegrable_circleAverage`: the inner circle average is circle integrable.
* `Real.circleAverage_circleAverage_swap`: the order of two circle averages can be exchanged.

## Implementation notes

Pulled back along `circleMap`, the integrand is a continuous function on `ℝ × ℝ`, so the
statements reduce to the parametric continuity
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` and Fubini's theorem
for interval integrals, `MeasureTheory.intervalIntegral_intervalIntegral_swap`.
-/

public section

open MeasureTheory Metric Set

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℂ → ℂ → E} {c c' : ℂ}
  {R R' : ℝ}

omit [NormedSpace ℝ E] in
/-- The pullback of a function jointly continuous on a product of circles along the two angle
parametrizations is continuous on `ℝ × ℝ`. -/
private theorem continuous_uncurry_circleMap
    (hF : ContinuousOn (Function.uncurry F) (sphere c |R| ×ˢ sphere c' |R'|)) :
    Continuous (Function.uncurry fun θ φ ↦ F (circleMap c R θ) (circleMap c' R' φ)) :=
  hF.comp_continuous (f := fun p : ℝ × ℝ ↦ (circleMap c R p.1, circleMap c' R' p.2))
    (by fun_prop) fun p ↦ ⟨circleMap_mem_sphere' c R p.1, circleMap_mem_sphere' c' R' p.2⟩

/-- If `F` is jointly continuous on `sphere c |R| ×ˢ sphere c' |R'|`, then the inner circle
average `z ↦ circleAverage (F z) c' R'` is circle integrable over `sphere c |R|`. -/
theorem circleIntegrable_circleAverage
    (hF : ContinuousOn (Function.uncurry F) (sphere c |R| ×ˢ sphere c' |R'|)) :
    CircleIntegrable (fun z ↦ circleAverage (F z) c' R') c R := by
  simp only [CircleIntegrable, circleAverage_def]
  exact ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_uncurry_circleMap hF) 0 (2 * π)).const_smul _).intervalIntegrable _ _

/-- **Fubini's theorem for circle averages.** If `F` is jointly continuous on
`sphere c |R| ×ˢ sphere c' |R'|`, then the two iterated circle averages of `F` agree. -/
theorem circleAverage_circleAverage_swap
    (hF : ContinuousOn (Function.uncurry F) (sphere c |R| ×ˢ sphere c' |R'|)) :
    circleAverage (fun z ↦ circleAverage (F z) c' R') c R =
      circleAverage (fun w ↦ circleAverage (fun z ↦ F z w) c R) c' R' := by
  have hG := continuous_uncurry_circleMap hF
  have hint : IntegrableOn
      (Function.uncurry fun θ φ ↦ F (circleMap c R θ) (circleMap c' R' φ))
      (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π)) :=
    (hG.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  simp only [circleAverage_def, intervalIntegral.integral_smul]
  rw [intervalIntegral_intervalIntegral_swap hint]

end Real
