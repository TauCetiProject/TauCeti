/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# The Poisson integral at `i` as a circle average

The substitution `θ = π + 2 arctan x` (`TauCeti.cayleyAngle`), under which
`e^{iθ} = (x - i)/(x + i)` and `dθ = 2 dx / (1 + x ^ 2)`, carries the unit circle onto the real
line. Under it, the circle average of `h ∘ inverseCayleyCoord` over the unit circle is the Poisson
integral `∫ P(i, x) h(x) dx` at `i` (`TauCeti.circleAverage_comp_inverseCayleyCoord`), and
circle integrability of `h ∘ inverseCayleyCoord` gives integrability of `h` for the Poisson measure
`dx / (1 + x ^ 2)` (`TauCeti.integrable_upperHalfPlanePoissonMeasure_of_circleIntegrable`).
-/

public section

noncomputable section

open Complex MeasureTheory Set
open Real (circleAverage circleAverage_def two_pi_pos)
open scoped Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Cayley change of variables.** For `h : ℝ → E`, the circle average of
`h ∘ inverseCayleyCoord` over the unit circle is the Poisson integral `∫ P(i, x) h(x) dx` at `i`. -/
theorem circleAverage_comp_inverseCayleyCoord (h : ℝ → E) :
    circleAverage (fun w ↦ h (inverseCayleyCoord w)) 0 1 =
      ∫ x, upperHalfPlanePoissonKernel I x • h x := by
  have himg := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_cayleyAngle x).hasDerivWithinAt) cayleyAngle_injective.injOn
    (fun θ ↦ h (inverseCayleyCoord (circleMap 0 1 θ)))
  rw [image_univ, range_cayleyAngle, Measure.restrict_univ] at himg
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le,
    integral_Ioc_eq_integral_Ioo, himg, ← integral_smul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [circleMap_zero_one, exp_cayleyAngle_mul_I, inverseCayleyCoord_cayley, ofReal_re,
    smul_smul, upperHalfPlanePoissonKernel_I]
  rw [abs_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Integrability under the Cayley change of variables.** If `h ∘ inverseCayleyCoord` is
integrable on the unit circle, then `h` is integrable for the Poisson measure `dx / (1 + x ^ 2)`. -/
theorem integrable_upperHalfPlanePoissonMeasure_of_circleIntegrable {h : ℝ → E}
    (hh : CircleIntegrable (fun w ↦ h (inverseCayleyCoord w)) 0 1) :
    Integrable h upperHalfPlanePoissonMeasure := by
  have hIoo : IntegrableOn (fun θ ↦ h (inverseCayleyCoord (circleMap 0 1 θ))) (Ioo 0 (2 * π)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hh).mono_set
      Ioo_subset_Ioc_self
  rw [← range_cayleyAngle, ← image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun x _ ↦ (hasDerivAt_cayleyAngle x).hasDerivWithinAt)
    cayleyAngle_injective.injOn, integrableOn_univ] at hIoo
  rw [integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul]
  refine (hIoo.smul (1 / 2 : ℝ)).congr (.of_forall fun x ↦ ?_)
  simp only [Pi.smul_apply, circleMap_zero_one, exp_cayleyAngle_mul_I, inverseCayleyCoord_cayley,
    ofReal_re, smul_smul]
  rw [abs_of_pos (by positivity)]
  congr 1
  ring

end TauCeti
