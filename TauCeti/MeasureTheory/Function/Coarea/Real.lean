/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Real-valued weighted coarea on the regular part

When the nonnegative Jacobian-weighted function is integrable, almost every fiber integral
is finite. The weighted coarea formula then becomes an equality of ordinary real integrals.
We supply both the fiberwise and outer integrability statements, so the real formula does not
rely on the value assigned to a divergent Bochner integral. The finiteness passage parallels
the weighted area formulas in `TauCeti.MeasureTheory.Function.AreaFormula.Real`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 (the coarea formula).
-/

public section

open MeasureTheory Measure Set Filter Module Function
open scoped ENNReal NNReal

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E} {g : E → ℝ≥0}

/-- An integrable nonnegative weighted coarea Jacobian has finite iterated fiber integral. -/
theorem lintegral_setLIntegral_fiber_ne_top_of_integrable_normDet_adjoint_fderiv_mul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * (g x : ℝ)) s) :
    ∫⁻ y, ∫⁻ x in s ∩ f ⁻¹' {y}, (g x : ℝ≥0∞) ∂μHE[finrank ℝ E - finrank ℝ F] ≠ ∞ := by
  rw [← lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs hd hsurj
    hg.coe_nnreal_ennreal]
  simpa only [ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), ENNReal.ofReal_coe_nnreal]
    using hint.lintegral_lt_top.ne

/-- Integrability of the weighted coarea Jacobian implies integrability of the weight on
almost every fiber, with respect to normalized Hausdorff measure. -/
theorem ae_integrableOn_fiber_of_integrable_normDet_adjoint_fderiv_mul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * (g x : ℝ)) s) :
    ∀ᵐ y, IntegrableOn (fun x ↦ (g x : ℝ)) (s ∩ f ⁻¹' {y})
      μHE[finrank ℝ E - finrank ℝ F] := by
  have hG := aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs
    (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt) hg.coe_nnreal_ennreal
  have hfinite :=
    lintegral_setLIntegral_fiber_ne_top_of_integrable_normDet_adjoint_fderiv_mul hs hd hsurj hg hint
  filter_upwards [ae_lt_top' hG hfinite] with y hy
  simpa only [IntegrableOn, ENNReal.coe_toReal] using
    integrable_toReal_of_lintegral_ne_top hg.coe_nnreal_ennreal.aemeasurable hy.ne

/-- The real fiber integrals are integrable on the target when the nonnegative weighted
coarea Jacobian is integrable. -/
theorem integrable_setIntegral_fiber_of_integrable_normDet_adjoint_fderiv_mul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * (g x : ℝ)) s) :
    Integrable (fun y ↦ ∫ x in s ∩ f ⁻¹' {y}, (g x : ℝ)
      ∂μHE[finrank ℝ E - finrank ℝ F]) volume := by
  have hG := aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs
    (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt) hg.coe_nnreal_ennreal
  have hfinite :=
    lintegral_setLIntegral_fiber_ne_top_of_integrable_normDet_adjoint_fderiv_mul hs hd hsurj hg hint
  refine (integrable_toReal_of_lintegral_ne_top hG hfinite).congr ?_
  exact Eventually.of_forall fun y ↦ by
    simpa only [ENNReal.coe_toReal] using
      (integral_toReal hg.coe_nnreal_ennreal.aemeasurable
        (Eventually.of_forall fun _ ↦ ENNReal.coe_lt_top)).symm

/-- **Real weighted coarea on the regular part.** An integrable nonnegative weighted
Jacobian integrates to the iterated real integral of the weight along fibers. The fiber
integrals are integrable almost everywhere, and the outer integrand is integrable. -/
theorem integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_fiber
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * (g x : ℝ)) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet * (g x : ℝ) =
      ∫ y, ∫ x in s ∩ f ⁻¹' {y}, (g x : ℝ) ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have houter :=
    integrable_setIntegral_fiber_of_integrable_normDet_adjoint_fderiv_mul hs hd hsurj hg hint
  have hfiber :=
    ae_integrableOn_fiber_of_integrable_normDet_adjoint_fderiv_mul hs hd hsurj hg hint
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x ↦ mul_nonneg (LinearMap.normDet_nonneg _) (g x).coe_nonneg)
      hint.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y ↦ integral_nonneg fun x ↦ (g x).coe_nonneg)
      houter.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs hd hsurj
    hg.coe_nnreal_ennreal]
  exact lintegral_congr_ae (hfiber.mono fun y hy ↦ lintegral_coe_eq_integral g hy)

end MeasureTheory
