/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Basic
public import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Weighted coarea on the regular part

For a map differentiable with surjective derivative on a Lebesgue-measurable set, integrating
an extended nonnegative measurable weight along its fibers gives the integral of that weight
times the coarea Jacobian. The fibers carry normalized Euclidean Hausdorff measure.
No Lipschitz hypothesis outside the set, or finiteness of either integral, is required.

The unweighted input is the regular-part coarea identity in
`TauCeti.MeasureTheory.Function.Coarea.Basic`. Measurable-function induction extends it to
weights, using almost-everywhere measurability of fiber integrals from
`TauCeti.MeasureTheory.Function.Coarea.Measurability`. This file does not treat critical points.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 (the coarea formula).
-/

public section

open MeasureTheory Measure Set Filter Module Function
open scoped ENNReal

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}

/-- **Weighted coarea on the regular part.** For a map differentiable with surjective
derivative on a Lebesgue-measurable set, the integral of a nonnegative measurable weight times
the norm determinant of the adjoint derivative equals its iterated integral along fibers.
Both sides may be infinite. -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * g x =
      ∫⁻ y, ∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hJ : Measurable fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet :=
    ENNReal.measurable_ofReal.comp (ContinuousLinearMap.continuous_normDet.measurable.comp
      (ContinuousLinearMap.adjoint.continuous.measurable.comp (measurable_fderiv ℝ f)))
  -- Indicator weights use the set formula; addition and monotone limits give all weights.
  refine Measurable.ennreal_induction ?_ ?_ ?_ hg
  · intro c t ht
    have hweight : (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet *
        t.indicator (fun _ ↦ c) x) =
        t.indicator (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * c) := by
      funext x
      exact (Set.indicator_mul_right t
        (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) (fun _ ↦ c)).symm
    rw [hweight, lintegral_indicator ht, Measure.restrict_restrict ht,
      lintegral_mul_const c hJ]
    simp_rw [lintegral_indicator ht, Measure.restrict_restrict ht, lintegral_const,
      Measure.restrict_apply_univ]
    have hset (y : F) : t ∩ (s ∩ f ⁻¹' {y}) = (s ∩ t) ∩ f ⁻¹' {y} := by ac_rfl
    simp_rw [hset]
    rw [lintegral_const_mul'' c
      (aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt volume
        (hs.inter ht.nullMeasurableSet) (fun x hx ↦ (hdw x hx.1).mono inter_subset_left)),
      lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
        (hs.inter ht.nullMeasurableSet) (fun x hx ↦ hd x hx.1) (fun x hx ↦ hsurj x hx.1),
      inter_comm t s, mul_comm]
  · intro g h hdisj hg hh ihg ihh
    simp_rw [Pi.add_apply, mul_add, lintegral_add_left hg]
    have hprod : Measurable (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * g x) :=
      hJ.mul hg
    rw [lintegral_add_left hprod, ihg, ihh,
      lintegral_add_left'
        (aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs hdw hg)]
  · intro g hg hmono ih
    simp_rw [ENNReal.mul_iSup]
    rw [lintegral_iSup]
    · simp_rw [ih]
      have heq (y : F) :
          (∫⁻ x in s ∩ f ⁻¹' {y}, ⨆ n, g n x ∂μHE[finrank ℝ E - finrank ℝ F]) =
            ⨆ n, ∫⁻ x in s ∩ f ⁻¹' {y}, g n x ∂μHE[finrank ℝ E - finrank ℝ F] :=
        lintegral_iSup hg hmono
      simp_rw [heq]
      exact (lintegral_iSup'
        (fun n ↦ aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs hdw (hg n))
        (Eventually.of_forall fun y i j hij ↦ lintegral_mono (hmono hij))).symm
    · exact fun n ↦ hJ.mul (hg n)
    · intro i j hij x
      exact mul_le_mul' le_rfl (hmono hij x)

end MeasureTheory
