/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Basic
public import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Measurable
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

For a real-valued function `h` the coarea Jacobian is the gradient norm `‖Dh‖`. Taking the weight
`1_I(h) ‖Dh‖⁻¹` on the regular set `{Dh ≠ 0}` recovers the volume of the regular part of each
preimage from the level integrals `∫_{{h = t} ∩ {Dh ≠ 0}} ‖Dh‖⁻¹ dHⁿ⁻¹`, for an arbitrary `h`.

## Main results

* `MeasureTheory.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber`: weighted
  coarea on the regular part.
* `MeasureTheory.volume_preimage_inter_setOf_fderiv_ne_zero`: the volume of the regular part of
  `h⁻¹(I)` is the integral of the level integrals over `I`.

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

/-- **The coarea formula for the regular part of a preimage.** For every function `h` and
measurable set `I`, the volume of the regular part `h⁻¹(I) ∩ {Dh ≠ 0}` is the integral over `I`
of the level integrals `∫_{{h = t} ∩ {Dh ≠ 0}} ‖Dh‖⁻¹ dHⁿ⁻¹`. Both sides may be infinite. -/
theorem volume_preimage_inter_setOf_fderiv_ne_zero {h : E → ℝ} {I : Set ℝ}
    (hI : MeasurableSet I) :
    volume (h ⁻¹' I ∩ {x | fderiv ℝ h x ≠ 0}) =
      ∫⁻ t in I, ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
        ∂μHE[finrank ℝ E - 1] := by
  set R := {x | fderiv ℝ h x ≠ 0}
  have hR : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hsurj (x : E) (hx : x ∈ R) : Surjective (fderiv ℝ h x) :=
    surjective_of_ne_zero_of_finrank_eq_one (finrank_self ℝ) (f := (fderiv ℝ h x).toLinearMap)
      ((ContinuousLinearMap.coe_injective.ne_iff' ContinuousLinearMap.toLinearMap_zero).2 hx)
  have hm : MeasurableSet (h ⁻¹' I ∩ R) :=
    TauCeti.measurableSet_preimage_inter_setOf_fderiv_ne_zero hI
  -- The weight `1_I(h) ‖Dh‖⁻¹` on the regular set.
  let w : E → ℝ≥0∞ := (h ⁻¹' I ∩ R).indicator fun x ↦ ‖fderiv ℝ h x‖ₑ⁻¹
  have hw : Measurable w := (measurable_fderiv ℝ h).enorm.inv.indicator hm
  have hcoarea := lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hR.nullMeasurableSet (fun _ hx ↦ TauCeti.differentiableAt_of_fderiv_ne_zero hx) hsurj hw
  rw [finrank_self] at hcoarea
  -- On `R` the coarea Jacobian `‖Dh‖` cancels the weight.
  have hlhs : ∫⁻ x in R, ENNReal.ofReal (fderiv ℝ h x).adjoint.normDet * w x =
      ∫⁻ x in R, (h ⁻¹' I ∩ R).indicator 1 x := by
    refine setLIntegral_congr_fun hR fun x hx ↦ ?_
    dsimp only [w]
    by_cases hxI : x ∈ h ⁻¹' I ∩ R
    · rw [indicator_of_mem hxI, indicator_of_mem hxI,
        ContinuousLinearMap.normDet_adjoint_eq_norm, Pi.one_apply, ofReal_norm]
      exact ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 hx)) (by simp)
    · rw [indicator_of_notMem hxI, indicator_of_notMem hxI, mul_zero]
  -- On the fiber over `t` the weight is `‖Dh‖⁻¹` if `t ∈ I` and zero otherwise.
  have hrhs (t : ℝ) : ∫⁻ x in R ∩ h ⁻¹' {t}, w x ∂μHE[finrank ℝ E - 1] =
      I.indicator (fun t ↦ ∫⁻ x in R ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) t := by
    have hfib : MeasurableSet (R ∩ h ⁻¹' {t}) := by
      rw [inter_comm]
      exact TauCeti.measurableSet_preimage_inter_setOf_fderiv_ne_zero (measurableSet_singleton t)
    dsimp only [w]
    by_cases htI : t ∈ I
    · rw [indicator_of_mem htI]
      refine setLIntegral_congr_fun hfib fun x hx ↦ ?_
      have hxt : h x = t := hx.2
      have hxI : x ∈ h ⁻¹' I ∩ R := ⟨by rwa [mem_preimage, hxt], hx.1⟩
      exact indicator_of_mem hxI _
    · rw [indicator_of_notMem htI]
      refine (setLIntegral_congr_fun hfib fun x hx ↦ ?_).trans lintegral_zero
      have hxt : h x = t := hx.2
      have hxI : x ∉ h ⁻¹' I ∩ R := fun h' ↦ htI (hxt ▸ h'.1)
      exact indicator_of_notMem hxI _
  rw [hlhs, lintegral_indicator_one hm, restrict_apply hm, inter_assoc, inter_self] at hcoarea
  rw [hcoarea, lintegral_congr hrhs]
  exact lintegral_indicator hI _

end MeasureTheory
