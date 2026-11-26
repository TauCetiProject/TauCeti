/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Basic
public import TauCeti.MeasureTheory.Function.Coarea.Measurability
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Weighted and Bochner coarea on the regular part

For a map differentiable with surjective derivative on a Lebesgue-measurable set, integrating
an extended nonnegative almost-everywhere measurable weight along its fibers gives the integral of
that weight times the coarea Jacobian. The fibers carry normalized Euclidean Hausdorff measure.
No Lipschitz hypothesis outside the set, or finiteness of either integral, is required.
Adapting `MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` in
`Mathlib.MeasureTheory.Function.Jacobian`, this yields a Radon-Nikodym pushforward identity:
pushing forward `(volume.restrict s).withDensity (ENNReal.ofReal (J f ·) * w ·)` under `f` produces
`volume` weighted by the fiber Hausdorff integrals of `w`.

For a Banach-space-valued integrand `g : E → V` into any real normed space `V`, if the
Jacobian-weighted integrand `x ↦ (fderiv ℝ f x)†.normDet • g x` is Bochner integrable on the
regular set `s`, then `g` is Hausdorff integrable on almost every fiber `s ∩ f ⁻¹' {y}`, the fiber
integrals are Bochner integrable on `F`, and
`∫ x in s, (fderiv ℝ f x)†.normDet • g x = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[n - m]`.
Neither completeness of `V` nor a separate measurability assumption on `g` is required: on `s` the
coarea Jacobian is everywhere nonzero, so almost-everywhere strong measurability of `J f • g`
recovers that of `g`.

The unweighted input is the regular-part coarea identity in
`TauCeti.MeasureTheory.Function.Coarea.Basic`. Measurable-function induction, `Integrable.induction`
against the Jacobian density, and ambient-to-fiber almost-everywhere descent extend it to
almost-everywhere measurable weights and Bochner-integrable vector-valued functions, using
`TauCeti.MeasureTheory.Function.Coarea.Measurability`. This file does not treat critical points.

For a real-valued function `h` the coarea Jacobian is the gradient norm `‖Dh‖`. Taking the weight
`1_I(h) ‖Dh‖⁻¹` on the regular set `{Dh ≠ 0}` recovers the volume of the regular part of each
preimage from the level integrals `∫_{{h = t} ∩ {Dh ≠ 0}} ‖Dh‖⁻¹ dHⁿ⁻¹`, for an arbitrary `h`.

## Main results

* `MeasureTheory.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber`: weighted
  coarea on the regular part.
* `MeasureTheory.map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber`,
  `map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure_inter_preimage`:
  Radon-Nikodym pushforward forms of regular-part coarea.
* `MeasureTheory.ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul`,
  `MeasureTheory.integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul`,
  `MeasureTheory.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber`,
  `MeasureTheory.integral_norm_setIntegral_fiber_le_of_integrableOn_normDet_adjoint_fderiv_smul`:
  fiberwise integrability, outer integrability, the Banach-space Bochner coarea formula, and its
  triangle-inequality bound on the regular part.
* `MeasureTheory.volume_preimage_inter_setOf_fderiv_ne_zero`: the volume of the regular part of
  `h⁻¹(I)` is the integral of the level integrals over `I`.
* `MeasureTheory.lintegral_comp_norm_fderiv_eq_lintegral_setLIntegral`: a gradient integral
  `∫ G(‖Dh‖)` with `G 0 = 0` is the integral over levels of `∫_{{h = t} ∩ {Dh ≠ 0}} G(‖Dh‖) ‖Dh‖⁻¹`.
* `ConvexOn.lintegral_ofReal_comp_norm_fderiv_eq_lintegral_setLIntegral`: the same identity for
  `G = ENNReal.ofReal ∘ Φ` with `Φ` convex on `[0, ∞)` and `Φ 0 ≤ 0`, where measurability of `G`
  comes from convexity.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 (the coarea formula).
-/

public section

open MeasureTheory Measure Set Filter Module Function Topology
open scoped ENNReal NNReal

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}

/-- Weighted coarea on the regular part for a Borel-measurable nonnegative weight. -/
private theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber_of_measurable
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * g x =
      ∫⁻ y, ∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hJ : Measurable fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet :=
    TauCeti.measurable_ofReal_normDet_adjoint_fderiv f
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
    simp_rw [lintegral_indicator_const ht, Measure.restrict_inter_apply _ _ _ ht]
    rw [lintegral_const_mul'' c
      (aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt volume
        (hs.inter ht.nullMeasurableSet) (fun x hx ↦ (hdw x hx.1).mono inter_subset_left)),
      lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
        (hs.inter ht.nullMeasurableSet) (fun x hx ↦ hd x hx.1) (fun x hx ↦ hsurj x hx.1),
      inter_comm t s, mul_comm]
  · intro g h _ hg _ ihg ihh
    simp_rw [Pi.add_apply, mul_add, lintegral_add_left hg]
    have hprod : Measurable (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * g x) :=
      hJ.mul hg
    rw [lintegral_add_left hprod, ihg, ihh,
      lintegral_add_left' (aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs hdw
        hg.aemeasurable.restrict)]
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
        (fun n ↦ aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs hdw
          (hg n).aemeasurable.restrict)
        (Eventually.of_forall fun y i j hij ↦ lintegral_mono (hmono hij))).symm
    · exact fun n ↦ hJ.mul (hg n)
    · intro i j hij x
      exact mul_le_mul' le_rfl (hmono hij x)

/-- **Weighted coarea on the regular part.** For a map differentiable with surjective
derivative on a Lebesgue-measurable set, the integral of a nonnegative almost-everywhere measurable
weight times the norm determinant of the adjoint derivative equals its iterated integral along
fibers. Both sides may be infinite. -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {g : E → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict s)) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * g x =
      ∫⁻ y, ∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hlhs : ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * g x =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * hg.mk g x :=
    lintegral_congr_ae (hg.ae_eq_mk.mono fun x hx ↦ congr_arg _ hx)
  have hrhs : (∫⁻ y, ∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) =
      ∫⁻ y, ∫⁻ x in s ∩ f ⁻¹' {y}, hg.mk g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
    lintegral_congr_ae ((ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt volume hdw
      hg.ae_eq_mk).mono fun _ hy ↦ lintegral_congr_ae hy)
  rw [hlhs, hrhs]
  exact lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber_of_measurable
    hs hd hsurj hg.measurable_mk

/-- Disintegration of Jacobian-weighted volume on the regular locus (adapting
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` in
`Mathlib.MeasureTheory.Function.Jacobian`): pushing forward
`(volume.restrict s).withDensity (ENNReal.ofReal (J f ·) * w ·)` under `f` produces `volume`
weighted by the fiber Hausdorff integrals of `w`. -/
theorem map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {w : E → ℝ≥0∞}
    (hw : AEMeasurable w (volume.restrict s)) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x) =
      volume.withDensity fun y ↦
        ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have h'f : AEMeasurable f (volume.restrict s) :=
    ContinuousOn.aemeasurable₀ (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt) hs
  have h''f : AEMeasurable f ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x) :=
    h'f.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext fun t ht ↦ ?_
  have h't : NullMeasurableSet (f ⁻¹' t) (volume.restrict s) := h'f.nullMeasurableSet_preimage ht
  rw [map_apply_of_aemeasurable h''f ht, withDensity_apply₀ _ h't, withDensity_apply _ ht,
    restrict_restrict₀ h't,
    lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
      ((nullMeasurableSet_restrict hs).1 h't) (fun x hx ↦ hd x hx.2) (fun x hx ↦ hsurj x hx.2)
      (hw.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)),
    ← lintegral_indicator ht]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ t
  · have hset : (f ⁻¹' t ∩ s) ∩ f ⁻¹' {y} = s ∩ f ⁻¹' {y} := by
      ext x; simp; grind
    rw [indicator_of_mem hy, hset]
  · have hset : (f ⁻¹' t ∩ s) ∩ f ⁻¹' {y} = ∅ := by
      ext x; simp; grind
    rw [indicator_of_notMem hy, hset, Measure.restrict_empty, lintegral_zero_measure]

/-- Unweighted Radon-Nikodym form of coarea on the regular locus: pushing forward
`(volume.restrict s).withDensity (ENNReal.ofReal (J f ·))` under `f` yields `volume` weighted by the
fiber Hausdorff measures `y ↦ μHE[dim E - dim F] (s ∩ f ⁻¹' {y})`. -/
theorem
    map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure_inter_preimage
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      volume.withDensity fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) := by
  simpa using map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber hs hd
    hsurj (aemeasurable_const (b := (1 : ℝ≥0∞)))

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
  have hw : Measurable w := (measurable_fderiv ℝ h).eNorm.inv.indicator hm
  have hcoarea := lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hR.nullMeasurableSet (fun _ hx ↦ TauCeti.differentiableAt_of_fderiv_ne_zero hx) hsurj
    hw.aemeasurable.restrict
  rw [finrank_self] at hcoarea
  -- On `R` the coarea Jacobian `‖Dh‖` cancels the weight.
  have hlhs : ∫⁻ x in R, ENNReal.ofReal (fderiv ℝ h x).adjoint.normDet * w x =
      ∫⁻ x in R, (h ⁻¹' I ∩ R).indicator 1 x := by
    refine setLIntegral_congr_fun hR fun x hx ↦ ?_
    dsimp only [w]
    by_cases hxI : x ∈ h ⁻¹' I ∩ R
    · rw [indicator_of_mem hxI, indicator_of_mem hxI,
        ContinuousLinearMap.normDet_adjoint_eq_norm, Pi.one_apply, ofReal_norm]
      exact ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 hx)) (by simp)
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

/-- **Gradient integrals as integrals over levels.** For every function `h : E → ℝ` and every
measurable `G : ℝ → ℝ≥0∞` with `G 0 = 0`, the integral of `G (‖Dh‖)` is the integral over the
levels `t` of `∫_{{h = t} ∩ {Dh ≠ 0}} G (‖Dh‖) ‖Dh‖⁻¹ dHⁿ⁻¹`. No regularity of `h` is needed:
the critical set `{Dh = 0}`, which includes the nondifferentiability points, does not contribute.
Both sides may be infinite. -/
theorem lintegral_comp_norm_fderiv_eq_lintegral_setLIntegral {h : E → ℝ} {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) (hG0 : G 0 = 0) :
    ∫⁻ x, G ‖fderiv ℝ h x‖ =
      ∫⁻ t, ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        G ‖fderiv ℝ h x‖ * ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] := by
  set R := {x | fderiv ℝ h x ≠ 0}
  have hR : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hsurj (x : E) (hx : x ∈ R) : Surjective (fderiv ℝ h x) :=
    surjective_of_ne_zero_of_finrank_eq_one (finrank_self ℝ) (f := (fderiv ℝ h x).toLinearMap)
      ((ContinuousLinearMap.coe_injective.ne_iff' ContinuousLinearMap.toLinearMap_zero).2 hx)
  have hw : Measurable fun x ↦ G ‖fderiv ℝ h x‖ * ‖fderiv ℝ h x‖ₑ⁻¹ :=
    (hG.comp (measurable_fderiv ℝ h).norm).mul (measurable_fderiv ℝ h).eNorm.inv
  have hcoarea := lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hR.nullMeasurableSet (fun _ hx ↦ TauCeti.differentiableAt_of_fderiv_ne_zero hx) hsurj
    hw.aemeasurable.restrict
  rw [finrank_self] at hcoarea
  rw [← hcoarea, ← setLIntegral_eq_of_support_subset (s := R) fun x hx ↦ ?_]
  · -- On `R` the coarea Jacobian `‖Dh‖` cancels the weight `‖Dh‖⁻¹`.
    refine setLIntegral_congr_fun hR fun x (hx : fderiv ℝ h x ≠ 0) ↦ ?_
    have hx0 : ‖fderiv ℝ h x‖ₑ ≠ 0 := ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 hx)
    rw [ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm, mul_left_comm,
      ENNReal.mul_inv_cancel hx0 (by simp), mul_one]
  · -- Off `R` the integrand is `G 0 = 0`.
    by_contra hxR
    exact hx (by simp_all [R])

/-- **Convex gradient integrals as integrals over levels.** For every function `h : E → ℝ` and
every `Φ` convex on `[0, ∞)` with `Φ 0 ≤ 0`, the integral of the positive part of `Φ (‖Dh‖)` is
the integral over the levels `t` of `∫_{{h = t} ∩ {Dh ≠ 0}} Φ (‖Dh‖)⁺ ‖Dh‖⁻¹ dHⁿ⁻¹`. This is
`lintegral_comp_norm_fderiv_eq_lintegral_setLIntegral` with measurability supplied by the
continuity of `Φ` on `(0, ∞)`. Both sides may be infinite. -/
theorem _root_.ConvexOn.lintegral_ofReal_comp_norm_fderiv_eq_lintegral_setLIntegral {h : E → ℝ}
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) =
      ∫⁻ t, ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) * ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] := by
  classical
  -- A measurable function agreeing with `ENNReal.ofReal ∘ Φ` on `[0, ∞)`.
  set G : ℝ → ℝ≥0∞ := (Ioi 0).piecewise (fun s ↦ ENNReal.ofReal (Φ s)) 0
  have hG (s : ℝ) (hs : 0 ≤ s) : G s = ENNReal.ofReal (Φ s) := by
    rcases hs.eq_or_lt with rfl | hs
    · simp [G, ENNReal.ofReal_eq_zero.2 hΦ0]
    · exact piecewise_eq_of_mem _ _ _ hs
  have hGm : Measurable G := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ioi
    have hcont := hΦ.continuousOn_interior
    rw [interior_Ici] at hcont
    exact ENNReal.continuous_ofReal.comp_continuousOn hcont
  have key := lintegral_comp_norm_fderiv_eq_lintegral_setLIntegral (h := h) hGm
    ((hG 0 le_rfl).trans (ENNReal.ofReal_eq_zero.2 hΦ0))
  simp_rw [hG _ (norm_nonneg _)] at key
  exact key

section RegularBochner

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {g : E → V}

omit [MeasurableSpace F] [BorelSpace F] in
/-- On a Lebesgue-measurable set where `fderiv ℝ f` is surjective, almost-everywhere strong
measurability of the Jacobian-weighted integrand `(fderiv ℝ f x)†.normDet • g x` implies
almost-everywhere strong measurability of `g`, since the scalar factor `(fderiv ℝ f x)†.normDet` is
measurable and everywhere nonzero on `s`. -/
private theorem aestronglyMeasurable_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hgm : AEStronglyMeasurable (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x)
      (volume.restrict s)) :
    AEStronglyMeasurable g (volume.restrict s) :=
  (aestronglyMeasurable_fun_smul_iff₀
    (TauCeti.measurable_normDet_adjoint_fderiv f).aestronglyMeasurable.restrict
    ((ae_restrict_mem₀ hs).mono fun x hx ↦
      ContinuousLinearMap.normDet_adjoint_ne_zero_iff.2 (hsurj x hx))).1 hgm

omit [MeasurableSpace F] [BorelSpace F] in
/-- Integrability against the coarea Jacobian density `(volume.restrict s).withDensity ...` is
equivalent to `IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • u x) s`. -/
private theorem integrable_withDensity_normDet_adjoint_fderiv_iff {u : E → V} :
    Integrable u ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) ↔
      IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • u x) s := by
  rw [integrable_withDensity_iff_integrable_smul'
    (TauCeti.measurable_ofReal_normDet_adjoint_fderiv f)
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [IntegrableOn, ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)]

omit [MeasurableSpace F] [BorelSpace F] in
/-- Integrability with respect to `(volume.restrict s).withDensity (ENNReal.ofReal (J f ·))` on the
regular locus `s` implies `volume.restrict s`-almost-everywhere strong measurability. -/
private theorem aestronglyMeasurable_of_integrable_withDensity
    (hs : NullMeasurableSet s volume) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {u : E → V}
    (hu : Integrable u ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet)) :
    AEStronglyMeasurable u (volume.restrict s) :=
  aestronglyMeasurable_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul hs hsurj
    (integrable_withDensity_normDet_adjoint_fderiv_iff.1 hu).aestronglyMeasurable

/-- Almost-everywhere strong measurability of the Bochner fiber integral on the regular locus when
the Jacobian-weighted integrand is almost everywhere strongly measurable on `s`. -/
theorem
    aestronglyMeasurable_setIntegral_fiber_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hgm : AEStronglyMeasurable (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x)
      (volume.restrict s)) :
    AEStronglyMeasurable
      (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  aestronglyMeasurable_setIntegral_fiber_of_hasFDerivWithinAt volume hs
    (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt)
    (aestronglyMeasurable_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul hs hsurj hgm)

/-- Integrability of `(fderiv ℝ f x)†.normDet • g x` on the regular locus `s` implies
`μHE[dim E - dim F]`-integrability of `g` on almost every fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] := by
  have hgm : AEStronglyMeasurable g (volume.restrict s) :=
    aestronglyMeasurable_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul hs hsurj
      hint.aestronglyMeasurable
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hco := lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs hd hsurj
    hgm.eNorm
  have hfin : (∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, ‖g x‖ₑ ∂μHE[finrank ℝ E - finrank ℝ F]) ≠ ∞ := by
    rw [← hco]
    refine (lintegral_congr fun x ↦ ?_).symm.trans_lt hint.hasFiniteIntegral |>.ne
    rw [eNorm_smul, Real.eNorm_of_nonneg (LinearMap.normDet_nonneg _)]
  filter_upwards [ae_aestronglyMeasurable_restrict_preimage_of_hasFDerivWithinAt volume hdw hgm,
    ae_lt_top' (aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs hdw hgm.eNorm)
      hfin] with y hy_meas hy_fin
  exact ⟨hy_meas, hy_fin⟩

/-- For an `L¹` function `u` with respect to `(volume.restrict s).withDensity w`, the `L¹` norm of
`u` equals the iterated fiber `L¹` integral of `u` when `s` lies in the regular locus. -/
private theorem lintegral_setLIntegral_enorm_eq_lintegral_withDensity
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {u : E → V}
    (hu : Integrable u ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet)) :
    (∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, ‖u x‖ₑ ∂μHE[finrank ℝ E - finrank ℝ F]) =
      ∫⁻ x, ‖u x‖ₑ ∂(volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  have hum : AEStronglyMeasurable u (volume.restrict s) :=
    aestronglyMeasurable_of_integrable_withDensity hs hsurj hu
  rw [← lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs hd hsurj hum.eNorm,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (TauCeti.measurable_ofReal_normDet_adjoint_fderiv f)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]

/-- Bochner integrability of the fiber integrals `y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]`
on the regular locus when `(fderiv ℝ f x)†.normDet • g x` is integrable on `s`. -/
theorem integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume := by
  have hgν := integrable_withDensity_normDet_adjoint_fderiv_iff.2 hint
  exact ⟨aestronglyMeasurable_setIntegral_fiber_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul
      hs hd hsurj hint.aestronglyMeasurable,
    (lintegral_mono fun _ ↦ eNorm_integral_le_lintegral_eNorm _).trans_lt
      ((lintegral_setLIntegral_enorm_eq_lintegral_withDensity hs hd hsurj hgν).trans_lt
        hgν.hasFiniteIntegral)⟩

/-- Indicator case of the regular-locus Bochner coarea induction. -/
private theorem integral_withDensity_eq_indicator [CompleteSpace V]
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) (c : V) {t : Set E} (ht : MeasurableSet t)
    (hνt : ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) t < ∞) :
    ∫ x, t.indicator (fun _ ↦ c) x ∂((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, t.indicator (fun _ ↦ c) x
        ∂μHE[finrank ℝ E - finrank ℝ F] := by
  set k := finrank ℝ E - finrank ℝ F
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hm : AEMeasurable (fun y : F ↦ μHE[k] ((s ∩ t) ∩ f ⁻¹' {y})) volume :=
    aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt volume
      (hs.inter ht.nullMeasurableSet) fun x hx ↦ (hdw x hx.1).mono inter_subset_left
  have hco : ∫⁻ y : F, μHE[k] ((s ∩ t) ∩ f ⁻¹' {y}) =
      ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) t := by
    rw [withDensity_apply _ ht, Measure.restrict_restrict ht, inter_comm t s]
    exact lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      (hs.inter ht.nullMeasurableSet) (fun x hx ↦ hd x hx.1) (fun x hx ↦ hsurj x hx.1)
  have hfib (y : F) : (∫ x in s ∩ f ⁻¹' {y}, t.indicator (fun _ ↦ c) x ∂μHE[k]) =
      μHE[k].real ((s ∩ t) ∩ f ⁻¹' {y}) • c := by
    rw [integral_indicator ht, Measure.restrict_inter_restrict _ _ _ ht, setIntegral_const]
  simp_rw [hfib]
  have hfin : ∀ᵐ y : F, μHE[k] ((s ∩ t) ∩ f ⁻¹' {y}) < ∞ :=
    ae_lt_top' hm (hco.trans_lt hνt).ne
  simp only [measureReal_def]
  rw [integral_indicator ht, setIntegral_const, integral_smul_const,
    integral_toReal hm hfin, hco, measureReal_def]

/-- Closedness in `L¹(ν)` of the class of functions satisfying the Bochner coarea identity on the
regular locus. -/
private theorem isClosed_L1_integral_withDensity_eq
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {ν : Measure E}
    (hν : ν = (volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) :
    IsClosed {u : E →₁[ν] V |
      ∫ x, u x ∂ν = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, u x ∂μHE[finrank ℝ E - finrank ℝ F]} := by
  subst hν
  set ν := (volume.restrict s).withDensity
    fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet
  set k := finrank ℝ E - finrank ℝ F
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have h_int (v : E →₁[ν] V) : Integrable v ν := memLp_one_iff_integrable.1 (Lp.memLp v)
  refine isClosed_of_closure_subset fun a ha ↦ ?_
  obtain ⟨u, huP, hu_lim⟩ := mem_closure_iff_seq_limit.1 ha
  have hL1 : Tendsto (fun n ↦ ∫⁻ x, ‖u n x - a x‖ₑ ∂ν) atTop (𝓝 0) := by
    simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm',
      eLpNorm_one_eq_lintegral_eNorm ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable a)),
      Pi.sub_apply] using hu_lim
  set D : ℕ → F → ℝ≥0∞ := fun n y ↦ ∫⁻ x in s ∩ f ⁻¹' {y}, ‖u n x - a x‖ₑ ∂μHE[k]
  have hD_lim : Tendsto (fun n ↦ ∫⁻ y, D n y) atTop (𝓝 0) :=
    hL1.congr fun n ↦ (lintegral_setLIntegral_enorm_eq_lintegral_withDensity hs hd hsurj
      ((h_int (u n)).sub (h_int a))).symm
  set U : ℕ → F → V := fun n y ↦ ∫ x in s ∩ f ⁻¹' {y}, u n x ∂μHE[k]
  set A : F → V := fun y ↦ ∫ x in s ∩ f ⁻¹' {y}, a x ∂μHE[k]
  have hbound (n : ℕ) : ∀ᵐ y : F, ‖U n y - A y‖ₑ ≤ D n y := by
    filter_upwards [ae_aestronglyMeasurable_restrict_preimage_of_hasFDerivWithinAt volume hdw
      (aestronglyMeasurable_of_integrable_withDensity hs hsurj (h_int (u n))),
      ae_aestronglyMeasurable_restrict_preimage_of_hasFDerivWithinAt volume hdw
        (aestronglyMeasurable_of_integrable_withDensity hs hsurj (h_int a))] with y hun ha'
    exact TauCeti.MeasureTheory.enorm_integral_sub_integral_le_lintegral_enorm_sub hun ha'
  have hU_int (n : ℕ) : Integrable (U n) volume :=
    integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd hsurj
      (integrable_withDensity_normDet_adjoint_fderiv_iff.1 (h_int (u n)))
  have hA_int : Integrable A volume :=
    integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd hsurj
      (integrable_withDensity_normDet_adjoint_fderiv_iff.1 (h_int a))
  have hLHS : Tendsto (fun n ↦ ∫ x, u n x ∂ν) atTop (𝓝 (∫ x, a x ∂ν)) :=
    tendsto_integral_of_L1 a (Lp.aestronglyMeasurable a)
      (Eventually.of_forall fun n ↦ h_int (u n)) hL1
  have hRHS : Tendsto (fun n ↦ ∫ y, U n y) atTop (𝓝 (∫ y, A y)) :=
    tendsto_integral_of_L1 A hA_int.aestronglyMeasurable (Eventually.of_forall hU_int)
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD_lim (fun _ ↦ zero_le)
        fun n ↦ lintegral_mono_ae (hbound n))
  exact tendsto_nhds_unique hLHS (hRHS.congr fun n ↦ (huP n).symm)

/-- Core `Integrable.induction` driver for the Bochner coarea identity on the regular locus. -/
private theorem integral_withDensity_eq
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hg : Integrable g ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet)) :
    ∫ x, g x ∂((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  by_cases hV : CompleteSpace V; swap
  · simp [integral_of_not_completeSpace hV]
  set ν := (volume.restrict s).withDensity
    (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) with hν
  set k := finrank ℝ E - finrank ℝ F
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  refine Integrable.induction
    (P := fun u : E → V ↦ ∫ x, u x ∂ν = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, u x ∂μHE[k])
    (fun c t ht hνt ↦ integral_withDensity_eq_indicator hs hd hsurj c ht hνt)
    ?_ (isClosed_L1_integral_withDensity_eq hs hd hsurj hν) ?_ hg
  · intro u₁ u₂ _ hu₁ hu₂ ih₁ ih₂
    have h₁ := integrable_withDensity_normDet_adjoint_fderiv_iff.1 hu₁
    have h₂ := integrable_withDensity_normDet_adjoint_fderiv_iff.1 hu₂
    have hadd : (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, (u₁ + u₂) x ∂μHE[k]) =ᵐ[volume]
        fun y : F ↦ (∫ x in s ∩ f ⁻¹' {y}, u₁ x ∂μHE[k]) +
          ∫ x in s ∩ f ⁻¹' {y}, u₂ x ∂μHE[k] := by
      filter_upwards [ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd hsurj
        h₁, ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd hsurj h₂]
        with y hy₁ hy₂
      exact integral_add hy₁ hy₂
    have hi₁ := integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd hsurj
      h₁
    have hi₂ := integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd hsurj
      h₂
    calc ∫ x, (u₁ + u₂) x ∂ν = (∫ x, u₁ x ∂ν) + ∫ x, u₂ x ∂ν := integral_add hu₁ hu₂
      _ = ∫ y : F, ((∫ x in s ∩ f ⁻¹' {y}, u₁ x ∂μHE[k]) +
            ∫ x in s ∩ f ⁻¹' {y}, u₂ x ∂μHE[k]) := by rw [ih₁, ih₂, ← integral_add hi₁ hi₂]
      _ = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, (u₁ + u₂) x ∂μHE[k] := integral_congr_ae hadd.symm
  · intro u₁ u₂ hu₁₂ _ ih₁
    have hae_s : u₁ =ᵐ[volume.restrict s] u₂ :=
      (withDensity_ae_eq (TauCeti.measurable_ofReal_normDet_adjoint_fderiv f).aemeasurable
        ((ae_restrict_mem₀ hs).mono fun x hxs ↦
          (ENNReal.ofReal_pos.2
            (ContinuousLinearMap.normDet_adjoint_pos_iff.2 (hsurj x hxs))).ne')).1 hu₁₂
    have hfib : (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u₁ x ∂μHE[k]) =ᵐ[volume]
        fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u₂ x ∂μHE[k] := by
      filter_upwards [ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt volume hdw hae_s] with y hy
      exact integral_congr_ae hy
    exact (integral_congr_ae hu₁₂).symm.trans (ih₁.trans (integral_congr_ae hfib))

/-- **Bochner coarea formula on the regular locus.** For a map differentiable with surjective
derivative on a Lebesgue-measurable set `s`, if `(fderiv ℝ f x)†.normDet • g x` is Bochner
integrable on `s` with values in a real normed space `V`, then its integral over `s` equals the
iterated Bochner integral of `g` along the fibers `s ∩ f ⁻¹' {y}` with respect to normalized
Euclidean Hausdorff measure. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have hco := integral_withDensity_eq hs hd hsurj
    (integrable_withDensity_normDet_adjoint_fderiv_iff.2 hint)
  rw [integral_withDensity_eq_integral_toReal_smul
    (TauCeti.measurable_ofReal_normDet_adjoint_fderiv f)
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at hco
  simpa only [ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)] using hco

/-- Triangle-inequality bound for fiber integrals on the regular locus:
`∫ y, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[k]‖ ≤ ∫ x in s, (fderiv ℝ f x)†.normDet * ‖g x‖`. -/
theorem integral_norm_setIntegral_fiber_le_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    (∫ y : F, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖) ≤
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet * ‖g x‖ := by
  have hnint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • ‖g x‖) s := by
    simpa only [IntegrableOn, norm_smul_of_nonneg (LinearMap.normDet_nonneg _), smul_eq_mul]
      using hint.norm
  have houter := integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd
    hsurj hint
  have hrhs_int := integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd
    hsurj hnint
  refine (integral_mono houter.norm hrhs_int fun y ↦ norm_integral_le_integral_norm _).trans_eq ?_
  simpa only [smul_eq_mul] using
    (integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hs hd hsurj hnint).symm

end RegularBochner

end MeasureTheory
