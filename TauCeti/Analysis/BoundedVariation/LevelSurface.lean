/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import TauCeti.Analysis.BoundedVariation.Truncation
import TauCeti.Analysis.Calculus.FDeriv.Clamp
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Perimeter and surface measure of Lipschitz level sets

For a locally Lipschitz real function, almost every superlevel set has relative perimeter
equal to the normalized Euclidean Hausdorff measure of the corresponding level surface.
The open domain need not be bounded, and neither the function nor its gradient needs to be
globally integrable. Infinite perimeters and surface measures are allowed.

This identifies the geometric level surfaces in the Lipschitz coarea formula with the
superlevel perimeters in BV coarea. In particular, it permits perimeter inequalities to be
used in level-by-level convex gradient estimates.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.4 and §5.5 (the two coarea formulas and level sets).
-/

public section

open MeasureTheory Set Filter Module TopologicalSpace
open scoped ENNReal Topology

namespace LocallyLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {h : E → ℝ} {Ω : Opens E}

/-- Clipping localizes BV coarea and Lipschitz coarea to the same interval of levels. -/
private theorem setLIntegral_perimeter_Ioo (hh : LocallyLipschitz h) {a b : ℝ} (hab : a < b) :
    ∫⁻ t in Ioo a b, TauCeti.perimeter volume Ω {x | t < h x} =
      ∫⁻ x in Ω, (h ⁻¹' Ioo a b).indicator (fun x ↦ ‖fderiv ℝ h x‖ₑ) x := by
  let v : E → ℝ := fun x ↦ max a (min (h x) b)
  have hv : LocallyLipschitz v := (hh.min_const b).const_max a
  have hshift : v = fun x ↦ max 0 (min (h x - a) (b - a)) + a := by
    funext x
    dsimp [v]
    grind
  have hd (x : E) : fderiv ℝ v x = (h ⁻¹' Ioo a b).indicator (fderiv ℝ h) x := by
    rw [hshift, fderiv_add_const,
      TauCeti.fderiv_max_min_eq_indicator (w := fun y ↦ h y - a)
        (hh.continuous.sub continuous_const) (sub_pos.mpr hab)]
    have hs : (fun y ↦ h y - a) ⁻¹' Ioo 0 (b - a) = h ⁻¹' Ioo a b := by
      ext y
      simp only [mem_preimage, mem_Ioo]
      constructor <;> intro hy <;> constructor <;> linarith [hy.1, hy.2]
    simp only [hs]
    by_cases hx : x ∈ h ⁻¹' Ioo a b <;> simp [hx, fderiv_sub_const]
  have hn (x : E) : ‖fderiv ℝ v x‖ₑ =
      (h ⁻¹' Ioo a b).indicator (fun x ↦ ‖fderiv ℝ h x‖ₑ) x := by
    rw [hd, ← ofReal_norm]
    by_cases hx : x ∈ h ⁻¹' Ioo a b <;> simp [hx, ofReal_norm]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ico,
    ← TauCeti.totalVariationOn_max_min_const_eq_lintegral_perimeter
      (hh.locallyLipschitzOn.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet),
    hv.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv]
  exact lintegral_congr hn

/-- Identification of the two coarea densities when their integral on the domain is finite. -/
private theorem ae_perimeter_eq_surface_of_integrableOn (hh : LocallyLipschitz h)
    (hi : IntegrableOn (fun x ↦ (fderiv ℝ h x).adjoint.normDet) Ω) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume Ω {x | t < h x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ h ⁻¹' {t}) := by
  let P : ℝ → ℝ≥0∞ := fun t ↦ TauCeti.perimeter volume Ω {x | t < h x}
  let S : ℝ → ℝ≥0∞ := fun t ↦ μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ h ⁻¹' {t})
  have hP : Measurable P := TauCeti.measurable_perimeter_setOf_lt hh.continuous.aemeasurable
  have hS : AEMeasurable S :=
    hh.locallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage
      volume Ω.isOpen.measurableSet.nullMeasurableSet (by simp only [finrank_self]; omega)
  have hJ : (∫⁻ x in Ω, ‖fderiv ℝ h x‖ₑ) < ∞ := by
    simpa only [ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm] using
      (hasFiniteIntegral_iff_ofReal (.of_forall fun x ↦
        (fderiv ℝ h x).adjoint.toLinearMap.normDet_nonneg)).mp hi.hasFiniteIntegral
  have hPi : ∫⁻ t, P t ≠ ∞ := by
    rw [← TauCeti.totalVariationOn_eq_lintegral_perimeter
      (hh.locallyLipschitzOn.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet),
      hh.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv]
    exact hJ.ne
  have : IsFiniteMeasure (volume.withDensity P) := isFiniteMeasure_withDensity hPi
  have heq : volume.withDensity P = volume.withDensity S := by
    apply Real.measure_ext_Ioo_rat
    intro a b
    rw [withDensity_apply _ measurableSet_Ioo, withDensity_apply _ measurableSet_Ioo]
    by_cases hab : (a : ℝ) < b
    · rw [hh.setLIntegral_perimeter_Ioo hab]
      have hco := hh
        |>.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
          (s := (Ω : Set E) ∩ h ⁻¹' Ioo (a : ℝ) b)
          (Ω.isOpen.measurableSet.inter
            (hh.continuous.measurable measurableSet_Ioo)).nullMeasurableSet
      have hlevels : (∫⁻ t, μHE[finrank ℝ E - 1]
          (((Ω : Set E) ∩ h ⁻¹' Ioo (a : ℝ) b) ∩ h ⁻¹' {t})) = ∫⁻ t in Ioo (a : ℝ) b, S t := by
        rw [← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro t
        rw [inter_assoc, ← preimage_inter]
        by_cases ht : t ∈ Ioo (a : ℝ) b
        · rw [indicator_of_mem ht, inter_singleton_of_mem ht]
        · rw [indicator_of_notMem ht, inter_singleton_of_notMem ht]
          simp
      simp only [finrank_self, ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm] at hco
      rw [← hlevels, hco, lintegral_indicator (hh.continuous.measurable measurableSet_Ioo),
        Measure.restrict_restrict (hh.continuous.measurable measurableSet_Ioo), inter_comm]
    · simp [Ioo_eq_empty hab]
  exact (withDensity_eq_iff hP.aemeasurable hS hPi).mp heq

/-- For a locally Lipschitz real function, almost every superlevel set has relative perimeter
equal to the normalized Hausdorff measure of its level surface inside the open domain.
Neither the domain nor the function is required to have finite volume or finite variation. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure (hh : LocallyLipschitz h)
    (Ω : Opens E) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume Ω {x | t < h x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ h ⁻¹' {t}) := by
  let U : ℕ → Opens E := fun n ↦ ⟨(Ω : Set E) ∩ Metric.ball 0 n,
    Ω.isOpen.inter Metric.isOpen_ball⟩
  have hmono : Monotone U := fun n m hnm ↦ fun x hx ↦
    ⟨hx.1, Metric.ball_subset_ball (Nat.cast_le.mpr hnm) hx.2⟩
  have hU : (⨆ n, U n) = Ω := by
    apply Opens.ext
    simp only [Opens.coe_iSup, U, Opens.coe_mk, ← inter_iUnion, Metric.iUnion_ball_nat,
      inter_univ]
  have hae (n : ℕ) := hh.ae_perimeter_eq_surface_of_integrableOn (Ω := U n)
    ((hh.integrableOn_normDet_adjoint_fderiv_of_isCompact
      (isCompact_closedBall (0 : E) n)).mono_set fun x hx ↦ Metric.ball_subset_closedBall hx.2)
  filter_upwards [ae_all_iff.mpr hae] with t ht
  rw [← hU, TauCeti.perimeter_iSup hmono.directed_le]
  simp_rw [ht]
  have hunion : (⋃ n, (U n : Set E) ∩ h ⁻¹' {t}) = (Ω : Set E) ∩ h ⁻¹' {t} := by
    rw [← iUnion_inter, ← Opens.coe_iSup, hU]
  rw [hU, ← hunion]
  exact (Monotone.measure_iUnion (fun n m hnm ↦
    inter_subset_inter_left _ (hmono hnm))).symm

end LocallyLipschitz
