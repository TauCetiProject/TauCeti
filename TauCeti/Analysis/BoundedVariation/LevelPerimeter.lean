/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.BoundedVariation.Truncation
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.Topology.EMetricSpace.Lipschitz
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Perimeter of superlevel sets of locally Lipschitz functions

For a locally Lipschitz function `u : E → ℝ` on an open set `Ω ⊆ E` in a finite-dimensional real
inner product space `E`, this file proves that at almost every level `t ∈ ℝ` the variational
perimeter `TauCeti.perimeter volume Ω {x | t < u x}` equals `μHE[finrank ℝ E - 1] (Ω ∩ u ⁻¹' {t})`,
without integrability or finite-variation hypotheses on `u`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §3.4 and §5.5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 13.
-/

public section

open Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Topology

section PrivateHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem fderiv_max_min_const_eq_indicator_of_continuousAt {u : E → ℝ} {x : E}
    (hu : ContinuousAt u x) {a b : ℝ} (hab : a < b) :
    fderiv ℝ (fun y ↦ max a (min (u y) b)) x = (u ⁻¹' Ioo a b).indicator (fderiv ℝ u) x := by
  rcases lt_trichotomy (u x) a with h | h | h
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (h.trans hx.1).false]
    refine (EventuallyEq.fderiv_eq (f := fun _ ↦ a) ?_).trans (fderiv_const_apply a)
    filter_upwards [hu.eventually (gt_mem_nhds h)] with _ hy
    exact max_eq_left ((min_le_left _ _).trans hy.le)
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (h ▸ hx.1).false]
    exact IsLocalMin.fderiv_eq_zero (.of_forall fun _ ↦ by simp [h, min_eq_left hab.le])
  rcases lt_trichotomy (u x) b with h' | h' | h'
  · rw [indicator_of_mem (s := u ⁻¹' Ioo a b) ⟨h, h'⟩]
    refine EventuallyEq.fderiv_eq ?_
    filter_upwards [hu.eventually (lt_mem_nhds h), hu.eventually (gt_mem_nhds h')] with _ hy hy'
    rw [min_eq_left hy'.le, max_eq_right hy.le]
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (h' ▸ hx.2).false]
    exact IsLocalMax.fderiv_eq_zero (.of_forall fun _ ↦ by simp [h', hab.le])
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (hx.2.trans h').false]
    refine (EventuallyEq.fderiv_eq (f := fun _ ↦ b) ?_).trans (fderiv_const_apply b)
    filter_upwards [hu.eventually (lt_mem_nhds h')] with _ hy
    rw [min_eq_right hy.le, max_eq_right hab.le]

private theorem setLIntegral_Ico_perimeter_eq_euclideanHausdorffMeasure {V : Opens E} {u : E → ℝ}
    (huV : LocallyLipschitzOn V u) {a b : ℝ} (hab : a < b) :
    ∫⁻ t in Ico a b, TauCeti.perimeter volume V {x | t < u x} =
      ∫⁻ t in Ico a b, μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
  have hVm : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  have hu_cont : ContinuousOn u V := huV.continuousOn
  have hclamp : LocallyLipschitzOn V (fun x ↦ max a (min (u x) b)) := by
    have hcomp := (((LipschitzWith.const a).max
      (LipschitzWith.id.min (LipschitzWith.const b))).locallyLipschitz).comp_locallyLipschitzOn huV
    simpa only [Function.comp_def, id_eq] using hcomp
  rw [← TauCeti.totalVariationOn_max_min_const_eq_lintegral_perimeter
      (hu_cont.locallyIntegrableOn hVm), hclamp.totalVariationOn_eq_setLIntegral_enorm_fderiv]
  have hband : MeasurableSet ((V : Set E) ∩ u ⁻¹' Ioo a b) :=
    (hu_cont.isOpen_inter_preimage V.isOpen isOpen_Ioo).measurableSet
  have hgrad : ∫⁻ x in (V : Set E), ‖fderiv ℝ (fun y ↦ max a (min (u y) b)) x‖ₑ =
      ∫⁻ x in (V : Set E) ∩ u ⁻¹' Ioo a b, ENNReal.ofReal (fderiv ℝ u x).adjoint.normDet := by
    have hind : ∫⁻ x in (V : Set E), ‖fderiv ℝ (fun y ↦ max a (min (u y) b)) x‖ₑ =
        ∫⁻ x in (V : Set E), (u ⁻¹' Ioo a b).indicator (fun x ↦ ‖fderiv ℝ u x‖ₑ) x :=
      setLIntegral_congr_fun hVm fun x hx ↦ by
        rw [fderiv_max_min_const_eq_indicator_of_continuousAt
          ((hu_cont x hx).continuousAt (V.isOpen.mem_nhds hx)) hab]
        by_cases hxu : x ∈ u ⁻¹' Ioo a b <;> simp [hxu, ← ofReal_norm]
    rw [hind, ← lintegral_indicator hVm, ← lintegral_indicator hband]
    refine lintegral_congr fun x ↦ ?_
    by_cases hxV : x ∈ (V : Set E) <;> by_cases hxu : x ∈ u ⁻¹' Ioo a b <;>
      simp [hxV, hxu, ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm]
  have hco :=
    huV.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      V.isOpen inter_subset_left hband.nullMeasurableSet
  rw [hgrad, ← hco, finrank_self, ← setLIntegral_congr Ioo_ae_eq_Ico,
    ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun t ↦ ?_
  by_cases ht : t ∈ Ioo a b
  · rw [indicator_of_mem ht]
    congr 1; ext x; simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun ⟨⟨hxV, _⟩, hxt⟩ ↦ ⟨hxV, hxt⟩, fun ⟨hxV, hxt⟩ ↦ ⟨⟨hxV, hxt.symm ▸ ht⟩, hxt⟩⟩
  · have hemp : ((V : Set E) ∩ u ⁻¹' Ioo a b) ∩ u ⁻¹' {t} = ∅ :=
      eq_empty_of_forall_notMem fun _ ⟨⟨_, hxu⟩, hxt⟩ ↦ ht (hxt ▸ hxu)
    simp [indicator_of_notMem ht, hemp]

private theorem ae_perimeter_eq_euclideanHausdorffMeasure_of_isCompact_closure {Ω V : Opens E}
    {u : E → ℝ} (hu : LocallyLipschitzOn Ω u) (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Ω) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume V {x | t < u x} =
      μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
  have huV : LocallyLipschitzOn V u := hu.mono (subset_closure.trans hVΩ)
  have hVm : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  set P : ℝ → ℝ≥0∞ := fun t ↦ TauCeti.perimeter volume V {x | t < u x}
  set H : ℝ → ℝ≥0∞ := fun t ↦ μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t})
  have hP_fin : IsFiniteMeasure (volume.withDensity P) := by
    rw [isFiniteMeasure_withDensity_iff, huV.lintegral_perimeter_eq_setLIntegral_enorm_fderiv]
    simpa only [ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm] using
      ((hu.integrableOn_normDet_adjoint_fderiv_of_isCompact Ω.isOpen hVΩ hVc).mono_set
        subset_closure).lintegral_lt_top.ne
  refine (withDensity_eq_iff_of_sigmaFinite
    (TauCeti.measurable_perimeter_setOf_lt (huV.continuousOn.aemeasurable hVm)).aemeasurable
    (huV.aemeasurable_euclideanHausdorffMeasure_inter_preimage (Y := ℝ) volume
      hVm.nullMeasurableSet (by rw [finrank_self]; exact le_add_tsub))).1 ?_
  refine (volume.withDensity P).ext_of_Ico (volume.withDensity H) fun a b hab ↦ ?_
  rw [withDensity_apply _ measurableSet_Ico, withDensity_apply _ measurableSet_Ico]
  exact setLIntegral_Ico_perimeter_eq_euclideanHausdorffMeasure huV hab

end PrivateHelpers

namespace LocallyLipschitzOn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {u : E → ℝ}

/-- **Superlevel perimeter of a locally Lipschitz function.** If `u : E → ℝ` is locally Lipschitz
on an open set `Ω`, then at almost every level `t ∈ ℝ` the variational perimeter of `{x | t < u x}`
in `Ω` equals the `(dim E - 1)`-dimensional Euclidean Hausdorff measure of `Ω ∩ u ⁻¹' {t}`. Neither
integrability nor finite total variation is required. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage
    (hu : LocallyLipschitzOn Ω u) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume Ω {x | t < u x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) := by
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hsup : (⨆ j, V j) = Ω := SetLike.coe_injective (by simp [hVU])
  filter_upwards [ae_all_iff.2 fun j ↦
    ae_perimeter_eq_euclideanHausdorffMeasure_of_isCompact_closure hu (hVc j) (hVΩ j)] with t ht
  have hunion : (Ω : Set E) ∩ u ⁻¹' {t} = ⋃ j, ((V j : Set E) ∩ u ⁻¹' {t}) := by
    rw [← iUnion_inter, hVU]
  rw [hunion, Monotone.measure_iUnion fun _ _ hij ↦ inter_subset_inter_left _ (hVmono hij),
    ← hsup, TauCeti.perimeter_iSup hVmono.directed_le]
  exact iSup_congr ht

end LocallyLipschitzOn

namespace LocallyLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}

/-- For a locally Lipschitz function `u : E → ℝ` and any open set `Ω`, at almost every level `t`
the perimeter of `{x | t < u x}` in `Ω` equals `μHE[dim E - 1] (Ω ∩ u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage
    (hu : LocallyLipschitz u) (Ω : Opens E) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume Ω {x | t < u x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) :=
  hu.locallyLipschitzOn.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage

/-- For a locally Lipschitz function `u : E → ℝ`, at almost every level `t` the whole-space
perimeter of `{x | t < u x}` equals `μHE[dim E - 1] (u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage
    (hu : LocallyLipschitz u) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume ⊤ {x | t < u x} =
      μHE[finrank ℝ E - 1] (u ⁻¹' {t}) := by
  simpa using hu.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage ⊤

end LocallyLipschitz

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {u : E → ℝ}

/-- For a Lipschitz function `u : E → ℝ`, at almost every level `t` the whole-space perimeter of
`{x | t < u x}` equals `μHE[dim E - 1] (u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage
    (hu : LipschitzWith K u) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume ⊤ {x | t < u x} =
      μHE[finrank ℝ E - 1] (u ⁻¹' {t}) :=
  hu.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage

end LipschitzWith
