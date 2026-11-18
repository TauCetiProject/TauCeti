/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Truncation
public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import TauCeti.Analysis.Calculus.FDeriv.Clamp
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.Topology.EMetricSpace.Lipschitz
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Level-set Hausdorff measure and superlevel perimeter

For a real-valued function `u` locally Lipschitz on an open set `Ω` of a finite-dimensional real
inner product space `E`, at almost every level `t : ℝ` the variational perimeter
`TauCeti.perimeter volume Ω {x | t < u x}` of the superlevel set `{u > t}` in `Ω` equals the
Euclidean Hausdorff measure `μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t})` of the level set
inside `Ω`.

This bridges variational lower bounds on superlevel perimeters—such as the sharp Euclidean
isoperimetric inequality and the superlevel perimeter comparison for Schwarz rearrangement—with
Hausdorff level-set integrals in the Lipschitz coarea formula, as used in the Lipschitz and Sobolev
Pólya–Szegő inequalities.

Both sides take values in `ℝ≥0∞` and may equal `∞` (for instance on unbounded level sets when
`Ω = ⊤`), with equality asserted in `ℝ≥0∞` via exhaustion of `Ω` by relatively compact open subsets
on which `‖fderiv ℝ u‖` is integrable and `Measure.ext_of_Ico` applies. No positive-dimension
hypothesis is imposed: when `finrank ℝ E = 0`, truncated subtraction `0 - 1 = 0` makes `μHE[0]`
counting measure, and both sides vanish at every level `t` other than the single value taken by
`u`.

## Main statements

* `LocallyLipschitzOn.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage`: for `u`
  locally Lipschitz on `Ω : Opens E`, `perimeter volume Ω {x | t < u x} =
  μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t})` for almost every `t : ℝ`.
* `LocallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage` and
  `LipschitzWith.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage`: whole-space
  specializations (`Ω = ⊤`).

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 and §5.5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 18.1.
-/

public section

open MeasureTheory Set TopologicalSpace Filter Module TauCeti
open scoped ENNReal NNReal Topology

namespace LocallyLipschitzOn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- On every open set `V` where `u` is locally Lipschitz, the superlevel perimeter and the
level-set Hausdorff measure have equal integrals over every half-open interval `Ico a b`. -/
private theorem setLIntegral_Ico_perimeter_eq_hausdorff {V : Opens E} {u : E → ℝ}
    (hu : LocallyLipschitzOn V u) (a b : ℝ) :
    ∫⁻ t in Ico a b, perimeter volume V {x | t < u x} =
      ∫⁻ t in Ico a b, μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
  have hVm : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  let S : Set E := (V : Set E) ∩ u ⁻¹' Ioo a b
  have hSm : MeasurableSet S :=
    (hu.continuousOn.isOpen_inter_preimage V.isOpen isOpen_Ioo).measurableSet
  have hvu : LocallyLipschitzOn V (fun x ↦ max a (min (u x) b)) :=
    ((LipschitzWith.id.min_const b).const_max a).locallyLipschitz.comp_locallyLipschitzOn hu
  have hlhs : ∫⁻ t in Ico a b, perimeter volume V {x | t < u x} =
      ∫⁻ x in S, ‖fderiv ℝ u x‖ₑ := by
    rw [← totalVariationOn_max_min_const_eq_lintegral_perimeter
      (hu.continuousOn.locallyIntegrableOn hVm) a b,
      hvu.totalVariationOn_eq_setLIntegral_enorm_fderiv]
    have hcongr : ∫⁻ x in V, ‖fderiv ℝ (fun y ↦ max a (min (u y) b)) x‖ₑ =
        ∫⁻ x in V, S.indicator (fun x ↦ ‖fderiv ℝ u x‖ₑ) x := by
      refine setLIntegral_congr_fun hVm fun x hx ↦ ?_
      rw [fderiv_max_min_eq_indicator u a b x]
      by_cases hxu : x ∈ u ⁻¹' Ioo a b
      · have hxS : x ∈ S := ⟨hx, hxu⟩
        simp [hxu, hxS]
      · have hxS : x ∉ S := fun h ↦ hxu h.2
        rw [indicator_of_notMem hxu, indicator_of_notMem hxS, ← ofReal_norm, norm_zero,
          ENNReal.ofReal_zero]
    rw [hcongr, setLIntegral_indicator hSm, inter_eq_left.mpr inter_subset_left]
  have hcoarea :=
    hu.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      V.isOpen inter_subset_left hSm.nullMeasurableSet
  rw [finrank_self] at hcoarea
  have hjac : ∫⁻ x in S, ENNReal.ofReal (fderiv ℝ u x).adjoint.normDet =
      ∫⁻ x in S, ‖fderiv ℝ u x‖ₑ := by
    refine setLIntegral_congr_fun hSm fun x _ ↦ ?_
    rw [ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm]
  have hfib : ∫⁻ t : ℝ, μHE[finrank ℝ E - 1] (S ∩ u ⁻¹' {t}) =
      ∫⁻ t in Ioo a b, μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t ↦ ?_
    by_cases ht : t ∈ Ioo a b
    · rw [indicator_of_mem ht]
      congr 1
      ext x
      simp only [S, mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun hx ↦ ⟨hx.1.1, hx.2⟩, fun hx ↦ ⟨⟨hx.1, hx.2 ▸ ht⟩, hx.2⟩⟩
    · rw [indicator_of_notMem ht]
      convert measure_empty (μ := μHE[finrank ℝ E - 1])
      ext x
      simp only [S, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun hx ↦ ht (hx.2 ▸ hx.1.2)
  rw [hlhs, ← hjac, ← hcoarea, hfib, setLIntegral_congr Ioo_ae_eq_Ico]

/-- When `‖fderiv ℝ u‖` has finite integral on `V`, equality of interval integrals promotes via
`Measure.ext_of_Ico` to almost-everywhere equality of the level densities. -/
private theorem ae_perimeter_setOf_lt_eq_of_lintegral_ne_top {V : Opens E} {u : E → ℝ}
    (hu : LocallyLipschitzOn V u) (hfin : ∫⁻ x in V, ‖fderiv ℝ u x‖ₑ ≠ ∞) :
    ∀ᵐ t : ℝ, perimeter volume V {x | t < u x} =
      μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
  have hVm : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  let f₁ : ℝ → ℝ≥0∞ := fun t ↦ perimeter volume V {x | t < u x}
  let f₂ : ℝ → ℝ≥0∞ := fun t ↦ μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t})
  have hf₁ : Measurable f₁ := measurable_perimeter_setOf_lt (hu.continuousOn.aemeasurable hVm)
  have hf₂ : AEMeasurable f₂ :=
    hu.aemeasurable_euclideanHausdorffMeasure_inter_preimage volume hVm.nullMeasurableSet
      (by rw [finrank_self]; exact le_add_tsub)
  have hfin₁ : ∫⁻ t, f₁ t ≠ ∞ := by
    rw [hu.lintegral_perimeter_eq_setLIntegral_enorm_fderiv]
    exact hfin
  have : IsFiniteMeasure (volume.withDensity f₁) := isFiniteMeasure_withDensity hfin₁
  have hμeq : volume.withDensity f₁ = volume.withDensity f₂ := by
    refine Measure.ext_of_Ico _ _ fun a b _ ↦ ?_
    rw [withDensity_apply _ measurableSet_Ico, withDensity_apply _ measurableSet_Ico]
    exact setLIntegral_Ico_perimeter_eq_hausdorff hu a b
  exact (withDensity_eq_iff_of_sigmaFinite hf₁.aemeasurable hf₂).mp hμeq

/-- **Level-set Hausdorff measure equals superlevel perimeter** for locally Lipschitz functions on
an open set `Ω`: at almost every level `t : ℝ`,
`perimeter volume Ω {x | t < u x} = μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage
    {Ω : Opens E} {u : E → ℝ} (hu : LocallyLipschitzOn Ω u) :
    ∀ᵐ t : ℝ, perimeter volume Ω {x | t < u x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) := by
  obtain ⟨V, hVc, hVΩ, hmono, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hΩ : (⨆ j, V j) = Ω := Opens.ext (by simpa using hVU)
  have hVfin (j : ℕ) : ∫⁻ x in V j, ‖fderiv ℝ u x‖ₑ ≠ ∞ := by
    have hint := hu.integrableOn_normDet_adjoint_fderiv_of_isCompact Ω.isOpen (hVΩ j) (hVc j)
    have hle : ∫⁻ x in V j, ‖fderiv ℝ u x‖ₑ ≤
        ∫⁻ x in closure (V j : Set E), ‖(fderiv ℝ u x).adjoint.normDet‖ₑ := by
      refine (lintegral_mono_set subset_closure).trans_eq (lintegral_congr fun x ↦ ?_)
      rw [ContinuousLinearMap.normDet_adjoint_eq_norm, Real.eNorm_of_nonneg (norm_nonneg _),
        ofReal_norm]
    exact ne_top_of_le_ne_top hint.2.ne hle
  have hae (j : ℕ) := ae_perimeter_setOf_lt_eq_of_lintegral_ne_top
    (hu.mono (subset_closure.trans (hVΩ j))) (hVfin j)
  filter_upwards [ae_all_iff.2 hae] with t ht
  have hper : perimeter volume Ω {x | t < u x} = ⨆ j, perimeter volume (V j) {x | t < u x} := by
    rw [← hΩ, perimeter_iSup hmono.directed_le]
  have hcov : ((Ω : Set E) ∩ u ⁻¹' {t}) = ⋃ j, ((V j : Set E) ∩ u ⁻¹' {t}) := by
    rw [← iUnion_inter, hVU]
  have hhaus : μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) =
      ⨆ j, μHE[finrank ℝ E - 1] ((V j : Set E) ∩ u ⁻¹' {t}) := by
    rw [hcov]
    exact Monotone.measure_iUnion fun _ _ h ↦ inter_subset_inter_left _ (hmono h)
  rw [hper, hhaus]
  exact iSup_congr ht

end LocallyLipschitzOn

namespace LocallyLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}

/-- For a globally locally Lipschitz function `u : E → ℝ` and an open set `Ω`, at almost every
level `t : ℝ` the superlevel perimeter in `Ω` equals `μHE[finrank ℝ E - 1] (Ω ∩ u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage
    (hu : LocallyLipschitz u) (Ω : Opens E) :
    ∀ᵐ t : ℝ, perimeter volume Ω {x | t < u x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) :=
  (hu.locallyLipschitzOn (s := Ω)).ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage

/-- **Whole-space level-set Hausdorff measure and superlevel perimeter** for locally Lipschitz
functions: `perimeter volume ⊤ {x | t < u x} = μHE[finrank ℝ E - 1] (u ⁻¹' {t})` for almost every
`t : ℝ`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage
    (hu : LocallyLipschitz u) :
    ∀ᵐ t : ℝ, perimeter volume ⊤ {x | t < u x} = μHE[finrank ℝ E - 1] (u ⁻¹' {t}) := by
  simpa using hu.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage ⊤

end LocallyLipschitz

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {u : E → ℝ}

/-- For a `K`-Lipschitz function `u : E → ℝ` and an open set `Ω`, at almost every level `t : ℝ` the
superlevel perimeter in `Ω` equals `μHE[finrank ℝ E - 1] (Ω ∩ u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage
    (hu : LipschitzWith K u) (Ω : Opens E) :
    ∀ᵐ t : ℝ, perimeter volume Ω {x | t < u x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) :=
  hu.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage Ω

/-- **Whole-space level-set Hausdorff measure and superlevel perimeter** for Lipschitz functions:
`perimeter volume ⊤ {x | t < u x} = μHE[finrank ℝ E - 1] (u ⁻¹' {t})` for almost every `t : ℝ`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage
    (hu : LipschitzWith K u) :
    ∀ᵐ t : ℝ, perimeter volume ⊤ {x | t < u x} = μHE[finrank ℝ E - 1] (u ⁻¹' {t}) :=
  hu.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage

end LipschitzWith
