/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Null sets for the Riemannian volume

The chart density of a continuous Riemannian metric is positive, so a set has Riemannian volume
zero exactly when its images in the charts are null for Haar measure. In other words, the null sets
of `TauCeti.riemannianVolume` are the chartwise null sets `TauCeti.IsNullSet`. This makes
chartwise results such as Sard's theorem apply to the Riemannian volume, also on manifolds with
boundary or corners.

## Main results

* `TauCeti.riemannianVolume_eq_zero_iff_image_of_subset`: a subset of a chart source has volume
  zero exactly when its image in the chart is null for an additive Haar measure.
* `TauCeti.isNullSet_iff_riemannianVolume_eq_zero`: a set is chartwise null exactly when it has
  Riemannian volume zero.
-/

public noncomputable section

open Bundle MeasureTheory Set
open scoped ENNReal Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

section Chart

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

private theorem riemannianVolume_eq_zero_iff_image_of_measurableSet {α : M} {s : Set M}
    (hs : MeasurableSet s) (hsub : s ⊆ (extChartAt I α).source) :
    riemannianVolume I M s = 0 ↔
      (Module.finBasis ℝ E).addHaar ((extChartAt I α) '' s) = 0 := by
  let e := extChartAt I α
  have him : MeasurableSet (e '' s) := hs.image_extChartAt α hsub
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have hd : ContinuousOn
      (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) α (e.symm y))) (e '' s) := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    apply (contMDiffOn_chartVolumeDensity (I := I) (n := 0) α).continuousOn.comp
      ((continuousOn_extChartAt_symm α).mono (image_mono hsub |>.trans e.image_source_eq_target.le))
    rintro y ⟨x, hx, rfl⟩
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I α]
    rw [e.left_inv (hsub hx)]
    exact hsub hx
  rw [riemannianVolume_apply_of_subset (by simpa only [extChartAt_source] using hsub),
    chartRiemannianVolume_apply α hs, inter_eq_left.mpr hsub]
  constructor
  · intro hz
    have ha := (lintegral_eq_zero_iff' (hd.aemeasurable him)).mp hz
    have hfalse : ∀ᵐ y ∂(Module.finBasis ℝ E).addHaar.restrict (e '' s), False := by
      filter_upwards [ae_restrict_mem him, ha] with y hy hyzero
      obtain ⟨x, hx, rfl⟩ := hy
      have hp := chartVolumeDensity_pos (I := I) α (by
        simpa only [TangentBundle.trivializationAt_baseSet, e.left_inv (hsub hx),
          ← extChartAt_source I α] using hsub hx)
      exact (ENNReal.ofReal_pos.mpr hp).ne' (by
        simpa only [e.left_inv (hsub hx), Pi.zero_apply] using hyzero)
    simpa only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ, e,
      extChartAt_coe] using ae_iff.mp hfalse
  · intro hz
    rw [Measure.restrict_zero_set hz, lintegral_zero_measure]

private theorem riemannianVolume_eq_zero_iff_finBasis_image {α : M} {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source) :
    riemannianVolume I M s = 0 ↔
      (Module.finBasis ℝ E).addHaar ((extChartAt I α) '' s) = 0 := by
  let e := extChartAt I α
  let μ := (Module.finBasis ℝ E).addHaar
  constructor
  · intro hs
    let t := toMeasurable (riemannianVolume I M) s ∩ e.source
    have hst : s ⊆ t := fun x hx ↦ ⟨subset_toMeasurable _ _ hx, hsub hx⟩
    have htm : MeasurableSet t :=
      (measurableSet_toMeasurable _ _).inter (isOpen_extChartAt_source α).measurableSet
    have ht : riemannianVolume I M t = 0 :=
      measure_mono_null inter_subset_left (by rwa [measure_toMeasurable])
    exact measure_mono_null (image_mono hst)
      ((riemannianVolume_eq_zero_iff_image_of_measurableSet htm inter_subset_right).mp ht)
  · intro hs
    let A := toMeasurable μ (e '' s)
    let t := Subtype.val '' (e.source.domRestrict e ⁻¹' A)
    have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
      MeasurableEmbedding.subtype_coe (isOpen_extChartAt_source α).measurableSet
    have htm : MeasurableSet t := hval.measurableSet_image.mpr
      ((measurableSet_toMeasurable _ _).preimage
        (measurableEmbedding_extChartAt_restrict α).measurable)
    have hts : t ⊆ e.source := by rintro x ⟨y, _, rfl⟩; exact y.property
    have hst : s ⊆ t := fun x hx ↦
      ⟨⟨x, hsub hx⟩, subset_toMeasurable μ (e '' s) (mem_image_of_mem e hx), rfl⟩
    have hAt : e '' t ⊆ A := by
      rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact hz
    apply measure_mono_null hst
    apply (riemannianVolume_eq_zero_iff_image_of_measurableSet htm hts).mpr
    exact measure_mono_null hAt (by rwa [measure_toMeasurable])

end Chart

section Null

variable [MeasurableSpace E] [BorelSpace E]

/-- A subset of the source of an extended chart has Riemannian volume zero exactly when its image
in the chart is null for an additive Haar measure. The set need not be measurable. -/
theorem riemannianVolume_eq_zero_iff_image_of_subset {α : M} {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source) (μ : Measure E) [μ.IsAddHaarMeasure] :
    riemannianVolume I M s = 0 ↔ μ ((extChartAt I α) '' s) = 0 := by
  obtain rfl : ‹MeasurableSpace E› = extChartAtMeasurableSpaceE := BorelSpace.measurable_eq
  let : MeasurableSpace E := extChartAtMeasurableSpaceE
  rw [riemannianVolume_eq_zero_iff_finBasis_image hsub]
  exact ⟨fun h ↦ Measure.absolutelyContinuous_isAddHaarMeasure μ _ h,
    fun h ↦ Measure.absolutelyContinuous_isAddHaarMeasure _ μ h⟩

/-- A set is chartwise null exactly when it has Riemannian volume zero. -/
theorem isNullSet_iff_riemannianVolume_eq_zero {s : Set M} :
    IsNullSet I s ↔ riemannianVolume I M s = 0 := by
  constructor
  · intro hs
    obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
      (fun x : M ↦ (extChartAt I x).source) fun x ↦ extChartAt_source_mem_nhds x
    have hsub : s ⊆ ⋃ α ∈ t, s ∩ (extChartAt I α).source := by
      intro x hx
      obtain ⟨α, hα, hxα⟩ := mem_iUnion₂.mp (hcover ▸ mem_univ x)
      exact mem_iUnion₂.mpr ⟨α, hα, hx, hxα⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff ht).mpr fun α _ ↦ ?_)
    exact (riemannianVolume_eq_zero_iff_image_of_subset inter_subset_right
      (Module.finBasis ℝ E).addHaar).mpr (hs.chartwise α _)
  · intro hs
    rw [isNullSet_iff]
    intro α μ _
    exact (riemannianVolume_eq_zero_iff_image_of_subset inter_subset_right μ).mp
      (measure_mono_null inter_subset_left hs)

/-- A chartwise null set has Riemannian volume zero. -/
theorem IsNullSet.riemannianVolume_eq_zero {s : Set M} (hs : IsNullSet I s) :
    riemannianVolume I M s = 0 := isNullSet_iff_riemannianVolume_eq_zero.mp hs

end Null

end TauCeti
