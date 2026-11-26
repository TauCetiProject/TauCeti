/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.Geometry.Manifold.ExtChartAt.SelfModel
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Positive density measures read in a finite bundle atlas

Let `M` be a manifold without boundary modelled on a finite-dimensional real normed space `E`
with an additive Haar measure `μ`, let `ν` be a positive continuous density measure on `M`
(`TauCeti.IsPositiveDensityMeasure`), such as a Riemannian volume, and let `A` be a finite bundle
atlas of a fibre bundle over `M`. The chart domains of `A` cover `M`, and in each chart `ν` reads
as `μ` weighted by a positive continuous density. So questions about `ν` reduce to the chart
images of `A` with the measure `μ`:

* a property holding `μ`-almost everywhere on every chart image, at the point of `M` read there,
  holds `ν`-almost everywhere (`TauCeti.FiniteBundleAtlas.ae_of_forall_ae_restrict_image`);
* a function whose readings in all charts are almost everywhere strongly measurable on the chart
  images is almost everywhere strongly measurable for `ν`
  (`TauCeti.FiniteBundleAtlas.aestronglyMeasurable_of_forall`);
* lower integrals against `ν` are at most a constant times the sum of the lower integrals of the
  chart readings over the chart images (`TauCeti.FiniteBundleAtlas.exists_lintegral_le`). The
  constant bounds the chart densities on the compact chart images of the closures of the chart
  domains.

## Main results

* `TauCeti.FiniteBundleAtlas.ae_of_forall_ae_restrict_image`: chartwise almost everywhere
  implies `ν`-almost everywhere.
* `TauCeti.FiniteBundleAtlas.aestronglyMeasurable_of_forall`: chartwise measurability implies
  measurability for `ν`.
* `TauCeti.FiniteBundleAtlas.exists_lintegral_le`: lower integrals against `ν` are controlled by
  the chart integrals.
-/

public section

open Bundle MeasureTheory Set
open scoped ENNReal Manifold

namespace TauCeti

namespace FiniteBundleAtlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V) {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure M}

variable {A}

/-- A subset of the domain of chart `i` is `ν`-null when its image in chart `i` is `μ`-null. -/
private theorem measure_eq_zero_of_image (hν : IsPositiveDensityMeasure 𝓘(ℝ, E) ν) {i : Fin A.n}
    {s : Set M} (hs : s ⊆ A.dom i) (h : μ (A.chart i '' s) = 0) : ν s = 0 := by
  have hsub : s ⊆ (extChartAt 𝓘(ℝ, E) (A.center i)).source := by
    rw [extChartAt_modelWithCornersSelf_eq]
    exact hs.trans (A.dom_subset_chart_source i)
  rw [hν.measure_eq_zero_iff_image_of_subset hsub μ, extChartAt_modelWithCornersSelf_eq]
  exact h

/-- **Chartwise almost everywhere implies almost everywhere.** If, for every chart `i` of `A`,
a property `P` holds at the point read at `y` for `μ`-almost every `y` of the chart image, then
`P` holds `ν`-almost everywhere. -/
theorem ae_of_forall_ae_restrict_image (hν : IsPositiveDensityMeasure 𝓘(ℝ, E) ν) {P : M → Prop}
    (h : ∀ i, ∀ᵐ y ∂μ.restrict (A.image i), P ((A.chart i).symm y)) : ∀ᵐ x ∂ν, P x := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx ↦ mem_iUnion.2 ?_)
    (measure_iUnion_null fun i ↦ measure_eq_zero_of_image (μ := μ) hν
      (inter_subset_right (s := {x | ¬P x}) (t := A.dom i)) ?_)
  · obtain ⟨i, hi⟩ := A.exists_mem_dom x
    exact ⟨i, hx, hi⟩
  · have hi := h i
    rw [ae_restrict_iff' (A.image i).isOpen.measurableSet, ae_iff] at hi
    refine measure_mono_null ?_ hi
    rintro _ ⟨x, ⟨hx, hdom⟩, rfl⟩
    simp only [mem_ofPred_eq, Classical.not_imp]
    refine ⟨A.mem_image.2 ⟨x, hdom, rfl⟩, ?_⟩
    rwa [(A.chart i).left_inv (A.dom_subset_chart_source i hdom)]

/-- **Chartwise measurability implies measurability.** A function on `M` whose reading in every
chart of `A` is almost everywhere strongly measurable on the chart image is almost everywhere
strongly measurable for `ν`. -/
theorem aestronglyMeasurable_of_forall (hν : IsPositiveDensityMeasure 𝓘(ℝ, E) ν) {G : Type*}
    [TopologicalSpace G] [TopologicalSpace.PseudoMetrizableSpace G] {g : M → G}
    (h : ∀ i, AEStronglyMeasurable (fun y ↦ g ((A.chart i).symm y)) (μ.restrict (A.image i))) :
    AEStronglyMeasurable g ν := by
  rw [← Measure.restrict_univ (μ := ν), ← A.iUnion_dom, aestronglyMeasurable_iUnion_iff]
  intro i
  have hdom : MeasurableSet (A.dom i) := (A.isOpen_dom i).measurableSet
  have he : AEMeasurable (A.chart i) (ν.restrict (A.dom i)) :=
    ((A.chart i).continuousOn.mono (A.dom_subset_chart_source i)).aemeasurable hdom
  -- The chart image of `ν` on the chart domain has no more null sets than `μ` on the chart image.
  have hac : (ν.restrict (A.dom i)).map (A.chart i) ≪ μ.restrict (A.image i) := by
    refine Measure.AbsolutelyContinuous.mk fun B hB hB0 ↦ ?_
    rw [Measure.map_apply_of_aemeasurable he hB, Measure.restrict_apply' hdom]
    refine measure_eq_zero_of_image hν inter_subset_right (measure_mono_null ?_
      ((Measure.restrict_apply hB).symm.trans hB0))
    rintro _ ⟨x, ⟨hxB, hx⟩, rfl⟩
    exact ⟨hxB, A.mem_image.2 ⟨x, hx, rfl⟩⟩
  refine (((h i).mono_ac hac).comp_aemeasurable he).congr ?_
  filter_upwards [ae_restrict_mem hdom] with x hx
  simp only [Function.comp_apply, (A.chart i).left_inv (A.dom_subset_chart_source i hx)]

/-- On the domain of chart `i`, `ν` reads as `μ` with a continuous density, which is bounded on the
chart image by some `K`. -/
private theorem exists_setLIntegral_dom_le (hν : IsPositiveDensityMeasure 𝓘(ℝ, E) ν) (i : Fin A.n) :
    ∃ K : ℝ, ∀ φ : M → ℝ≥0∞, ∫⁻ x in A.dom i, φ x ∂ν ≤
      ENNReal.ofReal K * ∫⁻ y in A.image i, φ ((A.chart i).symm y) ∂μ := by
  obtain ⟨w, hwc, -, hw⟩ := hν.exists_density (A.center i) μ
  rw [extChartAt_modelWithCornersSelf_eq] at hwc hw
  have himage : (A.image i : Set E) = A.chart i '' A.dom i := Set.ext fun _ ↦ A.mem_image
  have hit : (A.image i : Set E) ⊆ (A.chart i).target := himage ▸
    (image_mono (A.dom_subset_chart_source i)).trans (A.chart i).image_source_eq_target.subset
  have hct : A.chart i '' closure (A.dom i) ⊆ (A.chart i).target :=
    (image_mono (A.closure_dom_subset_source i)).trans (A.chart i).image_source_eq_target.subset
  obtain ⟨K, hK⟩ := (A.isCompact_chart_image_closure_dom i).exists_bound_of_continuousOn
    (hwc.mono hct)
  have hmeas : MeasurableSet (A.image i : Set E) := (A.image i).isOpen.measurableSet
  refine ⟨K, fun φ ↦ ?_⟩
  have hsub : A.dom i ⊆ (extChartAt 𝓘(ℝ, E) (A.center i)).source := by
    rw [extChartAt_modelWithCornersSelf_eq]
    exact A.dom_subset_chart_source i
  have hwm : AEMeasurable (fun y ↦ ENNReal.ofReal (w y))
      (((μ.restrict (A.chart i).target).restrict (A.image i))) := by
    rw [Measure.restrict_restrict hmeas, inter_eq_left.2 hit]
    exact (ENNReal.continuous_ofReal.comp_continuousOn (hwc.mono hit)).aemeasurable hmeas
  rw [setLIntegral_eq_setLIntegral_map_extChartAt hsub, extChartAt_modelWithCornersSelf_eq, hw,
    OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
    ← himage,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hwm _ hmeas
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hmeas, inter_eq_left.2 hit, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hmeas fun y hy ↦ ?_
  rw [Pi.mul_apply]
  gcongr
  exact (Real.le_norm_self _).trans (hK y (A.image_subset_chart_image_closure_dom i hy))

/-- **Lower integrals in the charts.** There is a finite constant `C` such that every lower
integral against `ν` is at most `C` times the sum over the charts of `A` of the lower integrals of
the chart readings over the chart images. -/
theorem exists_lintegral_le (hν : IsPositiveDensityMeasure 𝓘(ℝ, E) ν) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : M → ℝ≥0∞,
      ∫⁻ x, φ x ∂ν ≤ C * ∑ i, ∫⁻ y in A.image i, φ ((A.chart i).symm y) ∂μ := by
  choose K hK using fun i ↦ exists_setLIntegral_dom_le (A := A) (μ := μ) hν i
  refine ⟨∑ i, ENNReal.ofReal (K i), ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top,
    fun φ ↦ ?_⟩
  calc ∫⁻ x, φ x ∂ν = ∫⁻ x in ⋃ i, A.dom i, φ x ∂ν := by rw [A.iUnion_dom, Measure.restrict_univ]
    _ ≤ ∑ i, ∫⁻ x in A.dom i, φ x ∂ν := (lintegral_iUnion_le _ _).trans_eq (tsum_fintype _)
    _ ≤ ∑ i, ENNReal.ofReal (K i) * ∫⁻ y in A.image i, φ ((A.chart i).symm y) ∂μ :=
        Finset.sum_le_sum fun i _ ↦ hK i φ
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ by
        gcongr
        exact Finset.single_le_sum (f := fun i ↦ ENNReal.ofReal (K i)) (fun _ _ ↦ bot_le)
          (Finset.mem_univ i)

end FiniteBundleAtlas

end TauCeti
