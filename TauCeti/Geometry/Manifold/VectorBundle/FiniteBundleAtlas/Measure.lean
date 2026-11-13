/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Null sets and finite bundle atlases

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real normed space
`E` with a Haar measure `μ`, and let `A`, `A'` be two finite bundle atlases of a fibre bundle over
`M`. The chart transitions between the two atlases are `C¹` diffeomorphisms between open sets of
`E`, so they carry null sets to null sets. Hence a property of the points of `M` holding almost
everywhere in every chart of `A` holds almost everywhere in every chart of `A'`
(`TauCeti.FiniteBundleAtlas.ae_restrict_image_symm_of_ae`), and two sections whose readings agree
almost everywhere in the charts of `A` agree almost everywhere in the charts of `A'`
(`TauCeti.FiniteBundleAtlas.coord_ae_eq_of_coord_ae_eq`).

## Main results

* `TauCeti.FiniteBundleAtlas.ae_restrict_image_chart_symm`: change of atlas preserves null sets,
  chartwise.
* `TauCeti.FiniteBundleAtlas.ae_restrict_image_symm_of_ae`: almost everywhere statements on `M` do
  not depend on the atlas.
* `TauCeti.FiniteBundleAtlas.coord_ae_eq_of_coord_ae_eq`: sections whose readings agree almost
  everywhere in one atlas agree almost everywhere in every other atlas.
-/

public section

open Bundle MeasureTheory Set
open scoped Manifold

universe u

namespace TauCeti

namespace FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A A' : FiniteBundleAtlas E M F V) {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Change of atlas preserves null sets, chartwise.** If a property `P` of points of `E` holds
almost everywhere on the image of chart `i` of `A`, then almost everywhere on the image of chart
`i'` of `A'` it holds at the reading in chart `i` of the corresponding point of `M`, wherever that
point lies in the domain of chart `i`. The chart transition from `A'` to `A` is a `C¹`
diffeomorphism between open sets, whose inverse carries null sets to null sets. -/
theorem ae_restrict_image_chart_symm {i : Fin A.n} (i' : Fin A'.n) {P : E → Prop}
    (h : ∀ᵐ z ∂μ.restrict (A.image i), P z) :
    ∀ᵐ y ∂μ.restrict (A'.image i'), (A'.chart i').symm y ∈ A.dom i →
      P (A.chart i ((A'.chart i').symm y)) := by
  rw [ae_restrict_iff' (A.image i).isOpen.measurableSet] at h
  have hN : μ ({z | ¬P z} ∩ A.image i) = 0 := by
    rw [ae_iff] at h
    exact measure_mono_null (fun z hz ↦ fun h' ↦ hz.1 (h' hz.2)) h
  -- The chart transition from `A` to `A'` is differentiable on its source.
  have hd := ((contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (A'.center i')
    (A.center i)).differentiableOn one_ne_zero).mono
      (inter_subset_right (s := {z | ¬P z} ∩ A.image i))
  have himage := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hd
    (measure_mono_null inter_subset_left hN)
  rw [ae_iff, Measure.restrict_apply' (A'.image i').isOpen.measurableSet]
  refine measure_mono_null (fun y hy ↦ ?_) himage
  simp only [not_imp, mem_inter_iff, mem_ofPred_eq] at hy
  obtain ⟨⟨hdom, hP⟩, hy'⟩ := hy
  set x := (A'.chart i').symm y
  have hx : x ∈ (A.chart i).source := A.dom_subset_chart_source i hdom
  have hx' : x ∈ (A'.chart i').source := A'.dom_subset_chart_source i' (A'.symm_mem_dom hy')
  refine ⟨A.chart i x, ⟨⟨hP, A.mem_image.2 ⟨x, hdom, rfl⟩⟩, ?_⟩, ?_⟩
  · simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
      extChartAt_target, extChartAt_source, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq, range_id, inter_univ,
      preimage_id_eq]
    exact ⟨(A.chart i).map_source hx, by rwa [(A.chart i).left_inv hx]⟩
  · simp only [Function.comp_apply, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [(A.chart i).left_inv hx,
      (A'.chart i').right_inv (A'.closure_image_subset_target i' (subset_closure hy'))]

/-- **Almost everywhere statements on `M` do not depend on the atlas.** A property of points of `M`
that holds almost everywhere in every chart of `A` holds almost everywhere in every chart of
`A'`. -/
theorem ae_restrict_image_symm_of_ae {P : M → Prop}
    (h : ∀ i, ∀ᵐ z ∂μ.restrict (A.image i), P ((A.chart i).symm z)) (i' : Fin A'.n) :
    ∀ᵐ y ∂μ.restrict (A'.image i'), P ((A'.chart i').symm y) := by
  have hall := ae_all_iff.2 fun i ↦ A.ae_restrict_image_chart_symm A' i' (h i)
  filter_upwards [hall] with y hy
  obtain ⟨i, hi⟩ := A.exists_mem_dom ((A'.chart i').symm y)
  simpa only [(A.chart i).left_inv (A.dom_subset_chart_source i hi)] using hy i hi

/-- Sections whose readings agree almost everywhere in every chart of one finite bundle atlas agree
almost everywhere in every chart of any other. -/
theorem coord_ae_eq_of_coord_ae_eq [∀ x, Zero (V x)] {s t : ∀ x, V x}
    (h : ∀ i, A.coord i s =ᵐ[μ.restrict (A.image i)] A.coord i t) (i' : Fin A'.n) :
    A'.coord i' s =ᵐ[μ.restrict (A'.image i')] A'.coord i' t := by
  have hst := A.ae_restrict_image_symm_of_ae A' (P := fun x ↦ s x = t x) (fun i ↦ by
    filter_upwards [h i, ae_restrict_mem (A.image i).isOpen.measurableSet] with z hz hzU
    have hb := A.dom_subset_baseSet i (A.symm_mem_dom hzU)
    rw [← (A.triv i).symm_apply_apply_mk hb (s _), ← (A.triv i).symm_apply_apply_mk hb (t _)]
    rw [A.coord_def, A.coord_def] at hz
    exact congrArg _ hz) i'
  filter_upwards [hst] with y hy
  simp only [coord_def, hy]

end FiniteBundleAtlas

end TauCeti
