/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Null sets and finite bundle atlases

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real normed space
`E` with a Haar measure `μ`, and let `A`, `A'` be two finite bundle atlases of fibre bundles over
`M`, possibly of different bundles. The chart transitions between the two atlases are `C¹`
diffeomorphisms between open sets of `E`, so they carry null sets to null sets. Hence a property
of the points of `M` holding almost everywhere in every chart of `A` holds almost everywhere in
every chart of `A'` (`TauCeti.FiniteBundleAtlas.ae_restrict_image_symm_of_ae`), and, when `A` and
`A'` are atlases of the same bundle, two sections whose readings agree almost everywhere in the
charts of `A` agree almost everywhere in the charts of `A'`
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
  {F' : Type*} [TopologicalSpace F'] {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, TopologicalSpace (V' x)] [FiberBundle F' V']
  (A : FiniteBundleAtlas E M F V) {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Change of atlas preserves null sets, chartwise.** If a property `P` of points of `E` holds
almost everywhere on the image of chart `i` of `A`, then almost everywhere on the image of chart
`i'` of `A'` it holds at the reading in chart `i` of the corresponding point of `M`, wherever that
point lies in the domain of chart `i`. The chart transition from `A'` to `A` is a `C¹`
diffeomorphism between open sets, whose inverse carries null sets to null sets. -/
theorem ae_restrict_image_chart_symm (A' : FiniteBundleAtlas E M F' V') {i : Fin A.n}
    (i' : Fin A'.n) {P : E → Prop}
    (h : ∀ᵐ z ∂μ.restrict (A.image i), P z) :
    ∀ᵐ y ∂μ.restrict (A'.image i'), (A'.chart i').symm y ∈ A.dom i →
      P (A.chart i ((A'.chart i').symm y)) := by
  -- The chart transition `τ` from chart `i'` of `A'` to chart `i` of `A`, on the open set `s` of
  -- points of the image of chart `i'` lying over the domain of chart `i`.
  set τ := (A'.chart i').symm.trans (A.chart i)
  set s : Set E := (A'.image i' : Set E) ∩ (A'.chart i').symm ⁻¹' A.dom i
  have hs : IsOpen s :=
    (A'.continuousOn_chart_symm i').isOpen_inter_preimage (A'.image i').isOpen (A.isOpen_dom i)
  have hsub : s ⊆ τ.source := fun y hy ↦
    ⟨A'.closure_image_subset_target i' (subset_closure hy.1), A.dom_subset_chart_source i hy.2⟩
  have hφ := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := 1) (A'.center i')
  have hψ := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := 1) (A.center i)
  have hτ := ae_restrict_comp_of_differentiableOn μ hs
    (((contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ).differentiableOn one_ne_zero).mono hsub)
    (τ.injOn.mono hsub) (fun y hy ↦ det_fderiv_symm_trans_ne_zero one_ne_zero hφ hψ (hsub hy))
    (fun y hy ↦ A.mem_image.2 ⟨_, hy.2, rfl⟩) h
  rw [ae_restrict_iff' hs.measurableSet] at hτ
  rw [ae_restrict_iff' (A'.image i').isOpen.measurableSet]
  filter_upwards [hτ] with y hy hyU hdom
  exact hy ⟨hyU, hdom⟩

/-- **Almost everywhere statements on `M` do not depend on the atlas.** A property of points of `M`
that holds almost everywhere in every chart of `A` holds almost everywhere in every chart of
`A'`. -/
theorem ae_restrict_image_symm_of_ae (A' : FiniteBundleAtlas E M F' V') {P : M → Prop}
    (h : ∀ i, ∀ᵐ z ∂μ.restrict (A.image i), P ((A.chart i).symm z)) (i' : Fin A'.n) :
    ∀ᵐ y ∂μ.restrict (A'.image i'), P ((A'.chart i').symm y) := by
  have hall := ae_all_iff.2 fun i ↦ A.ae_restrict_image_chart_symm A' i' (h i)
  filter_upwards [hall] with y hy
  obtain ⟨i, hi⟩ := A.exists_mem_dom ((A'.chart i').symm y)
  simpa only [(A.chart i).left_inv (A.dom_subset_chart_source i hi)] using hy i hi

/-- Sections whose readings agree almost everywhere in every chart of one finite bundle atlas agree
almost everywhere in every chart of any other. -/
theorem coord_ae_eq_of_coord_ae_eq (A' : FiniteBundleAtlas E M F V) {s t : ∀ x, V x}
    (h : ∀ i, A.coord i s =ᵐ[μ.restrict (A.image i)] A.coord i t) (i' : Fin A'.n) :
    A'.coord i' s =ᵐ[μ.restrict (A'.image i')] A'.coord i' t := by
  have hst := A.ae_restrict_image_symm_of_ae A' (P := fun x ↦ s x = t x) (fun i ↦ by
    filter_upwards [h i, ae_restrict_mem (A.image i).isOpen.measurableSet] with z hz hzU
    exact (A.coord_eq_coord_iff hzU).1 hz) i'
  filter_upwards [hst] with y hy
  simp only [coord_def, hy]

end FiniteBundleAtlas

end TauCeti
