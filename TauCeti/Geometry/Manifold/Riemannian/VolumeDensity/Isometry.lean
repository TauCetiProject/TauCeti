/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# Isometry invariance of the Riemannian volume

A homeomorphism `Φ : M ≃ₜ N` between manifolds with continuous Riemannian metrics which is
differentiable, and whose tangent maps preserve the Riemannian inner products, carries the
Riemannian volume of `M` to the Riemannian volume of `N`. In particular isometric manifolds have
the same Riemannian volume, which is what makes the total volume a Riemannian invariant.

The isometry condition is stated pointwise, on the tangent maps, and no orientation is used, so
orientation-reversing isometries and manifolds with boundary or corners are covered. The two
manifolds may be modelled on different model spaces `H` and `H'` over the same vector space `E`.

The statement is the invariance of the Riemannian density under isometries, as in
J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
(Riemannian volume forms and densities).

## Main results

* `TauCeti.chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv`: the chart volume densities of
  two Riemannian manifolds differ by the absolute Jacobian determinant of a map whose tangent map
  preserves the inner products.
* `TauCeti.chartRiemannianVolume_image_of_inner_mfderiv`: such a map, injective on a subset of a
  chart source, carries its chart volume to the chart volume of its image.
* `Homeomorph.measurePreserving_riemannianVolume`: a differentiable homeomorphism whose tangent
  maps preserve the inner products preserves the Riemannian volume.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped InnerProductSpace Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]

/-- If the tangent map of `Φ` at `x` preserves the Riemannian inner products, then the volume
density of `M` in the chart at `α` is the volume density of `N` in the chart at `β` multiplied by
the absolute Jacobian determinant of `Φ` read in these two charts. -/
theorem chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv {Φ : M → N} {α x : M} {β : N}
    (hxα : x ∈ (chartAt H α).source) (hxβ : Φ x ∈ (chartAt H' β).source)
    (hinner : ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartVolumeDensity (I := I) α x =
      |(mfderiv I' 𝓘(ℝ, E) (extChartAt I' β) (Φ x) ∘L mfderiv I I' Φ x ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x) :
          E →L[ℝ] E).det| *
        chartVolumeDensity (I := I') β (Φ x) := by
  have hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxα
  have hβ : Φ x ∈ (trivializationAt E (TangentSpace I') β).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxβ
  set b := Module.finBasis ℝ E
  set bα := (trivializationAt E (TangentSpace I) α).basisAt b hα
  set bβ := (trivializationAt E (TangentSpace I') β).basisAt b hβ
  set L : E →L[ℝ] E := mfderiv I' 𝓘(ℝ, E) (extChartAt I' β) (Φ x) ∘L mfderiv I I' Φ x ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x)
  -- In the trivialization bases, the tangent map of `Φ` has the Jacobian matrix of `L`.
  have hmat : LinearMap.toMatrix bα bβ (mfderiv I I' Φ x).toLinearMap =
      LinearMap.toMatrix b b L.toLinearMap := by
    ext k i
    simp only [LinearMap.toMatrix_apply, bα, bβ, Trivialization.basisAt, Module.Basis.map_apply,
      Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
      Trivialization.linearEquivAt_symm_apply, Trivialization.linearEquivAt_apply]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hβ,
      ← Trivialization.symmL_apply (R := ℝ) _ hα, TangentBundle.symmL_trivializationAt hxα,
      TangentBundle.continuousLinearMapAt_trivializationAt hxβ]
    -- `L` evaluates the composite on `b i`. It is ascribed `E →L[ℝ] E`, while its factors act on
    -- tangent spaces of the model space, which are `E` only by definition, so
    -- `ContinuousLinearMap.comp_apply` does not match syntactically.
    rfl
  -- The inner product at `x` is pulled back from the one at `Φ x`, so the Gram matrices are
  -- congruent by that Jacobian matrix.
  have hform : innerₗ (TangentSpace I x) = LinearMap.BilinForm.comp
      (innerₗ (TangentSpace I' (Φ x))) (mfderiv I I' Φ x).toLinearMap
      (mfderiv I I' Φ x).toLinearMap := by
    ext v w
    simp [hinner]
  have hdet : (chartGramMatrix (I := I) α x).det =
      L.det ^ 2 * (chartGramMatrix (I := I') β (Φ x)).det := by
    rw [chartGramMatrix_eq_toMatrix α hα, chartGramMatrix_eq_toMatrix β hβ, hform,
      LinearMap.BilinForm.toMatrix_comp bβ bα, hmat, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, LinearMap.det_toMatrix, ContinuousLinearMap.det]
    ring
  rw [chartVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    chartVolumeDensity_def]

section Measure

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-- The Borel measurable space on the model vector space, used for chart volume. -/
local instance chartIsometryMeasurableSpaceE : MeasurableSpace E := borel E

/-- The model vector space's measurable space is its Borel measurable space. -/
local instance : BorelSpace E := ⟨rfl⟩

/-- A map which is injective and differentiable on a measurable subset `s` of the chart source at
`α`, maps `s` into the chart source at `β`, and whose tangent maps at points of `s` preserve the
Riemannian inner products, carries the chart volume of `s` at `α` to the chart volume of its image
at `β`. -/
theorem chartRiemannianVolume_image_of_inner_mfderiv {Φ : M → N} {α : M} {β : N} {s : Set M}
    (hs : MeasurableSet s) (hΦs : MeasurableSet (Φ '' s)) (hinj : InjOn Φ s)
    (hsα : s ⊆ (chartAt H α).source) (hsβ : MapsTo Φ s (chartAt H' β).source)
    (hΦ : ∀ x ∈ s, MDifferentiableAt I I' Φ x)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartRiemannianVolume (I := I') β (Φ '' s) = chartRiemannianVolume (I := I) α s := by
  -- This change-of-variables argument is adapted from the proof of
  -- `TauCeti.chartRiemannianVolume_restrict_overlap`.
  have hsα' : s ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hsβ' : Φ '' s ⊆ (extChartAt I' β).source := by
    rw [extChartAt_source]; exact hsβ.image_subset
  rw [chartRiemannianVolume_apply β hΦs, chartRiemannianVolume_apply α hs,
    inter_eq_left.2 hsα', inter_eq_left.2 hsβ']
  -- Change variables along `Φ` read in the charts at `α` and `β`.
  let A := extChartAt I α '' s
  let g := extChartAt I' β ∘ Φ ∘ (extChartAt I α).symm
  have hA : MeasurableSet A := hs.image_extChartAt α hsα'
  have hA_range : A ⊆ range I :=
    (image_mono hsα').trans ((extChartAt I α).image_source_eq_target.subset.trans
      (extChartAt_target_subset_range α))
  have himage : g '' A = extChartAt I' β '' (Φ '' s) := by
    simp only [A, g, image_image]
    apply image_congr
    intro x hx
    simp only [Function.comp_apply, (extChartAt I α).left_inv (hsα' hx)]
  have hinjA : InjOn g A := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    simp only [g, Function.comp_apply, (extChartAt I α).left_inv (hsα' hx),
      (extChartAt I α).left_inv (hsα' hx')] at h
    rw [hinj hx hx' ((extChartAt I' β).injOn (hsβ' (mem_image_of_mem Φ hx))
      (hsβ' (mem_image_of_mem Φ hx')) h)]
  have hderiv (x : M) (hx : x ∈ s) :
      HasFDerivWithinAt g (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β) (Φ x) ∘L mfderiv I I' Φ x ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x) :
          E →L[ℝ] E) (range I) (extChartAt I α x) :=
    (hΦ x hx).hasMFDerivAt.hasFDerivWithinAt_of_mem_source (hsα hx) (hsβ hx)
  rw [← himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul (Module.finBasis ℝ E).addHaar hA
    (f' := fun y ↦ fderivWithin ℝ g (range I) y) ?_ hinjA]
  · apply setLIntegral_congr_fun hA
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [(hderiv x hx).fderivWithin (I.uniqueDiffOn _ (hA_range (mem_image_of_mem _ hx))),
      (extChartAt I α).left_inv (hsα' hx)]
    simp only [g, Function.comp_apply, (extChartAt I α).left_inv (hsα' hx),
      (extChartAt I' β).left_inv (hsβ' (mem_image_of_mem Φ hx))]
    rw [chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv (β := β) (hsα hx) (hsβ hx)
      (hinner x hx), ENNReal.ofReal_mul (abs_nonneg _)]
  · rintro _ ⟨x, hx, rfl⟩
    exact (hderiv x hx).differentiableWithinAt.hasFDerivWithinAt.mono hA_range

/-- **Isometry invariance of the Riemannian volume.** A differentiable homeomorphism whose tangent
maps preserve the Riemannian inner products carries the Riemannian volume of `M` to the Riemannian
volume of `N`. -/
theorem _root_.Homeomorph.measurePreserving_riemannianVolume [LindelofSpace M] [LindelofSpace N]
    (Φ : M ≃ₜ N) (hΦ : MDifferentiable I I' Φ)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    MeasurePreserving Φ (riemannianVolume I M) (riemannianVolume I' N) := by
  refine ⟨Φ.measurable, eq_riemannianVolume_iff.2 fun β ↦ ?_⟩
  set S := (chartAt H' β).source
  have hS : MeasurableSet S := (chartAt H' β).open_source.measurableSet
  rw [Measure.restrict_map Φ.measurable hS]
  -- Pull the chart volume at `β` back to `M` and compare it with the Riemannian volume of `M`
  -- chart by chart, on a countable cover of `M` by chart sources.
  suffices h : (riemannianVolume I M).restrict (Φ ⁻¹' S) =
      (chartRiemannianVolume (I := I') β).map Φ.symm by
    rw [h, Measure.map_map Φ.measurable Φ.symm.measurable, Φ.self_comp_symm, Measure.map_id]
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : M ↦ (chartAt H x).source) fun x ↦ chart_source_mem_nhds H x
  refine Measure.ext_of_biUnion_eq_univ ht hcover fun α _ ↦ ?_
  ext s hs
  have hsα : MeasurableSet (s ∩ (chartAt H α).source) :=
    hs.inter (chartAt H α).open_source.measurableSet
  have hA : MeasurableSet (s ∩ (chartAt H α).source ∩ Φ ⁻¹' S) :=
    hsα.inter (hS.preimage Φ.measurable)
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Measure.restrict_apply hsα,
    Measure.map_apply Φ.symm.measurable hsα, ← chartRiemannianVolume_restrict_source β,
    Measure.restrict_apply' hS, Homeomorph.preimage_symm, ← image_inter_preimage,
    riemannianVolume_apply_of_subset (inter_subset_left.trans inter_subset_right),
    chartRiemannianVolume_image_of_inner_mfderiv hA
      (by rw [Φ.image_eq_preimage_symm]; exact hA.preimage Φ.symm.measurable)
      Φ.injective.injOn (inter_subset_left.trans inter_subset_right)
      (fun x hx ↦ hx.2) (fun x _ ↦ hΦ x) (fun x _ ↦ hinner x)]

end Measure

end TauCeti
