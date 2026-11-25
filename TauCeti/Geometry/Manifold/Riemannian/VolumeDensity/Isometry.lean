/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
import TauCeti.Geometry.Manifold.Polish

/-!
# Isometry invariance of the Riemannian volume

A homeomorphism `Φ : M ≃ₜ N` between manifolds with continuous Riemannian metrics whose tangent
maps preserve the Riemannian inner products carries the Riemannian volume of `M` to the
Riemannian volume of `N`; such a map is automatically differentiable. In particular isometric
manifolds have the same Riemannian volume, which is what makes the total volume a Riemannian
invariant.

The isometry condition is stated pointwise, on the tangent maps, and no orientation is used, so
orientation-reversing isometries and manifolds with boundary or corners are covered. The two
manifolds may have different model vector spaces. The chart comparison uses an equivalence
matching the coordinate bases and their normalized Haar measures.

The statement is the invariance of the Riemannian density under isometries, as in
J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
(Riemannian volume forms and densities).

## Main results

* `TauCeti.chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv`: the chart volume densities of
  two Riemannian manifolds differ by the absolute Jacobian determinant of a map whose tangent map
  preserves the inner products.
* `TauCeti.chartRiemannianVolume_image_of_inner_mfderiv`: such a map, injective on a subset of a
  chart source, carries its chart volume to the chart volume of its image.
* `TauCeti.riemannianVolume_image_of_inner_mfderiv`: such a map, injective on any measurable set,
  carries its Riemannian volume to the Riemannian volume of its image.
* `TauCeti.riemannianVolume_image_of_inner_mfderiv_of_finrank_eq`: the same image formula for
  different model vector spaces of equal dimension.
* `Homeomorph.measurePreserving_riemannianVolume`: a homeomorphism whose tangent maps preserve
  the inner products preserves the Riemannian volume.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

private theorem finrank_le_of_chartedSpace_homeomorph
    {E H F H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ F H')
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : M ≃ₜ N) (x : M) : Module.finrank ℝ E ≤ Module.finrank ℝ F := by
  let c := (chartAt H x).trans I.interiorChart
  obtain ⟨z, hz⟩ := interior_extChartAt_target_nonempty I x
  have hz' : z ∈ c.target := by
    have hzI := interior_mono (extChartAt_target_subset_range (I := I) x) hz
    have hzt := interior_subset hz
    rw [extChartAt_target I x] at hzt
    rw [show c = (chartAt H x).trans I.interiorChart from rfl,
      OpenPartialHomeomorph.trans_target, ModelWithCorners.interiorChart_target]
    exact ⟨hzI, by simpa only [ModelWithCorners.interiorChart_coe_symm] using hzt.1⟩
  let y := Φ (c.symm z)
  let e := (c.symm.trans Φ.toOpenPartialHomeomorph).trans (chartAt H' y)
  have hz'' : z ∈ e.source := by
    simpa only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_apply,
      preimage_univ, inter_univ, mem_inter_iff, mem_preimage, OpenPartialHomeomorph.trans_apply]
      using And.intro hz' (mem_chart_source H' y)
  have : Nonempty e.source := ⟨⟨z, hz''⟩⟩
  exact e.open_source.isOpenEmbedding_subtypeVal.finrank_le_of_isEmbedding
    (I'.isClosedEmbedding.isEmbedding.comp e.isOpenEmbedding_restrict.isEmbedding)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section CrossModel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]

private def finBasisEquiv (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : E ≃L[ℝ] F :=
  ((Module.finBasis ℝ E).equiv (Module.finBasis ℝ F) (finCongr hdim)).toContinuousLinearEquiv

private theorem finBasis_map_finBasisEquiv (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    (Module.finBasis ℝ E).map (finBasisEquiv hdim).toLinearEquiv =
      (Module.finBasis ℝ F).reindex (finCongr hdim).symm := by
  rw [finBasisEquiv, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, Module.Basis.map_equiv]

private abbrev chartDerivative (f : M → N) (α : M) (β : N) (x : M) : E →L[ℝ] F :=
  mfderiv I' 𝓘(ℝ, F) (extChartAt I' β) (f x) ∘L mfderiv I I' f x ∘L
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x)

private theorem chartVolumeDensity_eq_abs_det_mul_of_basis
    {C : E ≃L[ℝ] F} {σ : Fin (Module.finrank ℝ F) ≃ Fin (Module.finrank ℝ E)}
    (hC : (Module.finBasis ℝ E).map C.toLinearEquiv = (Module.finBasis ℝ F).reindex σ)
    {f : M → N} {α x : M} {β : N}
    (hxα : x ∈ (chartAt H α).source) (hxβ : f x ∈ (chartAt H' β).source)
    (hinner : ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' f x v, mfderiv I I' f x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartVolumeDensity (I := I) α x =
      |(C.symm.toContinuousLinearMap ∘L
        chartDerivative (I := I) (I' := I') f α β x).det| *
      chartVolumeDensity (I := I') β (f x) := by
  have hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxα
  have hβ : f x ∈ (trivializationAt F (TangentSpace I') β).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxβ
  let b := Module.finBasis ℝ E
  let bα := (trivializationAt E (TangentSpace I) α).basisAt b hα
  let bβ := (trivializationAt F (TangentSpace I') β).basisAt (b.map C.toLinearEquiv) hβ
  let L := C.symm.toContinuousLinearMap ∘L chartDerivative (I := I) (I' := I') f α β x
  have hmat : LinearMap.toMatrix bα bβ (mfderiv I I' f x).toLinearMap =
      LinearMap.toMatrix b b L.toLinearMap := by
    ext i j
    simp only [LinearMap.toMatrix_apply, bα, bβ, Trivialization.basisAt, Module.Basis.map_apply,
      Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
      Trivialization.linearEquivAt_symm_apply, Trivialization.linearEquivAt_apply]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hβ,
      ← Trivialization.symmL_apply (R := ℝ) _ hα, TangentBundle.symmL_trivializationAt hxα,
      TangentBundle.continuousLinearMapAt_trivializationAt hxβ]
    rfl
  have htarget : (LinearMap.BilinForm.toMatrix bβ (innerₗ (TangentSpace I' (f x)))).det =
      (chartGramMatrix (I := I') β (f x)).det := by
    have hgram : LinearMap.BilinForm.toMatrix bβ (innerₗ (TangentSpace I' (f x))) =
        Matrix.gram ℝ bβ := by
      ext i j
      simp only [LinearMap.BilinForm.toMatrix_apply, innerₗ_apply_apply, Matrix.gram_apply]
    rw [hgram, show bβ = _ from congrArg
      (fun c ↦ (trivializationAt F (TangentSpace I') β).basisAt c hβ)
      hC, gram_basisAt_finBasis_reindex,
      Matrix.det_submatrix_equiv_self]
  have hform : innerₗ (TangentSpace I x) = LinearMap.BilinForm.comp
      (innerₗ (TangentSpace I' (f x))) (mfderiv I I' f x).toLinearMap
      (mfderiv I I' f x).toLinearMap := by
    ext v w
    simp [hinner]
  have hdet : (chartGramMatrix (I := I) α x).det =
      L.det ^ 2 * (chartGramMatrix (I := I') β (f x)).det := by
    rw [chartGramMatrix_eq_toMatrix α hα, hform, LinearMap.BilinForm.toMatrix_comp bβ bα,
      hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, htarget,
      LinearMap.det_toMatrix, ContinuousLinearMap.det]
    ring
  rw [chartVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    chartVolumeDensity_def]

section Measure

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace I' y)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

private theorem chartRiemannianVolume_image_of_inner_mfderiv_aux
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) {f : M → N} {α : M} {β : N} {s : Set M}
    (hs : MeasurableSet s) (hinj : InjOn f s)
    (hsα : s ⊆ (chartAt H α).source) (hsβ : MapsTo f s (chartAt H' β).source)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' f x v, mfderiv I I' f x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartRiemannianVolume (I := I') β (f '' s) = chartRiemannianVolume (I := I) α s := by
  have hf (x : M) (hx : x ∈ s) : MDifferentiableAt I I' f x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  have hsα' : s ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hsβ' : f '' s ⊆ (extChartAt I' β).source := by
    simpa only [extChartAt_source] using hsβ.image_subset
  let C := finBasisEquiv hdim
  let A := extChartAt I α '' s
  let g := C.symm ∘ extChartAt I' β ∘ f ∘ (extChartAt I α).symm
  have hA : MeasurableSet A := hs.image_extChartAt α hsα'
  have hA_range : A ⊆ range I :=
    (image_mono hsα').trans ((extChartAt I α).image_source_eq_target.subset.trans
      (extChartAt_target_subset_range α))
  have himage : g '' A = C ⁻¹' (extChartAt I' β '' (f '' s)) := by
    rw [← C.image_symm_eq_preimage, image_comp]
    congr 1
    rw [image_image, image_image]
    exact image_congr fun x hx ↦ by
      simp only [Function.comp_apply, (extChartAt I α).left_inv (hsα' hx)]
  have hinjg : InjOn g A := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    simp only [g, Function.comp_apply, (extChartAt I α).left_inv (hsα' hx),
      (extChartAt I α).left_inv (hsα' hy), C.symm.injective.eq_iff] at h
    rw [hinj hx hy ((extChartAt I' β).injOn (hsβ' (mem_image_of_mem _ hx))
      (hsβ' (mem_image_of_mem _ hy)) h)]
  let D (x : M) := C.symm.toContinuousLinearMap ∘L chartDerivative (I := I) (I' := I') f α β x
  have hD (y : E) (hy : y ∈ A) :
      HasFDerivWithinAt g (D ((extChartAt I α).symm y)) A y := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [(extChartAt I α).left_inv (hsα' hx)]
    exact (C.symm : F →L[ℝ] E).hasFDerivAt.comp_hasFDerivWithinAt _
      (((hf x hx).hasMFDerivAt.hasFDerivWithinAt_of_mem_source (hsα hx) (hsβ hx)).mono hA_range)
  have hHaar : (Module.finBasis ℝ E).addHaar.map C = (Module.finBasis ℝ F).addHaar := by
    rw [Module.Basis.map_addHaar, finBasis_map_finBasisEquiv, Module.Basis.addHaar_reindex]
  have hC : MeasurableEmbedding C := C.toHomeomorph.measurableEmbedding
  have : PolishSpace H := I.isClosedEmbedding.polishSpace
  have : T2Space H' := I'.isClosedEmbedding.isEmbedding.t2Space
  have hfs : MeasurableSet (f '' s) :=
    hs.image_of_continuousOn_injOn_chartAt (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
      hinj hsα hsβ
  rw [chartRiemannianVolume_apply β hfs, inter_eq_left.2 hsβ',
    chartRiemannianVolume_apply α hs, inter_eq_left.2 hsα',
    ← hHaar, hC.restrict_map, hC.lintegral_map, ← himage,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (Module.finBasis ℝ E).addHaar hA hD hinjg]
  refine setLIntegral_congr_fun hA ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [g, Function.comp_apply, C.apply_symm_apply, (extChartAt I α).left_inv (hsα' hx),
    (extChartAt I' β).left_inv (hsβ' (mem_image_of_mem _ hx))]
  rw [chartVolumeDensity_eq_abs_det_mul_of_basis (finBasis_map_finBasisEquiv hdim)
      (hsα hx) (hsβ hx) (hinner x hx),
    ENNReal.ofReal_mul (abs_nonneg _)]

/-- **Volume of an injective isometric image in equal dimensions.** If `Φ` is injective on a
measurable set `s` and preserves the tangent inner products there, then `Φ '' s` has the
Riemannian volume of `s`. The map is only required to be a local isometry along `s`; for instance,
a Riemannian covering map preserves the volume of every measurable set on which it is injective. -/
theorem riemannianVolume_image_of_inner_mfderiv_of_finrank_eq
    [LindelofSpace M] [LindelofSpace N]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {Φ : M → N} {s : Set M} (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    riemannianVolume I' N (Φ '' s) = riemannianVolume I M s := by
  -- The models are a Polish space and a Hausdorff space, and a Lindelöf manifold modelled on a
  -- finite-dimensional space is second countable, hence hereditarily Lindelöf.
  have : PolishSpace H := I.isClosedEmbedding.polishSpace
  have : T2Space H' := I'.isClosedEmbedding.isEmbedding.t2Space
  have := ChartedSpace.secondCountable_of_lindelof H M
  have hΦ (x : M) (hx : x ∈ s) : MDifferentiableAt I I' Φ x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  -- The two volumes agree near each point `x` of `s`, on the open set `V x` which lies in the
  -- chart source at `x` and is mapped by `Φ` into the chart source at `Φ x`.
  let V (x : M) : Set M := (chartAt H x).source ∩ interior (Φ ⁻¹' (chartAt H' (Φ x)).source)
  have hV (x : M) (hx : x ∈ s) : V x ∈ 𝓝 x :=
    ((chartAt H x).open_source.inter isOpen_interior).mem_nhds ⟨mem_chart_source H x,
      mem_interior_iff_mem_nhds.2 <|
        (hΦ x hx).continuousAt.preimage_mem_nhds (chart_source_mem_nhds H' (Φ x))⟩
  -- The restriction of `Φ` to `s` is a measurable embedding, by the Lusin–Souslin theorem.
  refine measure_image_eq_of_locally_eq hs (ContinuousOn.measurableEmbedding_chartedSpace H H'
    (fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt) hs hinj) hV
    fun x _ u hu hus huV ↦ ?_
  have hmaps : MapsTo Φ u (chartAt H' (Φ x)).source := fun y hy ↦
    interior_subset (s := Φ ⁻¹' _) (huV hy).2
  rw [riemannianVolume_apply_of_subset (α := Φ x) hmaps.image_subset,
    riemannianVolume_apply_of_subset (α := x) (huV.trans inter_subset_left)]
  exact chartRiemannianVolume_image_of_inner_mfderiv_aux hdim hu (hinj.mono hus)
    (huV.trans inter_subset_left) hmaps fun y hy ↦ hinner y (hus hy)

/-- **Isometry invariance of the Riemannian volume.** A homeomorphism whose tangent maps preserve
the Riemannian inner products carries the Riemannian volume of `M` to the Riemannian volume of
`N`, even over different model vector spaces. -/
theorem _root_.Homeomorph.measurePreserving_riemannianVolume [LindelofSpace M] [LindelofSpace N]
    (Φ : M ≃ₜ N)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    MeasurePreserving Φ (riemannianVolume I M) (riemannianVolume I' N) := by
  refine ⟨Φ.measurable, Measure.ext fun s hs ↦ ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · let : IsEmpty M := hM
    have hs0 : s = ∅ := eq_empty_iff_forall_notMem.2 fun y _ ↦ isEmptyElim (Φ.symm y)
    simp only [hs0, measure_empty]
  obtain ⟨x⟩ := hM
  have hdim := (finrank_le_of_chartedSpace_homeomorph I I' Φ x).antisymm
    (finrank_le_of_chartedSpace_homeomorph I' I Φ.symm (Φ x))
  rw [Measure.map_apply Φ.measurable hs,
    ← riemannianVolume_image_of_inner_mfderiv_of_finrank_eq hdim
      (hs.preimage Φ.measurable) Φ.injective.injOn (fun x _ ↦ hinner x), Φ.image_preimage]

end Measure

namespace RiemannianIsometry

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace I' y)]

/-- A Riemannian isometry preserves the Riemannian volume measure.

This packages the general homeomorphism theorem at the canonical `RiemannianIsometry` API. -/
theorem measurePreserving_riemannianVolume [LindelofSpace M] [LindelofSpace N]
    (Φ : RiemannianIsometry I I' M N) :
    MeasurePreserving Φ (riemannianVolume I M) (riemannianVolume I' N) := by
  have h := Φ.toDiffeomorph.toHomeomorph.measurePreserving_riemannianVolume (I := I) (I' := I') ?_
  · rwa [Diffeomorph.coe_toHomeomorph, coe_toDiffeomorph] at h
  · intro x v w
    rw [Diffeomorph.coe_toHomeomorph, coe_toDiffeomorph]
    exact Φ.inner_mfderiv x v w

end RiemannianIsometry

end CrossModel

section SameModel

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
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
  have hC : (ContinuousLinearEquiv.refl ℝ E).symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by
    ext y
    rfl
  have hb : (Module.finBasis ℝ E).map (ContinuousLinearEquiv.refl ℝ E).toLinearEquiv =
      (Module.finBasis ℝ E).reindex (Equiv.refl _) := by
    ext i
    simp only [Module.Basis.map_apply, Module.Basis.reindex_apply]
    rfl
  simpa only [chartDerivative, hC, ContinuousLinearMap.id_comp] using
    (chartVolumeDensity_eq_abs_det_mul_of_basis (I := I) (I' := I')
      hb hxα hxβ hinner)

section Measure

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-- A map which is injective on a measurable subset `s` of the chart source at
`α`, maps `s` into the chart source at `β`, and whose tangent maps at points of `s` preserve the
Riemannian inner products, carries the chart volume of `s` at `α` to the chart volume of its image
at `β`. -/
theorem chartRiemannianVolume_image_of_inner_mfderiv {Φ : M → N} {α : M} {β : N} {s : Set M}
    (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hsα : s ⊆ (chartAt H α).source) (hsβ : MapsTo Φ s (chartAt H' β).source)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartRiemannianVolume (I := I') β (Φ '' s) = chartRiemannianVolume (I := I) α s :=
  chartRiemannianVolume_image_of_inner_mfderiv_aux rfl hs hinj hsα hsβ hinner

/-- **Volume of an injective isometric image.** If `Φ` is injective on a measurable set `s` and
its tangent maps at points of `s` preserve the Riemannian inner products, then `Φ '' s` has the
Riemannian volume of `s`. The map is only required to be a local isometry along `s`; for instance,
a Riemannian covering map preserves the volume of every measurable set on which it is injective. -/
theorem riemannianVolume_image_of_inner_mfderiv [LindelofSpace M] [LindelofSpace N]
    {Φ : M → N} {s : Set M} (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    riemannianVolume I' N (Φ '' s) = riemannianVolume I M s :=
  riemannianVolume_image_of_inner_mfderiv_of_finrank_eq rfl hs hinj hinner

end Measure

end SameModel

end TauCeti
