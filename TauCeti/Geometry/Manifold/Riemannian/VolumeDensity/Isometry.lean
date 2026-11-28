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
import TauCeti.Geometry.Manifold.InvarianceOfDomain
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
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
matching the coordinate bases and their normalized Haar measures, using
`Module.Basis.measurePreserving_equiv` (based on Mathlib's `Module.Basis.map_addHaar`) and
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`.

The statement is the invariance of the Riemannian density under isometries, as in
J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
(Riemannian volume forms and densities).

## Main results

* `TauCeti.chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv`: the chart volume densities of
  two Riemannian manifolds differ by the absolute Jacobian determinant of a map whose tangent map
  preserves the inner products, after identifying their model spaces by an equivalence matching
  the coordinate bases.
* `TauCeti.chartRiemannianVolume_image_of_inner_mfderiv`: such a map, injective on a subset of a
  chart source, carries its chart volume to the chart volume of its image. The set must be
  measurable and its image must lie in the target chart source; independent models must have
  equal dimension.
* `TauCeti.riemannianVolume_image_of_inner_mfderiv`: the global image formula for
  a map injective on a measurable set, over independent model vector spaces of equal dimension.
* `Homeomorph.measurePreserving_riemannianVolume`: a homeomorphism whose tangent maps preserve
  the inner products preserves the Riemannian volume.
* `TauCeti.measurePreserving_smul_riemannianVolume`: for a group acting by smooth maps, a
  translation whose tangent maps preserve the inner products preserves the Riemannian volume.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section CrossModel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]

/-- If the tangent map of `f` at `x` preserves the Riemannian inner products, then the source
chart density is the target chart density multiplied by the absolute coordinate determinant.
The equivalence `C` identifies the independent model spaces and matches their coordinate bases,
up to the reindexing `σ`. -/
theorem chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv
    {C : E ≃L[ℝ] F} {σ : Fin (Module.finrank ℝ F) ≃ Fin (Module.finrank ℝ E)}
    (hC : (Module.finBasis ℝ E).map C.toLinearEquiv = (Module.finBasis ℝ F).reindex σ)
    {f : M → N} {α x : M} {β : N}
    (hxα : x ∈ (chartAt H α).source) (hxβ : f x ∈ (chartAt H' β).source)
    (hinner : ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' f x v, mfderiv I I' f x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartVolumeDensity (I := I) α x =
      |(C.symm.toContinuousLinearMap ∘L
        (mfderiv I' 𝓘(ℝ, F) (extChartAt I' β) (f x) ∘L mfderiv I I' f x ∘L
          mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x)) :
          E →L[ℝ] E).det| *
      chartVolumeDensity (I := I') β (f x) := by
  let D : E →L[ℝ] TangentSpace I' (f x) := mfderiv I I' f x ∘L
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x)
  have hgram : Matrix.gram ℝ (fun i ↦ D (Module.finBasis ℝ E i)) =
      chartGramMatrix (I := I) α x := by
    ext i j
    -- The inverse chart derivative takes the model basis to the source chart frame.
    rw [Matrix.gram_apply, chartGramMatrix_apply, chartLocalFrame_eq_symmL,
      chartLocalFrame_eq_symmL, TangentBundle.symmL_trivializationAt hxα]
    exact hinner _ _
  rw [chartVolumeDensity_def, ← hgram]
  have h := sqrt_det_gram_eq_abs_det_mul_chartVolumeDensity hC hxβ D
  -- Read the self-model tangent spaces as model vector spaces in the coordinate maps.
  convert h using 2

section Measure

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace I' y)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

omit [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace I' y)] in
private theorem setLIntegral_chartVolumeDensity_image_of_inner_mfderiv
    {C : E ≃L[ℝ] F} {σ : Fin (Module.finrank ℝ F) ≃ Fin (Module.finrank ℝ E)}
    (hb : (Module.finBasis ℝ E).map C.toLinearEquiv = (Module.finBasis ℝ F).reindex σ)
    {f : M → N} {α : M} {β : N} {s : Set M}
    (hs : MeasurableSet s) (hinj : InjOn f s)
    (hsα : s ⊆ (chartAt H α).source) (hsβ : MapsTo f s (chartAt H' β).source)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' f x v, mfderiv I I' f x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    ∫⁻ y in (C.symm ∘ extChartAt I' β ∘ f ∘ (extChartAt I α).symm) ''
        (extChartAt I α '' s),
      ENNReal.ofReal (chartVolumeDensity (I := I') β ((extChartAt I' β).symm (C y)))
        ∂(Module.finBasis ℝ E).addHaar =
      ∫⁻ y in extChartAt I α '' s,
        ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y))
          ∂(Module.finBasis ℝ E).addHaar := by
  have hf (x : M) (hx : x ∈ s) : MDifferentiableAt I I' f x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  have hsα' : s ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hsβ' : f '' s ⊆ (extChartAt I' β).source := by
    simpa only [extChartAt_source] using hsβ.image_subset
  let A := extChartAt I α '' s
  let g := C.symm ∘ extChartAt I' β ∘ f ∘ (extChartAt I α).symm
  have hA : MeasurableSet A := hs.image_extChartAt α hsα'
  have hA_range : A ⊆ range I :=
    (image_mono hsα').trans ((extChartAt I α).image_source_eq_target.subset.trans
      (extChartAt_target_subset_range α))
  have hinjg : InjOn g A := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    simp only [g, Function.comp_apply, (extChartAt I α).left_inv (hsα' hx),
      (extChartAt I α).left_inv (hsα' hy), C.symm.injective.eq_iff] at h
    rw [hinj hx hy ((extChartAt I' β).injOn (hsβ' (mem_image_of_mem _ hx))
      (hsβ' (mem_image_of_mem _ hy)) h)]
  let D (x : M) : E →L[ℝ] E := C.symm.toContinuousLinearMap ∘L
    (mfderiv I' 𝓘(ℝ, F) (extChartAt I' β) (f x) ∘L mfderiv I I' f x ∘L
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x))
  have hD (y : E) (hy : y ∈ A) :
      HasFDerivWithinAt g (D ((extChartAt I α).symm y)) A y := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [(extChartAt I α).left_inv (hsα' hx)]
    exact (C.symm : F →L[ℝ] E).hasFDerivAt.comp_hasFDerivWithinAt _
      (((hf x hx).hasMFDerivAt.hasFDerivWithinAt_of_mem_source (hsα hx) (hsβ hx)).mono hA_range)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (Module.finBasis ℝ E).addHaar hA hD hinjg]
  refine setLIntegral_congr_fun hA ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [D, g, Function.comp_apply, C.apply_symm_apply,
    (extChartAt I α).left_inv (hsα' hx),
    (extChartAt I' β).left_inv (hsβ' (mem_image_of_mem _ hx))]
  rw [chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv hb
      (hsα hx) (hsβ hx) (hinner x hx),
    ENNReal.ofReal_mul (abs_nonneg _)]

/-- An injective map on a measurable subset of the chart at `α`, with image in the chart at
`β`, preserves chart volume if its tangent maps preserve inner products at points of the set
and the two model vector spaces have equal dimension. No neighborhood isometry is assumed.

The coordinate change-of-variables argument is adapted from
`TauCeti.chartRiemannianVolume_restrict_overlap`. -/
theorem chartRiemannianVolume_image_of_inner_mfderiv
    {f : M → N} {α : M} {β : N} {s : Set M}
    (hs : MeasurableSet s) (hinj : InjOn f s)
    (hsα : s ⊆ (chartAt H α).source) (hsβ : MapsTo f s (chartAt H' β).source)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' f x v, mfderiv I I' f x w⟫_ℝ = ⟪v, w⟫_ℝ)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    chartRiemannianVolume (I := I') β (f '' s) = chartRiemannianVolume (I := I) α s := by
  have hf (x : M) (hx : x ∈ s) : MDifferentiableAt I I' f x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  have hsα' : s ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hsβ' : f '' s ⊆ (extChartAt I' β).source := by
    simpa only [extChartAt_source] using hsβ.image_subset
  let C := ((Module.finBasis ℝ E).equiv (Module.finBasis ℝ F)
    (finCongr hdim)).toContinuousLinearEquiv
  have hb : (Module.finBasis ℝ E).map C.toLinearEquiv =
      (Module.finBasis ℝ F).reindex (finCongr hdim).symm := by
    dsimp only [C]
    rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, Module.Basis.map_equiv]
  let A := extChartAt I α '' s
  let g := C.symm ∘ extChartAt I' β ∘ f ∘ (extChartAt I α).symm
  have himage : g '' A = C ⁻¹' (extChartAt I' β '' (f '' s)) := by
    rw [← C.image_symm_eq_preimage]
    simp only [g, A, image_comp]
    rw [(extChartAt I α).symm_image_image_of_subset_source hsα']
  have hC : MeasurableEmbedding C := C.toHomeomorph.measurableEmbedding
  have hHaar : MeasurePreserving C (Module.finBasis ℝ E).addHaar
      (Module.finBasis ℝ F).addHaar :=
    (Module.finBasis ℝ E).measurePreserving_equiv (Module.finBasis ℝ F) (finCongr hdim)
  have : PolishSpace H := I.isClosedEmbedding.polishSpace
  have : T2Space H' := I'.isClosedEmbedding.isEmbedding.t2Space
  have hfs : MeasurableSet (f '' s) :=
    hs.image_of_continuousOn_injOn_chartAt (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
      hinj hsα hsβ
  rw [chartRiemannianVolume_apply β hfs, inter_eq_left.2 hsβ',
    chartRiemannianVolume_apply α hs, inter_eq_left.2 hsα']
  calc
    _ = ∫⁻ y in g '' A,
        ENNReal.ofReal (chartVolumeDensity (I := I') β ((extChartAt I' β).symm (C y)))
          ∂(Module.finBasis ℝ E).addHaar := by
      rw [himage]
      exact (hHaar.setLIntegral_comp_preimage_emb hC _ _).symm
    _ = _ := setLIntegral_chartVolumeDensity_image_of_inner_mfderiv hb hs hinj hsα hsβ hinner

/-- **Volume of an injective isometric image in equal dimensions.** If `Φ` is injective on a
measurable set `s` and preserves the tangent inner products there, then `Φ '' s` has the
Riemannian volume of `s`. Tangent inner-product preservation is required only at points of `s`,
with no neighborhood isometry assumption; for instance,
a Riemannian covering map preserves the volume of every measurable set on which it is injective. -/
theorem riemannianVolume_image_of_inner_mfderiv
    [LindelofSpace M] [LindelofSpace N]
    {Φ : M → N} {s : Set M} (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
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
  exact chartRiemannianVolume_image_of_inner_mfderiv hu (hinj.mono hus)
    (huV.trans inter_subset_left) hmaps (fun y hy ↦ hinner y (hus hy)) hdim

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
  · have hs0 : s = ∅ := eq_empty_iff_forall_notMem.2 fun y _ ↦ isEmptyElim (Φ.symm y)
    simp only [hs0, measure_empty]
  have hdim := Φ.finrank_eq_of_chartedSpace I I'
  rw [Measure.map_apply Φ.measurable hs,
    ← riemannianVolume_image_of_inner_mfderiv
      (hs.preimage Φ.measurable) Φ.injective.injOn (fun x _ ↦ hinner x) hdim, Φ.image_preimage]

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

section SMul

open scoped ContDiff

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]

/-- **Isometric translations preserve volume.** For a group acting on `M` by smooth maps, if the
differentials of the translation `x ↦ g • x` preserve the Riemannian inner products, then it
preserves the Riemannian volume. -/
theorem measurePreserving_smul_riemannianVolume (g : G)
    (hg : ∀ (x : M) (u w : TangentSpace I x),
      ⟪mfderiv I I (g • ·) x u, mfderiv I I (g • ·) x w⟫_ℝ = ⟪u, w⟫_ℝ) :
    MeasurePreserving (g • · : M → M) (riemannianVolume I M) (riemannianVolume I M) := by
  simpa only [RiemannianIsometry.coe_constSMul] using
    (RiemannianIsometry.constSMul g hg).measurePreserving_riemannianVolume

end SMul

end TauCeti
