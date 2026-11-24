/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.MeasureTheory.Function.AreaFormula.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Polish

/-!
# Riemannian volume of an isometrically immersed manifold

Let `M` be a Lindelöf (equivalently, second countable) manifold without boundary, modelled on a
real vector space of dimension `m`, with a continuous Riemannian metric, and let `Φ : M → V` be a
map into a finite-dimensional real inner product space whose tangent maps preserve the inner
products, `⟪dΦ_x v, dΦ_x w⟫ = g_x(v, w)`. This is the situation of
a submanifold of Euclidean space with its induced metric, such as the round sphere. This file
proves that `Φ` carries the Riemannian volume of `M` to the normalized `m`-dimensional Hausdorff
measure `μHE[m]` of `V`: for every measurable set `s` on which `Φ` is injective,

`μHE[m] (Φ '' s) = vol_g s`.

In particular, for an injective `Φ`, the pushforward of the Riemannian volume along `Φ` is `μHE[m]`
restricted to the image of `Φ`. The intrinsic volume of a submanifold therefore agrees with its
extrinsic surface measure.

Pointwise, for a map `f` from an inner product space `F` into `M` and an orthonormal basis of `F`,
the Riemannian Jacobian of `f` is the Euclidean Jacobian `(fderiv ℝ (Φ ∘ f) x).normDet` of the
composite map into `V`. Integrating this in charts, the change of variables formula for the
Riemannian volume and the area formula for `μHE[m]` give the two sides of the identity.

## Main results

* `TauCeti.riemannianJacobian_eq_normDet_fderiv_comp`: the Riemannian Jacobian of `f` is the
  Euclidean Jacobian of `Φ ∘ f`.
* `TauCeti.euclideanHausdorffMeasure_image_eq_riemannianVolume_of_inner_mfderiv`:
  `μHE[m] (Φ '' s) = vol_g s` for a measurable set `s` on which `Φ` is injective.
* `TauCeti.map_riemannianVolume_eq_restrict_euclideanHausdorffMeasure_of_inner_mfderiv`: for an
  injective `Φ`, the pushforward of the Riemannian volume is `μHE[m]` restricted to the range of
  `Φ`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the Riemannian density).
-/

public section

open Bundle MeasureTheory Set
open scoped ENNReal InnerProductSpace Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The Riemannian Jacobian through an isometric immersion.** If the tangent map of `Φ : M → V`
at `f x` preserves the inner products, then the Riemannian Jacobian of `f : F → M` at `x`, for an
orthonormal basis of `F`, is the Euclidean Jacobian `(fderiv ℝ (Φ ∘ f) x).normDet`. -/
theorem riemannianJacobian_eq_normDet_fderiv_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (b : OrthonormalBasis ι ℝ F)
    {Φ : M → V} {f : F → M} {x : F} (hf : MDifferentiableAt 𝓘(ℝ, F) I f x)
    (hinner : ∀ v w : TangentSpace I (f x),
      ⟪mfderiv I 𝓘(ℝ, V) Φ (f x) v, mfderiv I 𝓘(ℝ, V) Φ (f x) w⟫_ℝ = ⟪v, w⟫_ℝ) :
    riemannianJacobian (I := I) b.toBasis f x =
      LinearMap.normDet (fderiv ℝ (Φ ∘ f) x).toLinearMap := by
  have hΦ : MDifferentiableAt I 𝓘(ℝ, V) Φ (f x) :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner v v
  have hgram : Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, F) I f x (b.toBasis i)) =
      Matrix.gram ℝ (fun i ↦ (fderiv ℝ (Φ ∘ f) x).toLinearMap (b i)) := by
    ext i j
    simp only [Matrix.gram_apply, OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
    rw [fderiv_comp_apply_eq_mfderiv hΦ hf, fderiv_comp_apply_eq_mfderiv hΦ hf]
    exact (hinner _ _).symm
  have hsq := LinearMap.normDet_sq_eq_det_gram (fderiv ℝ (Φ ∘ f) x).toLinearMap b
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
  rw [riemannianJacobian_eq_sqrt_det_gram, hgram, ← hsq, Real.sqrt_sq (LinearMap.normDet_nonneg _)]

/-- If the tangent map of `Φ` at `f x` preserves the inner products and `f` has injective
differential at `x`, then `Φ ∘ f` has injective derivative at `x`. -/
private theorem injective_fderiv_comp_of_inner_mfderiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : M → V} {f : F → M} {x : F} (hf : MDifferentiableAt 𝓘(ℝ, F) I f x)
    (hfD : Function.Injective (mfderiv 𝓘(ℝ, F) I f x))
    (hinner : ∀ v w : TangentSpace I (f x),
      ⟪mfderiv I 𝓘(ℝ, V) Φ (f x) v, mfderiv I 𝓘(ℝ, V) Φ (f x) w⟫_ℝ = ⟪v, w⟫_ℝ) :
    Function.Injective (fderiv ℝ (Φ ∘ f) x) := by
  have hΦ : MDifferentiableAt I 𝓘(ℝ, V) Φ (f x) :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner v v
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ hfD ?_
  have h0 := hinner (mfderiv 𝓘(ℝ, F) I f x a) (mfderiv 𝓘(ℝ, F) I f x a)
  rw [← fderiv_comp_apply_eq_mfderiv hΦ hf, ha] at h0
  have hw : mfderiv 𝓘(ℝ, F) I f x a = 0 :=
    inner_self_eq_zero.1 (h0.symm.trans (inner_zero_left _))
  exact hw.trans (map_zero _).symm

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 1 M]

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The identity `μHE[m] (Φ '' u) = vol_g u` on a measurable subset `u` of a chart source. -/
private theorem euclideanHausdorffMeasure_image_eq_riemannianVolume_of_subset_chart {Φ : M → V}
    {α : M} {u : Set M} (hu : MeasurableSet u) (huα : u ⊆ (chartAt H α).source)
    (hinj : InjOn Φ u)
    (hinner : ∀ x ∈ u, ∀ v w : TangentSpace I x,
      ⟪mfderiv I 𝓘(ℝ, V) Φ x v, mfderiv I 𝓘(ℝ, V) Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    μHE[Module.finrank ℝ E] (Φ '' u) = riemannianVolume I M u := by
  -- Parametrize `u` by `f = e⁻¹ ∘ L` on `s = L⁻¹ (e '' u)`, where `e` is the chart at `α` and `L`
  -- is a linear isomorphism from a Euclidean space, so that the area formula applies to `Φ ∘ f`.
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let e := extChartAt I α
  let f : F → M := e.symm ∘ L
  let s : Set F := L ⁻¹' (e '' u)
  have hue : u ⊆ e.source := by rwa [extChartAt_source]
  have hs : MeasurableSet s := by
    let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    exact (hu.image_extChartAt α hue).preimage L.continuous.measurable
  have hsT {y : F} (hy : y ∈ s) : L y ∈ e.target := by
    obtain ⟨z, hz, hzy⟩ := hy
    exact hzy ▸ e.map_source (hue hz)
  have hfs : f '' s = u := by
    rw [image_comp, image_preimage_eq _ L.surjective]
    exact e.symm_image_image_of_subset_source hue
  have hfu : MapsTo f s u := fun y hy ↦ hfs ▸ mem_image_of_mem f hy
  have hinjf : InjOn f s := fun y hy y' hy' h ↦
    L.injective (e.symm.injOn (by simpa using hsT hy) (by simpa using hsT hy') h)
  -- `f` has invertible differential on `s`, as the inverse chart composed with `L`.
  have hfD {y : F} (hy : y ∈ s) : (mfderiv 𝓘(ℝ, F) I f y).IsInvertible := by
    refine isInvertible_mfderiv_comp (isInvertible_mfderiv_extChartAt_symm (hsT hy)) ?_
    rw [L.hasFDerivAt.hasMFDerivAt.mfderiv]
    exact ⟨L, rfl⟩
  have hf {y : F} (hy : y ∈ s) := mdifferentiableAt_of_isInvertible_mfderiv (hfD hy)
  have hΦ {y : F} (hy : y ∈ s) : MDifferentiableAt I 𝓘(ℝ, V) Φ (f y) :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner (f y) (hfu hy) v v
  -- Compare the change of variables formula for `f` with the area formula for `Φ ∘ f`.
  let b := EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ
  have hvol := b.toBasis.setLIntegral_riemannianVolume_image_of_injOn (I := I)
    (by simp) hs hinjf (fun y hy ↦ hf hy) (fun _ ↦ 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one, b.addHaar_eq_volume, hfs] at hvol
  have harea := lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hs
    (fun y hy ↦ ((hΦ hy).comp y (hf hy)).differentiableAt)
    (fun y hy ↦ injective_fderiv_comp_of_inner_mfderiv (hf hy) (hfD hy).injective
      (hinner (f y) (hfu hy)))
    (hinj.comp hinjf hfu)
  rw [finrank_euclideanSpace_fin, image_comp, hfs] at harea
  rw [hvol, ← harea]
  refine setLIntegral_congr_fun hs fun y hy ↦ ?_
  rw [riemannianJacobian_eq_normDet_fderiv_comp b (hf hy) (hinner (f y) (hfu hy))]

/-- **Riemannian volume as Hausdorff measure.** Let `M` be a Lindelöf (equivalently, second
countable) manifold without boundary, modelled on a space of dimension `m`, with a continuous
Riemannian metric, and let `V` be a finite-dimensional inner product space. If `Φ : M → V` is
injective on a measurable set `s` and its tangent maps at points of `s` preserve the inner
products, then the normalized `m`-dimensional Hausdorff measure of `Φ '' s` is the Riemannian
volume of `s`. -/
theorem euclideanHausdorffMeasure_image_eq_riemannianVolume_of_inner_mfderiv {Φ : M → V}
    {s : Set M} (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I 𝓘(ℝ, V) Φ x v, mfderiv I 𝓘(ℝ, V) Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    μHE[Module.finrank ℝ E] (Φ '' s) = riemannianVolume I M s := by
  -- The model is a Polish space, and a Lindelöf manifold modelled on a finite-dimensional space
  -- is second countable, hence hereditarily Lindelöf.
  have : PolishSpace H := I.isClosedEmbedding.polishSpace
  have := ChartedSpace.secondCountable_of_lindelof H M
  have hΦ (x : M) (hx : x ∈ s) : MDifferentiableAt I 𝓘(ℝ, V) Φ x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  -- The restriction of `Φ` to `s` is a measurable embedding, by the Lusin–Souslin theorem, and
  -- the two measures agree on the part of `s` in each chart source.
  refine measure_image_eq_of_locally_eq hs (ContinuousOn.measurableEmbedding_chartedSpace H V
    (fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt) hs hinj)
    (fun x _ ↦ chart_source_mem_nhds H x) fun x _ u hu hus hux ↦ ?_
  exact euclideanHausdorffMeasure_image_eq_riemannianVolume_of_subset_chart hu hux
    (hinj.mono hus) fun y hy ↦ hinner y (hus hy)

/-- **Riemannian volume as Hausdorff measure.** If `Φ : M → V` is injective and its tangent maps
preserve the inner products, then it carries the Riemannian volume of `M` to the normalized
`m`-dimensional Hausdorff measure on its range, where `m` is the dimension of `M`. -/
theorem map_riemannianVolume_eq_restrict_euclideanHausdorffMeasure_of_inner_mfderiv {Φ : M → V}
    (hinj : Function.Injective Φ)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I 𝓘(ℝ, V) Φ x v, mfderiv I 𝓘(ℝ, V) Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    (riemannianVolume I M).map Φ = (μHE[Module.finrank ℝ E]).restrict (range Φ) := by
  have hΦ : Continuous Φ := continuous_iff_continuousAt.2 fun x ↦
    (mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x v v).continuousAt
  ext t ht
  rw [Measure.map_apply hΦ.measurable ht, Measure.restrict_apply ht,
    ← euclideanHausdorffMeasure_image_eq_riemannianVolume_of_inner_mfderiv
      (ht.preimage hΦ.measurable) hinj.injOn fun x _ ↦ hinner x, image_preimage_eq_inter_range]

end TauCeti
