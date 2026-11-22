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
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.Polish

/-!
# Riemannian volume of an isometrically immersed manifold

Let `M` be a manifold without boundary, modelled on a real vector space of dimension `m`, with a
continuous Riemannian metric, and let `Φ : M → V` be a map into a real inner product space whose
tangent maps preserve the inner products, `⟪dΦ_x v, dΦ_x w⟫ = g_x(v, w)`. This is the situation of
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
* `TauCeti.euclideanHausdorffMeasure_image_of_inner_mfderiv`: `μHE[m] (Φ '' s) = vol_g s` for a
  measurable set `s` on which `Φ` is injective.
* `TauCeti.map_riemannianVolume_of_inner_mfderiv`: for an injective `Φ`, the pushforward of the
  Riemannian volume is `μHE[m]` restricted to the range of `Φ`.

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

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The derivative of `Φ ∘ f` from a vector space into a vector space, through a manifold, is the
composite of the manifold derivatives. -/
private theorem fderiv_comp_apply_eq_mfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : M → V} {f : F → M} {x : F} (hΦ : MDifferentiableAt I 𝓘(ℝ, V) Φ (f x))
    (hf : MDifferentiableAt 𝓘(ℝ, F) I f x) (a : F) :
    fderiv ℝ (Φ ∘ f) x a = mfderiv I 𝓘(ℝ, V) Φ (f x) (mfderiv 𝓘(ℝ, F) I f x a) := by
  have h := mfderiv_comp_apply x hΦ hf a
  -- `mfderiv_eq_fderiv` reads the tangent spaces of `F` and `V` as the spaces themselves through
  -- `NormedSpace.fromTangentSpace`, which is the identity.
  rw [mfderiv_eq_fderiv] at h
  exact h

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

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E] in
/-- On a manifold without boundary, the inverse of a chart, precomposed with a linear isomorphism
`L`, is differentiable with injective differential at every point mapped into the chart target. -/
private theorem mdifferentiableAt_and_injective_mfderiv_extChartAt_symm_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (α : M) (L : F ≃L[ℝ] E) {y : F}
    (hy : L y ∈ (extChartAt I α).target) :
    MDifferentiableAt 𝓘(ℝ, F) I ((extChartAt I α).symm ∘ L) y ∧
      Function.Injective (mfderiv 𝓘(ℝ, F) I ((extChartAt I α).symm ∘ L) y) := by
  have hsymm := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hy
  rw [I.range_eq_univ, mdifferentiableWithinAt_univ] at hsymm
  have hmf := hsymm.hasMFDerivAt.comp y L.hasFDerivAt.hasMFDerivAt
  have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := α) hy
  rw [I.range_eq_univ, mfderivWithin_univ] at hinv
  refine ⟨hmf.mdifferentiableAt, ?_⟩
  rw [hmf.mfderiv]
  exact hinv.injective.comp L.injective

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The identity `μHE[m] (Φ '' u) = vol_g u` on a measurable subset `u` of a chart source. -/
private theorem euclideanHausdorffMeasure_image_of_inner_mfderiv_of_subset_chart {Φ : M → V}
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
  have hf {y : F} (hy : y ∈ s) :=
    mdifferentiableAt_and_injective_mfderiv_extChartAt_symm_comp α L (hsT hy)
  have hΦ {y : F} (hy : y ∈ s) : MDifferentiableAt I 𝓘(ℝ, V) Φ (f y) :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner (f y) (hfu hy) v v
  -- Compare the change of variables formula for `f` with the area formula for `Φ ∘ f`.
  let b := EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ
  have hvol := b.toBasis.setLIntegral_riemannianVolume_image_of_injOn (I := I)
    (by simp) hs hinjf (fun y hy ↦ (hf hy).1) (fun _ ↦ 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one, b.addHaar_eq_volume, hfs] at hvol
  have harea := lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hs
    (fun y hy ↦ ((hΦ hy).comp y (hf hy).1).differentiableAt)
    (fun y hy ↦ injective_fderiv_comp_of_inner_mfderiv (hf hy).1 (hf hy).2
      (hinner (f y) (hfu hy)))
    (hinj.comp hinjf hfu)
  rw [finrank_euclideanSpace_fin, image_comp, hfs] at harea
  rw [hvol, ← harea]
  refine setLIntegral_congr_fun hs fun y hy ↦ ?_
  rw [riemannianJacobian_eq_normDet_fderiv_comp b (hf hy).1 (hinner (f y) (hfu hy))]

/-- **Riemannian volume as Hausdorff measure.** Let `M` be a manifold without boundary, modelled on
a space of dimension `m`, with a continuous Riemannian metric. If `Φ : M → V` is injective on a
measurable set `s` and its tangent maps at points of `s` preserve the inner products, then the
normalized `m`-dimensional Hausdorff measure of `Φ '' s` is the Riemannian volume of `s`. -/
theorem euclideanHausdorffMeasure_image_of_inner_mfderiv {Φ : M → V} {s : Set M}
    (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I 𝓘(ℝ, V) Φ x v, mfderiv I 𝓘(ℝ, V) Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    μHE[Module.finrank ℝ E] (Φ '' s) = riemannianVolume I M s := by
  -- The model is a Polish space, and a Lindelöf manifold modelled on a finite-dimensional space
  -- is second countable, hence hereditarily Lindelöf.
  have : PolishSpace H := I.isClosedEmbedding.polishSpace
  have := ChartedSpace.secondCountable_of_lindelof H M
  have hΦ (x : M) (hx : x ∈ s) : MDifferentiableAt I 𝓘(ℝ, V) Φ x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  -- Compare the measures `t ↦ μHE[m] (Φ '' t)` and `t ↦ vol t` on the subtype `s`. They agree on
  -- the part of `s` in each chart source, and countably many chart sources cover `s`.
  obtain ⟨T, hTc, -, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_nhds_subcover
    (fun x ↦ (chartAt H x).source) fun x _ ↦ chart_source_mem_nhds H x
  have hι : MeasurableEmbedding (Subtype.val : s → M) := .subtypeVal hs
  have he : MeasurableEmbedding (s.domRestrict Φ) :=
    ContinuousOn.measurableEmbedding_chartedSpace (H := H) (H' := V)
      (fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt) hs hinj
  have hf_image (t : Set s) : s.domRestrict Φ '' t = Φ '' (Subtype.val '' t) := by
    rw [Set.domRestrict_eq, image_comp]
  suffices h : (μHE[Module.finrank ℝ E]).comap (s.domRestrict Φ) =
      (riemannianVolume I M).comap Subtype.val by
    have h' := congr($h univ)
    rwa [he.comap_apply, hι.comap_apply, image_univ, image_univ, Set.range_domRestrict,
      Subtype.range_coe] at h'
  refine Measure.ext_of_biUnion_eq_univ
    (s := fun x ↦ (Subtype.val : s → M) ⁻¹' (chartAt H x).source) hTc
    (by rw [← preimage_iUnion₂]; exact eq_univ_of_forall fun y ↦ hcover y.property)
    fun x _ ↦ ?_
  ext t ht
  have htV : MeasurableSet (t ∩ Subtype.val ⁻¹' (chartAt H x).source) :=
    ht.inter ((chartAt H x).open_source.measurableSet.preimage measurable_subtypeVal)
  set u := Subtype.val '' (t ∩ Subtype.val ⁻¹' (chartAt H x).source)
  have hus : u ⊆ s := Subtype.coe_image_subset s _
  have hux : u ⊆ (chartAt H x).source := by rintro _ ⟨y, hy, rfl⟩; exact hy.2
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht, he.comap_apply, hι.comap_apply,
    hf_image]
  exact euclideanHausdorffMeasure_image_of_inner_mfderiv_of_subset_chart
    (hι.measurableSet_image' htV) hux (hinj.mono hus) fun y hy ↦ hinner y (hus hy)

/-- **Riemannian volume as Hausdorff measure.** If `Φ : M → V` is injective and its tangent maps
preserve the inner products, then it carries the Riemannian volume of `M` to the normalized
`m`-dimensional Hausdorff measure on its range, where `m` is the dimension of `M`. -/
theorem map_riemannianVolume_of_inner_mfderiv {Φ : M → V} (hinj : Function.Injective Φ)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I 𝓘(ℝ, V) Φ x v, mfderiv I 𝓘(ℝ, V) Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    (riemannianVolume I M).map Φ = (μHE[Module.finrank ℝ E]).restrict (range Φ) := by
  have hΦ : Continuous Φ := continuous_iff_continuousAt.2 fun x ↦
    (mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x v v).continuousAt
  ext t ht
  rw [Measure.map_apply hΦ.measurable ht, Measure.restrict_apply ht,
    ← euclideanHausdorffMeasure_image_of_inner_mfderiv (ht.preimage hΦ.measurable)
      hinj.injOn fun x _ ↦ hinner x, image_preimage_eq_inter_range]

end TauCeti
