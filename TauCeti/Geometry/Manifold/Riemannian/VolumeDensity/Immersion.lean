/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.MeasureTheory.Function.AreaFormula.Basic
public import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Riemannian volume of isometric immersions, embeddings, and flat spaces

Let `M` be a `C¹` Riemannian manifold without boundary modelled on a finite-dimensional real inner
product space `F`, and let `ι : M → E` be a differentiable map into a finite-dimensional real inner
product space `E` whose differential preserves inner products. Reading `ι` in a preferred chart at
`α` gives a map `ψ = ι ∘ (extChartAt I α).symm : F → E`. Because the chart volume density
`TauCeti.chartVolumeDensity` is computed from `Module.finBasis ℝ F` while coordinate integration
uses `(Module.finBasis ℝ F).addHaar`, the basis-normalization factor `√det(Gram b)` cancels against
`Module.Basis.volume_eq_smul_addHaar`, leaving Lebesgue measure on `F` weighted by the Euclidean
Jacobian `(fderiv ℝ ψ y).normDet`.

Combining this coordinate formula with the injective area formula
`MeasureTheory.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image` identifies the
Riemannian volume of an injective chart piece with the `dim F`-dimensional normalized Euclidean
Hausdorff measure `μHE[finrank ℝ F]` of its image. Globally, for any isometric measurable embedding
`ι : M → E` of a Lindelöf manifold without boundary, `riemannianVolume I M` is the pullback
`(μHE[finrank ℝ F]).comap ι`. Taking `ι = id` on `E` itself shows that the Riemannian volume of a
finite-dimensional real inner product space is its standard Lebesgue `volume`.

## Main results

* `TauCeti.chartVolumeDensity_of_inner_mfderiv_eq`: the chart volume density of an isometric map in
  terms of `(fderiv ℝ (ι ∘ (extChartAt I α).symm) _).normDet`.
* `TauCeti.setLIntegral_riemannianVolume_eq_lintegral_normDet_of_subset` and
  `TauCeti.setIntegral_riemannianVolume_eq_integral_normDet_of_subset`: coordinate integration
  against Lebesgue `volume` on the model space weighted by `normDet`.
* `TauCeti.riemannianVolume_apply_eq_euclideanHausdorffMeasure_image_of_subset`: the Riemannian
  volume of an injective chart piece is the Euclidean Hausdorff measure of its image.
* `TauCeti.riemannianVolume_eq_comap_euclideanHausdorffMeasure` and
  `TauCeti.map_riemannianVolume_eq_restrict_euclideanHausdorffMeasure`: global identification of
  `riemannianVolume` for an isometric measurable embedding.
* `TauCeti.riemannianVolume_model_space`: on a finite-dimensional real inner product space `E`,
  `riemannianVolume 𝓘(ℝ, E) E = volume`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §3.3.
-/

public section

open Bundle Function MeasureTheory Measure Module Riemannian.Tensor Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

section Immersion

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **Chart volume density of an isometric map.** At a chart point `x` where `ι : M → E` is
differentiable and its differential preserves inner products, the chart volume density is the basis
normalization factor `√det(Gram (Module.finBasis ℝ F))` times the Euclidean Jacobian `normDet` of
`ι` read in the extended chart. -/
theorem chartVolumeDensity_of_inner_mfderiv_eq (α : M) {x : M} (hx : x ∈ (chartAt H α).source)
    {ι : M → E} (hι : MDifferentiableAt I 𝓘(ℝ, E) ι x)
    (hinner : ∀ v w : TangentSpace I x,
      inner ℝ (mfderiv I 𝓘(ℝ, E) ι x v) (mfderiv I 𝓘(ℝ, E) ι x w) = inner ℝ v w) :
    chartVolumeDensity (I := I) α x =
      √(Matrix.gram ℝ (Module.finBasis ℝ F)).det *
        (fderiv ℝ (ι ∘ (extChartAt I α).symm) (extChartAt I α x)).normDet := by
  set b := Module.finBasis ℝ F
  set A := (fderiv ℝ (ι ∘ (extChartAt I α).symm) (extChartAt I α x)).toLinearMap
  let u := stdOrthonormalBasis ℝ F
  let T : F →ₗ[ℝ] F := u.toBasis.constr ℝ b
  have hb : (fun i ↦ T (u i)) = b := funext fun i ↦ u.toBasis.constr_basis ℝ b i
  have hG : chartGramMatrix (I := I) α x = Matrix.gram ℝ (fun i ↦ (A ∘ₗ T) (u i)) := by
    ext i j
    rw [chartGramMatrix_apply, ← hinner, TauCeti.Manifold.inner_tangentSpace_vectorSpace,
      NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_apply,
      ← mvfderiv_apply_eq_mfderiv_apply, ← mvfderiv_apply_eq_mfderiv_apply,
      mvfderiv_chartLocalFrame α hx hι i, mvfderiv_chartLocalFrame α hx hι j,
      Matrix.gram_apply, LinearMap.comp_apply, LinearMap.comp_apply, congrFun hb i, congrFun hb j,
      ContinuousLinearMap.coe_coe]
  have hdet_b : (Matrix.gram ℝ b).det = T.normDet ^ 2 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, hb] using (T.normDet_sq_eq_det_gram u).symm
  have hdet_AT : (Matrix.gram ℝ (fun i ↦ (A ∘ₗ T) (u i))).det = (A ∘ₗ T).normDet ^ 2 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using ((A ∘ₗ T).normDet_sq_eq_det_gram u).symm
  rw [chartVolumeDensity_def, hG, hdet_AT, hdet_b, Real.sqrt_sq (LinearMap.normDet_nonneg _),
    Real.sqrt_sq T.normDet_nonneg, LinearMap.normDet_comp_of_finrank_eq T A rfl, mul_comm]

section Measure

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace I x)]

/-- **Coordinate Lebesgue integral for an isometric map.** Over a measurable subset `s` of a chart
source where `ι : M → E` is differentiable and preserves inner products, integrating against
`riemannianVolume I M` is integrating against Lebesgue `volume` on `F` weighted by the Euclidean
Jacobian `(fderiv ℝ (ι ∘ (extChartAt I α).symm) y).normDet`. -/
theorem setLIntegral_riemannianVolume_eq_lintegral_normDet_of_subset
    [MeasurableSpace F] [BorelSpace F] {α : M} {s : Set M}
    (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) {ι : M → E}
    (hι : ∀ x ∈ s, MDifferentiableAt I 𝓘(ℝ, E) ι x)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      inner ℝ (mfderiv I 𝓘(ℝ, E) ι x v) (mfderiv I 𝓘(ℝ, E) ι x w) = inner ℝ v w)
    (φ : M → ℝ≥0∞) :
    ∫⁻ x in s, φ x ∂riemannianVolume I M =
      ∫⁻ y in extChartAt I α '' s,
        ENNReal.ofReal (fderiv ℝ (ι ∘ (extChartAt I α).symm) y).normDet *
          φ ((extChartAt I α).symm y) ∂volume := by
  borelize F
  let b := Module.finBasis ℝ F
  have himg_meas : MeasurableSet (extChartAt I α '' s) := hs'.image_extChartAt α (by
    simpa only [extChartAt_source] using hs)
  rw [setLIntegral_riemannianVolume_of_subset hs hs' φ, b.volume_eq_smul_addHaar,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun himg_meas fun y hy ↦ ?_
  rcases hy with ⟨x, hx, rfl⟩
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact hs hx
  have hsymm : (extChartAt I α).symm (extChartAt I α x) = x := (extChartAt I α).left_inv hx_src
  rw [hsymm, chartVolumeDensity_of_inner_mfderiv_eq α (hs hx) (hι x hx) (hinner x hx),
    ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]

/-- **Coordinate Bochner integral for an isometric map.** Over a measurable subset `s` of a chart
source where `ι : M → E` is differentiable and preserves inner products, integrating against
`riemannianVolume I M` is integrating against Lebesgue `volume` on `F` weighted by the Euclidean
Jacobian `(fderiv ℝ (ι ∘ (extChartAt I α).symm) y).normDet`. -/
theorem setIntegral_riemannianVolume_eq_integral_normDet_of_subset
    [MeasurableSpace F] [BorelSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : M} {s : Set M} (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) {ι : M → E}
    (hι : ∀ x ∈ s, MDifferentiableAt I 𝓘(ℝ, E) ι x)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      inner ℝ (mfderiv I 𝓘(ℝ, E) ι x v) (mfderiv I 𝓘(ℝ, E) ι x w) = inner ℝ v w)
    (φ : M → G) :
    ∫ x in s, φ x ∂riemannianVolume I M =
      ∫ y in extChartAt I α '' s,
        (fderiv ℝ (ι ∘ (extChartAt I α).symm) y).normDet • φ ((extChartAt I α).symm y) ∂volume := by
  borelize F
  let b := Module.finBasis ℝ F
  have himg_meas : MeasurableSet (extChartAt I α '' s) := hs'.image_extChartAt α (by
    simpa only [extChartAt_source] using hs)
  rw [setIntegral_riemannianVolume_of_subset hs hs' φ, b.volume_eq_smul_addHaar,
    Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ← integral_smul]
  refine setIntegral_congr_fun himg_meas fun y hy ↦ ?_
  rcases hy with ⟨x, hx, rfl⟩
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact hs hx
  have hsymm : (extChartAt I α).symm (extChartAt I α x) = x := (extChartAt I α).left_inv hx_src
  rw [hsymm, chartVolumeDensity_of_inner_mfderiv_eq α (hs hx) (hι x hx) (hinner x hx), mul_smul]

/-- **Riemannian volume of an injective isometric chart piece.** On a measurable subset `s` of a
chart source on which `ι : M → E` is injective, differentiable, and isometric on tangent spaces,
`riemannianVolume I M s` equals the `dim F`-dimensional Euclidean Hausdorff measure of `ι '' s`. -/
theorem riemannianVolume_apply_eq_euclideanHausdorffMeasure_image_of_subset
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {α : M} {s : Set M}
    (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) {ι : M → E}
    (hι : ∀ x ∈ s, MDifferentiableAt I 𝓘(ℝ, E) ι x)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      inner ℝ (mfderiv I 𝓘(ℝ, E) ι x v) (mfderiv I 𝓘(ℝ, E) ι x w) = inner ℝ v w)
    (hinj : InjOn ι s) :
    riemannianVolume I M s = μHE[finrank ℝ F] (ι '' s) := by
  let _ : MeasurableSpace F := extChartAtMeasurableSpaceE
  let _ : BorelSpace F := extChartAtBorelSpaceE
  set e := extChartAt I α
  set ψ := ι ∘ e.symm
  have hs_ext : s ⊆ e.source := by rwa [extChartAt_source]
  have himg_meas : MeasurableSet (e '' s) := hs'.image_extChartAt α hs_ext
  have hd : ∀ y ∈ e '' s, DifferentiableAt ℝ ψ y := by
    rintro _ ⟨x, hx, rfl⟩
    have hsymm : MDifferentiableAt 𝓘(ℝ, F) I e.symm (e x) := by
      have := mdifferentiableWithinAt_extChartAt_symm (I := I) (e.map_source (hs_ext hx))
      rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at this
    have hx' : e.symm (e x) = x := e.left_inv (hs_ext hx)
    exact mdifferentiableAt_iff_differentiableAt.1 ((hx'.symm ▸ hι x hx).comp (e x) hsymm)
  have hdf_inj : ∀ y ∈ e '' s, Injective (fderiv ℝ ψ y) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx_base : x ∈ (trivializationAt F (TangentSpace I) α).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hs hx
    have hρ_pos : 0 < chartVolumeDensity (I := I) α x := chartVolumeDensity_pos α hx_base
    rw [chartVolumeDensity_of_inner_mfderiv_eq α (hs hx) (hι x hx) (hinner x hx)] at hρ_pos
    have hnd : (fderiv ℝ ψ (e x)).normDet ≠ 0 := right_ne_zero_of_mul hρ_pos.ne'
    exact LinearMap.ker_eq_bot.1
      (not_ne_iff.1 ((LinearMap.normDet_eq_zero_iff_ker_ne_bot).not.1 hnd))
  have hψ_inj : InjOn ψ (e '' s) := by
    rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hEq
    have hEq' : ι x₁ = ι x₂ := by
      simpa only [ψ, Function.comp_apply, e.left_inv (hs_ext hx₁), e.left_inv (hs_ext hx₂)]
        using hEq
    rw [hinj hx₁ hx₂ hEq']
  have himage : ψ '' (e '' s) = ι '' s := by
    rw [← image_comp]
    exact image_congr fun x hx ↦ congrArg ι (e.left_inv (hs_ext hx))
  have hvol := setLIntegral_riemannianVolume_eq_lintegral_normDet_of_subset hs hs' hι hinner 1
  simp only [Pi.one_apply, mul_one, setLIntegral_one] at hvol
  rw [hvol, MeasureTheory.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image
    himg_meas hd hdf_inj hψ_inj, himage]

/-- **Riemannian volume of an isometric measurable embedding.** If `ι : M → E` is a differentiable
measurable embedding into a finite-dimensional real inner product space whose differential preserves
inner products everywhere, then `riemannianVolume I M` is the pullback of the `dim F`-dimensional
Euclidean Hausdorff measure along `ι`. -/
theorem riemannianVolume_eq_comap_euclideanHausdorffMeasure
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : M → E}
    (hemb : MeasurableEmbedding ι) (hι : MDifferentiable I 𝓘(ℝ, E) ι)
    (hinner : ∀ x (v w : TangentSpace I x),
      inner ℝ (mfderiv I 𝓘(ℝ, E) ι x v) (mfderiv I 𝓘(ℝ, E) ι x w) = inner ℝ v w) :
    riemannianVolume I M = (μHE[finrank ℝ F] : Measure E).comap ι := by
  symm
  rw [eq_riemannianVolume_iff]
  intro α
  have hopen : MeasurableSet (chartAt H α).source := (chartAt H α).open_source.measurableSet
  ext s hs
  rw [Measure.restrict_apply hs, hemb.comap_apply, ← chartRiemannianVolume_restrict_source α,
    Measure.restrict_apply hs, ← riemannianVolume_apply_of_subset inter_subset_right]
  exact (riemannianVolume_apply_eq_euclideanHausdorffMeasure_image_of_subset inter_subset_right
    (hs.inter hopen) (fun x _ ↦ hι x) (fun x _ ↦ hinner x) hemb.injective.injOn).symm

/-- Pushing `riemannianVolume I M` forward along an isometric measurable embedding `ι : M → E`
yields the restriction of `dim F`-dimensional Euclidean Hausdorff measure to `range ι`. -/
theorem map_riemannianVolume_eq_restrict_euclideanHausdorffMeasure
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : M → E}
    (hemb : MeasurableEmbedding ι) (hι : MDifferentiable I 𝓘(ℝ, E) ι)
    (hinner : ∀ x (v w : TangentSpace I x),
      inner ℝ (mfderiv I 𝓘(ℝ, E) ι x v) (mfderiv I 𝓘(ℝ, E) ι x w) = inner ℝ v w) :
    (riemannianVolume I M).map ι = (μHE[finrank ℝ F] : Measure E).restrict (range ι) := by
  rw [riemannianVolume_eq_comap_euclideanHausdorffMeasure hemb hι hinner, hemb.map_comap]

end Measure

end Immersion

section ModelSpace

/-- On a finite-dimensional real inner product space carrying its standard Riemannian metric, the
Riemannian volume measure coincides with Lebesgue `volume`. -/
@[simp]
theorem riemannianVolume_model_space (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    riemannianVolume 𝓘(ℝ, E) E = volume := by
  rw [riemannianVolume_eq_comap_euclideanHausdorffMeasure (E := E) MeasurableEmbedding.id
    mdifferentiable_id, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  · exact Measure.comap_id volume
  · intro x v w
    rw [mfderiv_id]
    rfl

end ModelSpace

end TauCeti
