/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.Normed.Group.BallSphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import TauCeti.MeasureTheory.Function.AreaFormula.Integral
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity

/-!
# The Riemannian volume of the round sphere

Let `E` be a real inner product space of dimension `n + 1`, and let `Sⁿ` be its unit sphere with
the round metric (`TauCeti.sphereRoundMetric`). This file proves two linked descriptions of its
Riemannian volume measure `TauCeti.riemannianVolume`:

* **Stereographic coordinates.** Read in the inverse of Mathlib's stereographic chart
  `stereographic' n v` from a unit vector `v`, the round metric is `(4 / (‖y‖² + 4))²` times the
  Euclidean metric of `ℝⁿ` (`TauCeti.inner_mfderiv_stereographic'_symm`). Its Riemannian Jacobian
  at `y` is therefore `(4 / (‖y‖² + 4)) ^ n`, and pushing forward Lebesgue measure weighted by that
  density gives the Riemannian volume on `{v}ᶜ` — hence on the whole sphere whenever `n > 0`, since
  singletons have volume zero in positive dimension.
* **Normalized Hausdorff measure.** Composed with the inclusion `Sⁿ → E`, the inverse stereographic
  chart has ambient norm determinant `(4 / (‖y‖² + 4)) ^ n`, so the injective area formula
  identifies the Riemannian volume on `{v}ᶜ` with normalized `n`-dimensional Hausdorff measure
  `μHE[n]`. Covering `Sⁿ` by `{v}ᶜ` and `{-v}ᶜ` identifies the Riemannian volume globally with the
  pullback of `μHE[n]` (and with Mathlib's cone surface measure `Measure.toSphere volume`), in
  every dimension `n ≥ 0` — unlike the ambient `(n + 1)`-dimensional Lebesgue measure of `Sⁿ ⊆ E`,
  which vanishes by `MeasureTheory.Measure.addHaar_sphere`.

Consequently, the total Riemannian volume of the unit round `n`-sphere is
`|Sⁿ| = TauCeti.roundSphereVolume n = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`, and the round
`n`-sphere of radius `r > 0` (`TauCeti.sphereRoundMetricOfRadius`) has total volume `r ^ n |Sⁿ|`.

## Main results

* `TauCeti.riemannianJacobian_stereographic'_symm` and
  `TauCeti.normDet_fderiv_coe_comp_stereographic'_symm`: the Riemannian and ambient Jacobians
  `(4 / (‖y‖² + 4)) ^ n` of `(stereographic' n v).symm`.
* `TauCeti.map_stereographic'_symm_withDensity_eq_restrict_riemannianVolume` and
  `TauCeti.map_stereographic'_symm_withDensity_eq_riemannianVolume`: stereographic pushforward of
  `(4 / (‖y‖² + 4)) ^ n dy` onto `Sⁿ \ {v}`, and onto `Sⁿ` for `n > 0`.
* `TauCeti.lintegral_riemannianVolume_sphere_eq_stereographic'`,
  `TauCeti.integrable_riemannianVolume_sphere_iff_stereographic'`, and
  `TauCeti.integral_riemannianVolume_sphere_eq_stereographic'`: integration on `Sⁿ` in
  stereographic coordinates.
* `TauCeti.riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure`,
  `TauCeti.map_subtypeVal_riemannianVolume_sphere`, and
  `TauCeti.riemannianVolume_sphere_eq_toSphere`: the Riemannian volume of `Sⁿ` is normalized
  `n`-dimensional Hausdorff measure, and coincides with `Measure.toSphere volume`.
* `TauCeti.riemannianVolume_sphere_univ`, `TauCeti.riemannianTotalVolume_sphere`, and
  `TauCeti.riemannianTotalVolume_sphereRoundMetricOfRadius`: the total volumes `|Sⁿ|` and
  `r ^ n |Sⁿ|`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (Riemannian densities) and Chapter 3 (stereographic coordinates on the round sphere).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
-/

public section

open Bundle Function MeasureTheory Metric Module Set
open scoped ContDiff ENNReal InnerProductSpace Manifold

noncomputable section

namespace TauCeti

section Jacobian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **Riemannian Jacobian of inverse stereographic projection.** Relative to the standard
orthonormal basis of `ℝⁿ`, the Riemannian Jacobian of `(stereographic' n v).symm` at `y` for the
round metric is `(4 / (‖y‖² + 4)) ^ n`. -/
theorem riemannianJacobian_stereographic'_symm (v : sphere (0 : E) 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    riemannianJacobian (I := 𝓡 n) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (stereographic' n v).symm y =
      (4 / (‖y‖ ^ 2 + 4)) ^ n := by
  rw [riemannianJacobian_eq_normDet (EuclideanSpace.basisFun (Fin n) ℝ)]
  let J : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      TangentSpace (𝓡 n) ((stereographic' n v).symm y) :=
    (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y).toLinearMap
  change J.normDet = _
  rw [J.normDet_eq_pow_finrank_of_norm_eq (c := 4 / (‖y‖ ^ 2 + 4)) fun u ↦ ?_,
    finrank_euclideanSpace_fin]
  have hinner := inner_mfderiv_stereographic'_symm v y u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← mul_pow] at hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hinner

/-- **Ambient Jacobian of inverse stereographic projection.** Composed with the inclusion of the
unit sphere into `E`, `(stereographic' n v).symm` has norm determinant `(4 / (‖y‖² + 4)) ^ n` at
`y`. -/
theorem normDet_fderiv_coe_comp_stereographic'_symm (v : sphere (0 : E) 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    LinearMap.normDet
        (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y).toLinearMap =
      (4 / (‖y‖ ^ 2 + 4)) ^ n := by
  have hσ : MDifferentiableAt (𝓡 n) (𝓡 n) (stereographic' n v).symm y :=
    mdifferentiableAt_atlas_symm (e := stereographic' n v) (Exists.intro v rfl) (by simp)
  let x := (stereographic' n v).symm y
  let ιL : TangentSpace (𝓡 n) x →ₗᵢ[ℝ] E :=
    (ℝ ∙ (x : E))ᗮ.subtypeₗᵢ.comp (sphereTangentEquiv x).toLinearIsometry
  let J : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y).toLinearMap
  have hcomp :
      (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y).toLinearMap =
        ιL.toLinearMap ∘ₗ J := by
    refine LinearMap.ext fun (c : TangentSpace (𝓡 n) y) ↦ ?_
    have h1 := mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv x
      (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y c)
    rw [← mvfderiv_comp_apply y ((contMDiff_coe_sphere (m := 1) _).mdifferentiableAt one_ne_zero)
      hσ, mvfderiv_eq_fderiv] at h1
    exact h1
  rw [hcomp, LinearMap.normDet_comp_of_finrank_eq J ιL.toLinearMap rfl,
    ιL.normDet_eq_one, one_mul]
  exact (riemannianJacobian_eq_normDet (EuclideanSpace.basisFun (Fin n) ℝ)
    (stereographic' n v).symm y).symm.trans (riemannianJacobian_stereographic'_symm v y)

end Jacobian

section Stereographic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]
  [LindelofSpace (sphere (0 : E) 1)]
  [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)]

/-- **Stereographic pushforward onto the punctured sphere.** The inverse stereographic chart from
`v` pushes Lebesgue measure on `ℝⁿ` weighted by `(4 / (‖y‖² + 4)) ^ n` forward to the Riemannian
volume of the unit sphere restricted to `{v}ᶜ`. -/
theorem map_stereographic'_symm_withDensity_eq_restrict_riemannianVolume
    (v : sphere (0 : E) 1) :
    Measure.map (stereographic' n v).symm
        (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) ↦
          ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n)) =
      (riemannianVolume (𝓡 n) (sphere (0 : E) 1)).restrict {v}ᶜ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1) 1 :=
    ((stereographic' n v).toPartialDiffeomorphOfMemMaximalAtlas
      (stereographic'_mem_maximalAtlas (k := 1) v)).symm
  have hΦ : (Φ : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1) = (stereographic' n v).symm := by
    funext y
    exact (stereographic' n v).toPartialDiffeomorphOfMemMaximalAtlas_symm_apply
      (stereographic'_mem_maximalAtlas (k := 1) v) y
  have hsrc : Φ.source = univ := by
    simp [Φ]
  have htgt : Φ.target = {v}ᶜ := by
    simp [Φ]
  have hmap := Φ.map_withDensity_riemannianJacobian one_ne_zero b.toBasis
  rwa [hsrc, Measure.restrict_univ, b.addHaar_eq_volume, htgt, hΦ,
    funext (riemannianJacobian_stereographic'_symm v)] at hmap

/-- **Stereographic pushforward of the round-sphere volume.** In positive dimension `n > 0`, the
centre `v` of projection has Riemannian volume zero, so `(stereographic' n v).symm` pushes
Lebesgue measure weighted by `(4 / (‖y‖² + 4)) ^ n` forward to the full Riemannian volume of the
unit sphere. -/
theorem map_stereographic'_symm_withDensity_eq_riemannianVolume (hn : 0 < n)
    (v : sphere (0 : E) 1) :
    Measure.map (stereographic' n v).symm
        (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) ↦
          ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n)) =
      riemannianVolume (𝓡 n) (sphere (0 : E) 1) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  rw [map_stereographic'_symm_withDensity_eq_restrict_riemannianVolume v,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (by simp))]

omit [LindelofSpace (sphere (0 : E) 1)] in
private theorem measurableEmbedding_stereographic'_symm (v : sphere (0 : E) 1) :
    MeasurableEmbedding (stereographic' n v).symm :=
  ((stereographic' n v).symm.isOpenEmbedding (by simp)).measurableEmbedding

/-- **Lebesgue integration on the round sphere in stereographic coordinates.** For `n > 0`, the
lower Lebesgue integral of any nonnegative function `f` against the Riemannian volume of `Sⁿ` is
its stereographic integral weighted by `(4 / (‖y‖² + 4)) ^ n`. No measurability of `f` is
required. -/
theorem lintegral_riemannianVolume_sphere_eq_stereographic' (hn : 0 < n)
    (v : sphere (0 : E) 1) (f : sphere (0 : E) 1 → ℝ≥0∞) :
    ∫⁻ p, f p ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n) * f ((stereographic' n v).symm y) := by
  rw [← map_stereographic'_symm_withDensity_eq_riemannianVolume hn v,
    (measurableEmbedding_stereographic'_symm v).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin n) ↦
        ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n))
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rfl

/-- **Integrability on the round sphere in stereographic coordinates.** In every dimension `n ≥ 0`,
a normed-space-valued function `f` on `Sⁿ` is integrable for the Riemannian volume if and only if
`y ↦ (4 / (‖y‖² + 4)) ^ n • f (σ⁻¹ y)` is integrable on `ℝⁿ`. For `n = 0` both spaces are finite
and both sides hold unconditionally. -/
theorem integrable_riemannianVolume_sphere_iff_stereographic'
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : sphere (0 : E) 1) (f : sphere (0 : E) 1 → F) :
    Integrable f (riemannianVolume (𝓡 n) (sphere (0 : E) 1)) ↔
      Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
        ((4 / (‖y‖ ^ 2 + 4)) ^ n) • f ((stereographic' n v).symm y)) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Finite (sphere (0 : E) 1) := finite_sphere_of_finrank_eq_one Fact.out (0 : E) 1
    exact ⟨fun _ ↦ Integrable.of_finite, fun _ ↦ Integrable.of_finite⟩
  · rw [← map_stereographic'_symm_withDensity_eq_riemannianVolume hn v,
      (measurableEmbedding_stereographic'_symm v).integrable_map_iff,
      TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff
        (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin n) ↦
          (4 / (‖y‖ ^ 2 + 4)) ^ n).aemeasurable
        (ae_of_all _ fun _ ↦ by positivity)]
    rfl

/-- **Bochner integration on the round sphere in stereographic coordinates.** For `n > 0`, the
integral of any function `f` against the Riemannian volume of `Sⁿ` is its stereographic integral
weighted by `(4 / (‖y‖² + 4)) ^ n`. Neither integrability of `f` nor completeness of the target
space is required. -/
theorem integral_riemannianVolume_sphere_eq_stereographic' (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : sphere (0 : E) 1) (f : sphere (0 : E) 1 → F) :
    ∫ p, f p ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫ y : EuclideanSpace ℝ (Fin n),
        ((4 / (‖y‖ ^ 2 + 4)) ^ n) • f ((stereographic' n v).symm y) := by
  rw [← map_stereographic'_symm_withDensity_eq_riemannianVolume hn v,
    (measurableEmbedding_stereographic'_symm v).integral_map,
    TauCeti.MeasureTheory.integral_withDensity_ofReal
      (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin n) ↦
        (4 / (‖y‖ ^ 2 + 4)) ^ n).aemeasurable
      (ae_of_all _ fun _ ↦ by positivity)]

end Stereographic

section Hausdorff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [MeasurableSpace E] [BorelSpace E]

/-- On `{v}ᶜ`, the Riemannian volume of the unit sphere agrees with the pullback of normalized
`n`-dimensional Hausdorff measure. -/
private theorem restrict_riemannianVolume_sphere_eq_restrict_comap_euclideanHausdorffMeasure
    [LindelofSpace (sphere (0 : E) 1)] (v : sphere (0 : E) 1) :
    (riemannianVolume (𝓡 n) (sphere (0 : E) 1)).restrict {v}ᶜ =
      ((μHE[n] : Measure E).comap (↑)).restrict {v}ᶜ := by
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos ((Fact.out : finrank ℝ E = n + 1) ▸ Nat.succ_pos n)
  let ι : sphere (0 : E) 1 → E := (↑)
  let σ : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1 := (stereographic' n v).symm
  have hι : MeasurableEmbedding ι :=
    MeasurableEmbedding.subtypeVal isClosed_sphere.measurableSet
  have harea := restrict_map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure
    (U := EuclideanSpace ℝ (Fin n)) (V := E) (f := ι ∘ σ) (s := univ) MeasurableSet.univ
    (fun y _ ↦ (contDiff_coe_comp_stereographic'_symm (k := 1) v).differentiable one_ne_zero y)
    (fun y _ ↦ injective_fderiv_coe_comp_stereographic'_symm v y)
    (Subtype.val_injective.comp
      (isSmoothEmbedding_stereographic'_symm (k := 1) v).isEmbedding.injective).injOn
  have hdom : Measure.map ((univ : Set (EuclideanSpace ℝ (Fin n))).domRestrict (ι ∘ σ))
      (Measure.comap Subtype.val
        (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) ↦
          ENNReal.ofReal (fderiv ℝ (ι ∘ σ) y).toLinearMap.normDet)) =
      Measure.map ι (Measure.map σ (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) ↦
        ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n))) := by
    have hu := MeasurableEmbedding.subtypeVal
      (MeasurableSet.univ : MeasurableSet (univ : Set (EuclideanSpace ℝ (Fin n))))
    have hfun : (univ : Set (EuclideanSpace ℝ (Fin n))).domRestrict (ι ∘ σ) =
        (ι ∘ σ) ∘ Subtype.val := rfl
    rw [hfun, ← Measure.map_map ((contDiff_coe_comp_stereographic'_symm (k := 1)
        v).continuous.measurable) hu.measurable, hu.map_comap, Subtype.range_coe,
      Measure.restrict_univ, Measure.map_map hι.measurable
        ((stereographic' n v).symm.isOpenEmbedding (by simp)).continuous.measurable]
    simp only [normDet_fderiv_coe_comp_stereographic'_symm, ι, σ]
  have himg : (ι ∘ σ) '' univ = ι '' ({v}ᶜ : Set (sphere (0 : E) 1)) := by
    rw [image_comp]
    congr 1
    simpa [σ] using (stereographic' n v).symm.image_source_eq_target
  rw [finrank_euclideanSpace_fin, hdom, himg,
    map_stereographic'_symm_withDensity_eq_restrict_riemannianVolume v] at harea
  simpa only [hι.comap_map, ← hι.restrict_comap] using congrArg (Measure.comap ι) harea

/-- **The Riemannian volume of the unit sphere is normalized Hausdorff measure.** In every
dimension `n ≥ 0`, the Riemannian volume of `Sⁿ` for the round metric is the pullback of the
normalized `n`-dimensional Hausdorff measure `μHE[n]` along the inclusion into `E`. -/
theorem riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure
    [LindelofSpace (sphere (0 : E) 1)] :
    riemannianVolume (𝓡 n) (sphere (0 : E) 1) = (μHE[n] : Measure E).comap (↑) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  have := HasUniqueDiv.of_isTorsionFree ℝ E
  obtain ⟨v⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hcov : (⋃ b : Bool, bif b then ({v}ᶜ : Set (sphere (0 : E) 1)) else {-v}ᶜ) = univ := by
    rw [← Set.union_eq_iUnion]
    exact compl_singleton_union_compl_singleton_neg one_ne_zero v
  refine Measure.ext_of_iUnion_eq_univ hcov fun b ↦ ?_
  cases b <;> exact restrict_riemannianVolume_sphere_eq_restrict_comap_euclideanHausdorffMeasure _

/-- Pushing the Riemannian volume of the unit sphere forward along the inclusion `Sⁿ → E` gives
normalized `n`-dimensional Hausdorff measure restricted to the sphere. -/
theorem map_subtypeVal_riemannianVolume_sphere [LindelofSpace (sphere (0 : E) 1)] :
    (riemannianVolume (𝓡 n) (sphere (0 : E) 1)).map (↑) =
      (μHE[n] : Measure E).restrict (sphere 0 1) := by
  rw [riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure,
    (MeasurableEmbedding.subtypeVal isClosed_sphere.measurableSet).map_comap, Subtype.range_coe]

/-- **The Riemannian volume of the unit sphere agrees with `Measure.toSphere volume`.** -/
theorem riemannianVolume_sphere_eq_toSphere [FiniteDimensional ℝ E] :
    riemannianVolume (𝓡 n) (sphere (0 : E) 1) = (volume : Measure E).toSphere := by
  rw [toSphere_volume_eq_comap_euclideanHausdorffMeasure, (Fact.out : finrank ℝ E = n + 1),
    Nat.add_sub_cancel, riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure]

end Hausdorff

section TotalVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The Riemannian volume measure of the unit `n`-sphere assigns `univ` measure
`ENNReal.ofReal (roundSphereVolume n)`. -/
theorem riemannianVolume_sphere_univ
    [LindelofSpace (sphere (0 : E) 1)]
    [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)] :
    riemannianVolume (𝓡 n) (sphere (0 : E) 1) univ = ENNReal.ofReal (roundSphereVolume n) := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain rfl : ‹MeasurableSpace (sphere (0 : E) 1)› = Subtype.instMeasurableSpace :=
    BorelSpace.measurable_eq.trans BorelSpace.measurable_eq.symm
  rw [riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure,
    (MeasurableEmbedding.subtypeVal isClosed_sphere.measurableSet).comap_apply, image_univ,
    Subtype.range_coe, euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume Fact.out]

/-- **Total Riemannian volume of the unit round sphere**: `Vol(Sⁿ) = |Sⁿ|`. -/
@[simp]
theorem riemannianTotalVolume_sphere
    [CompactSpace (sphere (0 : E) 1)]
    [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)] :
    riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) = roundSphereVolume n := by
  rw [riemannianTotalVolume_def, Measure.real, riemannianVolume_sphere_univ,
    ENNReal.toReal_ofReal (roundSphereVolume_pos n).le]

/-- **Total Riemannian volume of the round sphere of radius `r > 0`**: `Vol(Sⁿ(r)) = r ^ n |Sⁿ|`. -/
@[simp]
theorem riemannianTotalVolume_sphereRoundMetricOfRadius
    [CompactSpace (sphere (0 : E) 1)] {r : ℝ} (hr : 0 < r) :
    riemannianTotalVolume (𝓡 n)
        (WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr)) =
      r ^ n * roundSphereVolume n := by
  let _ : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
  have : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
  have hrpow : (r ^ 2) ^ ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) / 2) = r ^ n := by
    rw [finrank_euclideanSpace_fin, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le,
      Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero, Real.rpow_natCast]
  have hbase :
      riemannianTotalVolume (𝓡 n)
        (WithMetric ((sphereRoundMetric (E := E) (n := n)).ofLE (le_top : (∞ : ℕ∞ω) ≤ ω))) =
        riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) :=
    (WithMetric.homeomorph _).riemannianTotalVolume_eq fun x v w ↦ by
      rw [WithMetric.coe_homeomorph, WithMetric.inner_def, ContMDiffRiemannianMetric.ofLE_inner,
        sphereRoundMetric_inner, inner_tangentSpace_sphere]
  rw [sphereRoundMetricOfRadius_def, WithMetric.riemannianTotalVolume_rescale, hrpow,
    integral_const, smul_eq_mul, ← riemannianTotalVolume_def, hbase,
    riemannianTotalVolume_sphere, mul_comm]

end TotalVolume

end TauCeti
