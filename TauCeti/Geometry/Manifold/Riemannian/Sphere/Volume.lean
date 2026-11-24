/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Hausdorff
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null

/-!
# The Riemannian volume of the round sphere

The round metric on the unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1`
(`TauCeti.sphereRoundMetric`) is induced by the inclusion of the sphere into `E`. Its Riemannian
volume is therefore the extrinsic surface measure of the sphere: the inclusion carries it to the
normalized `n`-dimensional Hausdorff measure `μHE[n]` of `E` restricted to the sphere. In
particular the round sphere has total volume `|Sⁿ| = TauCeti.roundSphereVolume n`, and the round
`n`-sphere of radius `r > 0` (`TauCeti.sphereRoundMetricOfRadius`) has total volume `r ^ n |Sⁿ|`.

* **Stereographic coordinates.** Read in the inverse of Mathlib's stereographic chart
  `stereographic' n v` from a unit vector `v`, the round metric is `(4 / (‖y‖² + 4))²` times the
  Euclidean metric of `ℝⁿ` (`TauCeti.inner_mfderiv_stereographic'_symm`). Its Riemannian Jacobian
  at `y` is therefore `(4 / (‖y‖² + 4)) ^ n`, and pushing forward Lebesgue measure weighted by that
  density gives the Riemannian volume on `{v}ᶜ` — hence on the whole sphere whenever `n > 0`, since
  singletons have volume zero in positive dimension.
* **Normalized Hausdorff measure and `Measure.toSphere`.** The Riemannian volume of `Sⁿ` is the
  pullback of `μHE[n]` along the inclusion `Sⁿ → E` (and coincides with Mathlib's cone surface
  measure `Measure.toSphere volume`), in every dimension `n ≥ 0` — unlike the ambient
  `(n + 1)`-dimensional Lebesgue measure of `Sⁿ ⊆ E`, which vanishes by
  `MeasureTheory.Measure.addHaar_sphere`.
* **Antipodal invariance.** The instance `TauCeti.isNegInvariant_riemannianVolume_sphere` states
  that the antipodal map preserves native Riemannian volume on the round unit sphere. For mean-zero
  cancellation, also import `TauCeti.MeasureTheory.Integral.OddSymmetric` and apply
  `MeasureTheory.integral_eq_zero_of_odd`; for a pointwise odd function, pass
  `Filter.Eventually.of_forall hodd` as the symmetry hypothesis.

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
* `TauCeti.map_subtypeVal_riemannianVolume_sphere_eq_restrict_euclideanHausdorffMeasure`,
  `TauCeti.riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure`, and
  `TauCeti.riemannianVolume_sphere_eq_toSphere`: the Riemannian volume of `Sⁿ` is normalized
  `n`-dimensional Hausdorff measure, and coincides with `Measure.toSphere volume`.
* `TauCeti.riemannianVolume_sphere_univ`, `TauCeti.riemannianTotalVolume_sphere`, and
  `TauCeti.riemannianTotalVolume_sphereRoundMetricOfRadius`: the total volumes `|Sⁿ|` and
  `r ^ n |Sⁿ|`.
* `TauCeti.isNegInvariant_riemannianVolume_sphere`: antipodal invariance of `riemannianVolume` on
  the unit sphere.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the round metric as an induced metric, and the Riemannian density) and Chapter 3 (stereographic
  coordinates on the round sphere).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
* [`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/1666783/ForTauCeti/Geometry/Manifold/Riemannian/Examples/Immersion/ProjectiveEquator/OddMean.lean)
  (origin of `isNegInvariant_riemannianVolume_sphere`).
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

omit [LindelofSpace (sphere (0 : E) 1)] [MeasurableSpace (sphere (0 : E) 1)]
  [BorelSpace (sphere (0 : E) 1)] in
private def stereographic'SymmPartialDiffeomorph (v : sphere (0 : E) 1) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1) 1 :=
  ((stereographic' n v).toPartialDiffeomorphOfMemMaximalAtlas
    (stereographic'_mem_maximalAtlas (k := 1) v)).symm

omit [LindelofSpace (sphere (0 : E) 1)] [MeasurableSpace (sphere (0 : E) 1)]
  [BorelSpace (sphere (0 : E) 1)] in
private theorem coe_stereographic'SymmPartialDiffeomorph (v : sphere (0 : E) 1) :
    (stereographic'SymmPartialDiffeomorph (n := n) v :
      EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1) = (stereographic' n v).symm :=
  funext ((stereographic' n v).toPartialDiffeomorphOfMemMaximalAtlas_symm_apply
    (stereographic'_mem_maximalAtlas (k := 1) v))

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
  have hmap := (stereographic'SymmPartialDiffeomorph (n := n) v).map_withDensity_riemannianJacobian
    one_ne_zero b.toBasis
  rw [coe_stereographic'SymmPartialDiffeomorph v,
    funext (riemannianJacobian_stereographic'_symm v)] at hmap
  simpa [stereographic'SymmPartialDiffeomorph, b.addHaar_eq_volume] using hmap

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
    restrict_compl_singleton v]

/-- **Lebesgue integration on the round sphere in stereographic coordinates.** For `n > 0`, the
lower Lebesgue integral of any nonnegative function `f` against the Riemannian volume of `Sⁿ` is
its stereographic integral weighted by `(4 / (‖y‖² + 4)) ^ n`. No measurability of `f` is
required. -/
theorem lintegral_riemannianVolume_sphere_eq_stereographic' (hn : 0 < n)
    (v : sphere (0 : E) 1) (f : sphere (0 : E) 1 → ℝ≥0∞) :
    ∫⁻ p, f p ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n) * f ((stereographic' n v).symm y) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h := (stereographic'SymmPartialDiffeomorph (n := n) v).setLIntegral_riemannianVolume_eq
    one_ne_zero b.toBasis f
  rw [coe_stereographic'SymmPartialDiffeomorph v,
    funext (riemannianJacobian_stereographic'_symm v)] at h
  simpa [stereographic'SymmPartialDiffeomorph, restrict_compl_singleton,
    b.addHaar_eq_volume] using h

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
  · have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    have h := (stereographic'SymmPartialDiffeomorph (n := n) v).integrableOn_riemannianVolume_iff
      one_ne_zero b.toBasis f
    rw [coe_stereographic'SymmPartialDiffeomorph v,
      funext (riemannianJacobian_stereographic'_symm v)] at h
    simpa [IntegrableOn, stereographic'SymmPartialDiffeomorph, restrict_compl_singleton,
      b.addHaar_eq_volume] using h

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
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h := (stereographic'SymmPartialDiffeomorph (n := n) v).setIntegral_riemannianVolume_eq
    one_ne_zero b.toBasis f
  rw [coe_stereographic'SymmPartialDiffeomorph v,
    funext (riemannianJacobian_stereographic'_symm v)] at h
  simpa [stereographic'SymmPartialDiffeomorph, restrict_compl_singleton,
    b.addHaar_eq_volume] using h

end Stereographic

section Antipodal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- Native Riemannian volume on the round unit sphere is invariant under negation. -/
instance isNegInvariant_riemannianVolume_sphere :
    letI := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
    (riemannianVolume (𝓡 n) (Metric.sphere (0 : E) 1)).IsNegInvariant := by
  have := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
  let Φ := (LinearIsometryEquiv.neg ℝ (E := E)).unitSphereRiemannianIsometry
    (n := n) (k := n)
  have hΦ : (Φ : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1) = fun x => -x := by
    funext x
    rw [← RiemannianIsometry.coe_toDiffeomorph Φ]
    rw [LinearIsometryEquiv.unitSphereRiemannianIsometry_toDiffeomorph]
    exact LinearIsometryEquiv.unitSphereDiffeomorph_neg_apply x
  exact ⟨by simpa only [Measure.neg_def, hΦ] using Φ.measurePreserving_riemannianVolume.map_eq⟩

end Antipodal

section SurfaceMeasure

open Metric Module Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] [FiniteDimensional ℝ E]

/-- **The Riemannian volume of the round sphere is its surface measure.** The inclusion of the unit
sphere `Sⁿ` into `E` carries the Riemannian volume of the round metric to the normalized
`n`-dimensional Hausdorff measure of `E` restricted to the sphere. -/
theorem map_subtypeVal_riemannianVolume_sphere_eq_restrict_euclideanHausdorffMeasure :
    (riemannianVolume (𝓡 n) (sphere (0 : E) 1)).map ((↑) : sphere (0 : E) 1 → E) =
      (μHE[n]).restrict (sphere (0 : E) 1) := by
  have h := map_riemannianVolume_eq_restrict_euclideanHausdorffMeasure_of_inner_mfderiv
    (I := 𝓡 n) (M := sphere (0 : E) 1) Subtype.val_injective fun x v w ↦ by
      rw [inner_tangentSpace_sphere, mvfderiv_apply_eq_mfderiv_apply,
        mvfderiv_apply_eq_mfderiv_apply]
      -- The two sides use the inner products of `TangentSpace 𝓘(ℝ, E) x` and of `E`, which agree.
      rfl
  rwa [finrank_euclideanSpace_fin, Subtype.range_coe] at h

/-- **The volume of the round sphere.** The unit sphere `Sⁿ` with its round metric has total volume
`|Sⁿ| = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`. -/
@[simp]
theorem riemannianTotalVolume_sphere :
    riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) = roundSphereVolume n := by
  have h := congr($(map_subtypeVal_riemannianVolume_sphere_eq_restrict_euclideanHausdorffMeasure
    (E := E) (n := n)) univ)
  rw [Measure.map_apply measurable_subtypeVal MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume Fact.out] at h
  rw [riemannianTotalVolume_def, measureReal_def, h,
    ENNReal.toReal_ofReal (roundSphereVolume_pos n).le]

end SurfaceMeasure

section Hausdorff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [MeasurableSpace E] [BorelSpace E]

/-- **The Riemannian volume of the unit sphere is normalized Hausdorff measure.** In every
dimension `n ≥ 0`, the Riemannian volume of `Sⁿ` for the round metric is the pullback of the
normalized `n`-dimensional Hausdorff measure `μHE[n]` along the inclusion into `E`. -/
theorem riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure
    [LindelofSpace (sphere (0 : E) 1)] :
    riemannianVolume (𝓡 n) (sphere (0 : E) 1) = (μHE[n] : Measure E).comap (↑) := by
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos ((Fact.out : finrank ℝ E = n + 1) ▸ Nat.succ_pos n)
  let ι : sphere (0 : E) 1 → E := (↑)
  have hι : MeasurableEmbedding ι :=
    MeasurableEmbedding.subtypeVal isClosed_sphere.measurableSet
  calc
    riemannianVolume (𝓡 n) (sphere (0 : E) 1)
      = ((riemannianVolume (𝓡 n) (sphere (0 : E) 1)).map ι).comap ι := (hι.comap_map _).symm
    _ = ((μHE[n]).restrict (ι '' univ)).comap ι := by
          rw [map_subtypeVal_riemannianVolume_sphere_eq_restrict_euclideanHausdorffMeasure,
            image_univ, Subtype.range_coe]
    _ = ((μHE[n] : Measure E).comap ι).restrict univ := (hι.restrict_comap _ _).symm
    _ = (μHE[n] : Measure E).comap (↑) := Measure.restrict_univ

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

/-- **Total Riemannian volume of the round sphere of radius `r > 0`**: `Vol(Sⁿ(r)) = r ^ n |Sⁿ|`. -/
@[simp]
theorem riemannianTotalVolume_sphereRoundMetricOfRadius
    [CompactSpace (sphere (0 : E) 1)] {r : ℝ} (hr : 0 < r) :
    riemannianTotalVolume (𝓡 n)
        (WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr)) =
      r ^ n * roundSphereVolume n := by
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos ((Fact.out : finrank ℝ E = n + 1) ▸ Nat.succ_pos n)
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
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
