/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Immersion
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry

/-!
# Riemannian volume and stereographic integration on round spheres

The unit sphere `Sⁿ = sphere (0 : E) 1` of an `(n + 1)`-dimensional real inner product space `E`
carries the round Riemannian metric `TauCeti.sphereRoundMetric`, induced by the isometric
embedding `((↑) : sphere (0 : E) 1 → E)`. Applying the isometric-embedding volume theorem
`TauCeti.riemannianVolume_eq_comap_euclideanHausdorffMeasure` identifies its Riemannian volume
measure `riemannianVolume (𝓡 n) (sphere (0 : E) 1)` with both the pullback of `n`-dimensional
normalized Euclidean Hausdorff measure `μHE[n]` and Mathlib's cone-based surface measure
`(volume : Measure E).toSphere`. Consequently, its total Riemannian volume is strictly positive and
equals `TauCeti.roundSphereVolume n = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`, and the round sphere of
radius `r > 0` (`TauCeti.sphereRoundMetricOfRadius`) has total Riemannian volume
`r ^ n * roundSphereVolume n`.

In stereographic coordinates `stereographic' n v` from `v ∈ Sⁿ`, the inverse chart map read in `E`
is conformal with factor `4 / (‖y‖² + 4)` (`TauCeti.inner_mfderiv_stereographic'_symm`), so its
Euclidean Jacobian `normDet` is `(4 / (‖y‖² + 4)) ^ n`. When `1 ≤ n`, singletons have Riemannian
volume zero (`S⁰` is the sharp exception: its two points each carry mass `1`), so omitting the pole
`v` does not change integrals and integrating over `Sⁿ` reduces to integrating over `ℝⁿ` against
`(4 / (‖y‖² + 4)) ^ n` times Lebesgue `volume`.

## Main results

* `TauCeti.inner_fderiv_coe_comp_stereographic'_symm` and
  `TauCeti.normDet_fderiv_coe_comp_stereographic'_symm`: the ambient inner product and Euclidean
  Jacobian `(4 / (‖y‖² + 4)) ^ n` of inverse stereographic projection.
* `TauCeti.riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure` and
  `TauCeti.riemannianVolume_sphere_eq_toSphere`: `riemannianVolume (𝓡 n) (sphere (0 : E) 1)` agrees
  with `(μHE[n]).comap (↑)` and `(volume : Measure E).toSphere`.
* `TauCeti.riemannianTotalVolume_sphere`, `TauCeti.riemannianTotalVolume_sphere_pos`, and
  `TauCeti.riemannianTotalVolume_sphereRoundMetricOfRadius`: the total Riemannian volumes of unit
  and radius-`r` round spheres.
* `TauCeti.instNullSingletonClassRiemannianVolumeSphere`: `riemannianVolume` on `Sⁿ` has null
  singletons when `n ≠ 0`.
* `TauCeti.lintegral_riemannianVolume_sphere_eq_stereographic'` and
  `TauCeti.integral_riemannianVolume_sphere_eq_stereographic'`: stereographic coordinate formulas
  for Lebesgue and Bochner integrals over `Sⁿ` (`1 ≤ n`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 3.
-/

public section

open Bundle Function MeasureTheory Measure Metric Module Set
open scoped ContDiff ENNReal InnerProductSpace Manifold

noncomputable section

namespace TauCeti

section StereographicJacobian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- Read in the ambient space `E`, the Fréchet derivative of inverse stereographic projection
`(↑) ∘ (stereographic' n v).symm` scales inner products by `(4 / (‖y‖² + 4))²`. -/
theorem inner_fderiv_coe_comp_stereographic'_symm (v : sphere (0 : E) 1)
    (y a b : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y a)
        (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y b) =
      (4 / (‖y‖ ^ 2 + 4)) ^ 2 * inner ℝ a b := by
  have hsymm : MDifferentiableAt (𝓡 n) (𝓡 n) (stereographic' n v).symm y :=
    mdifferentiableAt_atlas_symm (e := stereographic' n v) (Exists.intro v rfl) (by simp)
  have hd (c : TangentSpace (𝓡 n) y) :
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) ((stereographic' n v).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y c) =
        fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y c := by
    rw [← mvfderiv_comp_apply y ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero)
      hsymm, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact congrArg _ (NormedSpace.fromTangentSpace_apply y c)
  rw [← inner_mfderiv_stereographic'_symm v y a b, inner_tangentSpace_sphere, hd a, hd b]

/-- **Jacobian of inverse stereographic projection.** Read in the ambient space `E`, the inverse of
the stereographic chart `stereographic' n v` has Euclidean Jacobian `(4 / (‖y‖² + 4)) ^ n` at
`y`. -/
theorem normDet_fderiv_coe_comp_stereographic'_symm (v : sphere (0 : E) 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y).normDet =
      (4 / (‖y‖ ^ 2 + 4)) ^ n := by
  set A := (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y).toLinearMap
  set c : ℝ := 4 / (‖y‖ ^ 2 + 4)
  have hc : 0 ≤ c := by positivity
  let u := EuclideanSpace.basisFun (Fin n) ℝ
  have hgram : Matrix.gram ℝ (fun i ↦ A (u i)) = c ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.gram_apply, ContinuousLinearMap.coe_coe, A, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [inner_fderiv_coe_comp_stereographic'_symm, orthonormal_iff_ite.mp u.orthonormal i j,
      mul_ite, mul_one, mul_zero]
  have hsq : A.normDet ^ 2 = (c ^ n) ^ 2 := by
    have h := A.normDet_sq_eq_det_gram u
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [h, hgram, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, pow_right_comm]
  exact (sq_eq_sq₀ A.normDet_nonneg (pow_nonneg hc n)).mp hsq

end StereographicJacobian

section SphereVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

section AmbientMeasure

variable [MeasurableSpace E] [BorelSpace E]

/-- **Riemannian volume of the unit round sphere.** On the unit sphere of an `(n + 1)`-dimensional
real inner product space `E`, the Riemannian volume measure of the round metric is the pullback of
`n`-dimensional normalized Euclidean Hausdorff measure `μHE[n]` along the inclusion into `E`. -/
theorem riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure :
    riemannianVolume (𝓡 n) (sphere (0 : E) 1) = (μHE[n] : Measure E).comap (↑) := by
  have h := riemannianVolume_eq_comap_euclideanHausdorffMeasure
    (I := 𝓡 n) (M := sphere (0 : E) 1) (E := E)
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet)
    ((contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero)
    (fun x a b ↦ (Manifold.inner_tangentSpace_vectorSpace _ _).trans
      (inner_tangentSpace_sphere x a b).symm)
  rwa [finrank_euclideanSpace_fin] at h

/-- On the unit sphere of a finite-dimensional real inner product space, the Riemannian volume
measure of the round metric coincides with Mathlib's cone-based surface measure
`(volume : Measure E).toSphere`. -/
theorem riemannianVolume_sphere_eq_toSphere :
    riemannianVolume (𝓡 n) (sphere (0 : E) 1) = (volume : Measure E).toSphere := by
  rw [riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure,
    toSphere_volume_eq_comap_euclideanHausdorffMeasure, (Fact.out : finrank ℝ E = n + 1),
    Nat.add_sub_cancel]

/-- Pushing the Riemannian volume of the unit sphere forward into `E` yields the restriction of
`n`-dimensional normalized Euclidean Hausdorff measure to `sphere (0 : E) 1`. -/
theorem map_subtypeVal_riemannianVolume_sphere :
    (riemannianVolume (𝓡 n) (sphere (0 : E) 1)).map ((↑) : sphere (0 : E) 1 → E) =
      (μHE[n] : Measure E).restrict (sphere (0 : E) 1) := by
  rw [riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).map_comap, Subtype.range_coe]

/-- The Riemannian volume measure gives the unit `n`-sphere total mass
`ENNReal.ofReal (roundSphereVolume n)`. -/
theorem riemannianVolume_sphere_univ :
    riemannianVolume (𝓡 n) (sphere (0 : E) 1) univ = ENNReal.ofReal (roundSphereVolume n) := by
  rw [riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).comap_apply, image_univ,
    Subtype.range_coe, euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume Fact.out]

/-- **Total Riemannian volume of the unit round sphere.** -/
@[simp]
theorem riemannianTotalVolume_sphere :
    riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) = roundSphereVolume n := by
  rw [riemannianTotalVolume_def, measureReal_def, riemannianVolume_sphere_univ,
    ENNReal.toReal_ofReal (roundSphereVolume_pos n).le]

/-- The unit round `n`-sphere has strictly positive total Riemannian volume in every dimension. -/
theorem riemannianTotalVolume_sphere_pos :
    0 < riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) := by
  rw [riemannianTotalVolume_sphere]
  exact roundSphereVolume_pos n

/-- **Total Riemannian volume of the unit round sphere**, in terms of the Gamma function:
`Vol(Sⁿ) = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`. -/
theorem riemannianTotalVolume_sphere_eq_two_mul_pi_rpow_div_Gamma :
    riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) =
      2 * Real.pi ^ (((n : ℝ) + 1) / 2) / Real.Gamma (((n : ℝ) + 1) / 2) := by
  rw [riemannianTotalVolume_sphere, roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma]

/-- When `n ≠ 0`, singletons on the unit `n`-sphere have Riemannian volume zero. (For `n = 0`, the
two-point sphere `S⁰` carries counting measure.) -/
instance instNullSingletonClassRiemannianVolumeSphere [NeZero n] :
    NullSingletonClass (riemannianVolume (𝓡 n) (sphere (0 : E) 1)) := by
  refine ⟨fun v ↦ ?_⟩
  have : NullSingletonClass (μH[n] : Measure E) :=
    nullSingletonClass_hausdorff E (Nat.cast_pos.2 (NeZero.pos n))
  rw [riemannianVolume_sphere_eq_comap_euclideanHausdorffMeasure,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).comap_apply, image_singleton,
    euclideanHausdorffMeasure_def, smul_apply, measure_singleton, smul_zero]

/-- **Stereographic Lebesgue integration on the unit sphere.** For `1 ≤ n` and any pole `v ∈ Sⁿ`,
integrating a nonnegative function over `Sⁿ` against its Riemannian volume equals integrating its
stereographic coordinate expression over `ℝⁿ` against `(4 / (‖y‖² + 4)) ^ n` times Lebesgue
`volume`. The bound `1 ≤ n` is sharp: on `S⁰` each of the two points has mass `1`, so omitting `v`
loses half the total mass. -/
theorem lintegral_riemannianVolume_sphere_eq_stereographic' (hn : 1 ≤ n) (v : sphere (0 : E) 1)
    (φ : sphere (0 : E) 1 → ℝ≥0∞) :
    ∫⁻ x, φ x ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫⁻ y, ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n) * φ ((stereographic' n v).symm y) ∂volume := by
  have : NeZero n := ⟨by omega⟩
  have hsrc : ({v}ᶜ : Set (sphere (0 : E) 1)) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) (-v)).source := by
    rw [chartAt_sphere, neg_neg, stereographic'_source]
  rw [← restrict_compl_singleton v (μ := riemannianVolume (𝓡 n) (sphere (0 : E) 1)),
    setLIntegral_riemannianVolume_eq_lintegral_normDet_of_subset hsrc
      isOpen_compl_singleton.measurableSet
      (fun x _ ↦ (contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero x)
      (fun x _ a b ↦ (Manifold.inner_tangentSpace_vectorSpace _ _).trans
        (inner_tangentSpace_sphere x a b).symm)
      φ]
  rw [extChartAt_coe, modelWithCornersSelf_coe, id_comp, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, comp_id, chartAt_sphere, neg_neg,
    ← stereographic'_source (n := n) v, OpenPartialHomeomorph.image_source_eq_target,
    stereographic'_target, Measure.restrict_univ]
  simp_rw [normDet_fderiv_coe_comp_stereographic'_symm]

/-- **Stereographic Bochner integration on the unit sphere.** For `1 ≤ n` and any pole `v ∈ Sⁿ`,
integrating a Banach-space-valued function over `Sⁿ` against its Riemannian volume equals
integrating its stereographic coordinate expression over `ℝⁿ` weighted by `(4 / (‖y‖² + 4)) ^ n`.
The bound `1 ≤ n` is sharp: on `S⁰` omitting `v` drops a point of mass `1`. -/
theorem integral_riemannianVolume_sphere_eq_stereographic' {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (hn : 1 ≤ n) (v : sphere (0 : E) 1) (φ : sphere (0 : E) 1 → G) :
    ∫ x, φ x ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫ y, (4 / (‖y‖ ^ 2 + 4)) ^ n • φ ((stereographic' n v).symm y) ∂volume := by
  have : NeZero n := ⟨by omega⟩
  have hsrc : ({v}ᶜ : Set (sphere (0 : E) 1)) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) (-v)).source := by
    rw [chartAt_sphere, neg_neg, stereographic'_source]
  rw [← restrict_compl_singleton v (μ := riemannianVolume (𝓡 n) (sphere (0 : E) 1)),
    setIntegral_riemannianVolume_eq_integral_normDet_of_subset hsrc
      isOpen_compl_singleton.measurableSet
      (fun x _ ↦ (contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero x)
      (fun x _ a b ↦ (Manifold.inner_tangentSpace_vectorSpace _ _).trans
        (inner_tangentSpace_sphere x a b).symm)
      φ]
  rw [extChartAt_coe, modelWithCornersSelf_coe, id_comp, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, comp_id, chartAt_sphere, neg_neg,
    ← stereographic'_source (n := n) v, OpenPartialHomeomorph.image_source_eq_target,
    stereographic'_target, Measure.restrict_univ]
  simp_rw [normDet_fderiv_coe_comp_stereographic'_symm]

end AmbientMeasure

/-- **Total Riemannian volume of the round sphere of radius `r`.** Carrying `r²` times the unit
round metric (`TauCeti.sphereRoundMetricOfRadius`), the `n`-sphere has total Riemannian volume
`r ^ n * roundSphereVolume n`. -/
@[simp]
theorem riemannianTotalVolume_sphereRoundMetricOfRadius {r : ℝ} (hr : 0 < r) :
    riemannianTotalVolume (𝓡 n)
        (WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr)) =
      r ^ n * roundSphereVolume n := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set g₀ := (sphereRoundMetric (E := E) (n := n)).ofLE (m := ∞) le_top
  have hvol : riemannianTotalVolume (𝓡 n) (WithMetric g₀) =
      riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) :=
    (WithMetric.riemannianIsometryOfRiemannianBundleEq
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm).riemannianTotalVolume_eq
  have hexp : (2 : ℕ) * ((n : ℝ) / 2) = (n : ℝ) := by push_cast; ring
  rw [sphereRoundMetricOfRadius_def, WithMetric.riemannianTotalVolume_rescale,
    integral_const, smul_eq_mul, ← riemannianTotalVolume_def, hvol, riemannianTotalVolume_sphere,
    finrank_euclideanSpace_fin, ← Real.rpow_natCast_mul hr.le, hexp, Real.rpow_natCast, mul_comm]

end SphereVolume

end TauCeti
