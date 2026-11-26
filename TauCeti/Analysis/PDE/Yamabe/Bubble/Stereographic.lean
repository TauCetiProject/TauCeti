/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Analysis.PDE.Yamabe.ConformalLaplacian
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Volume
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import TauCeti.MeasureTheory.Integral.Bochner.Affine
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Yamabe bubbles as stereographic pullbacks of the round sphere

Let `n ≠ 2` and let `U_{t,b}` be the Yamabe bubble of scale `t > 0` centred at `b` on `ℝⁿ`
(`TauCeti.Yamabe.bubble`). This file proves that its Yamabe conformal factor
`U_{t,b} ^ (4 / (n - 2))` is the round metric of the unit sphere `Sⁿ` read in rescaled
stereographic coordinates: if `σ = stereographic' n v` is Mathlib's stereographic chart from a
unit vector `v` and `Φ(x) = σ⁻¹((2 / t) (x - b))`, then for all tangent vectors `a`, `c` at `x`,

`⟪dΦ_x a, dΦ_x c⟫_{Sⁿ} = U_{t,b}(x) ^ (4 / (n - 2)) ⟪a, c⟫`.

In other words, `Φ` is an isometry from `(ℝⁿ, U_{t,b} ^ (4 / (n - 2)) δ)` onto the round sphere
minus the point `v`. Consequently, its Riemannian Jacobian at `x` is the critical power
`U_{t,b}(x) ^ pₙ`, where `pₙ = 2 n / (n - 2)` (`TauCeti.Yamabe.criticalExponent`), and `Φ` pushes
Lebesgue measure weighted by `U_{t,b} ^ pₙ` forward to the Riemannian volume of `Sⁿ \ {v}` — hence
to the full Riemannian volume of `Sⁿ` whenever `n > 0`. In particular, for `n > 0`,
`u ↦ U_{t,b} · (u ∘ Φ)` preserves `L^{pₙ}` integrals between `Sⁿ` and `ℝⁿ`. The scale `2 / t`
reflects Mathlib's normalization of `σ`, whose inverse chart alone pulls the round metric back to
`U_{2,0} ^ (4 / (n - 2)) δ`.

This is how integrals over the round sphere, such as the Yamabe quotient of a conformal factor
on `Sⁿ`, become integrals over `ℝⁿ` weighted by bubbles.

## Main results

* `TauCeti.Yamabe.bubbleMetric`, `TauCeti.Yamabe.bubbleMetric_def`,
  `TauCeti.Yamabe.bubbleMetric_inner`, and `TauCeti.Yamabe.conformalLaplacian_bubbleMetric`:
  the bubble conformal metric on `ℝⁿ` and its conformal Laplacian rescaling formula.
* `TauCeti.Yamabe.inner_mfderiv_stereographic'_symm_smul_sub` and
  `TauCeti.Yamabe.isLocalRiemannianIsometry_stereographic'_symm_smul_sub`: the pullback of the
  round metric along `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ (4 / (n - 2))` times the Euclidean
  metric, and `x ↦ σ⁻¹((2 / t) (x - b))` is a local Riemannian isometry from `WithMetric
  (bubbleMetric ht b)` to `Sⁿ`.
* `TauCeti.Yamabe.riemannianJacobian_stereographic'_symm_smul_sub`: the Riemannian Jacobian of
  `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ pₙ`.
* `TauCeti.Yamabe.lintegral_riemannianVolume_sphere_eq_lintegral_bubble_rpow_mul` and
  `TauCeti.Yamabe.integral_riemannianVolume_sphere_eq_integral_bubble_rpow_smul`: the
  stereographic change of variables on the round sphere, for nonnegative and for vector-valued
  functions.
* `TauCeti.Yamabe.map_stereographic'_symm_smul_sub_withDensity_eq_restrict_riemannianVolume` and
  `TauCeti.Yamabe.map_stereographic'_symm_smul_sub_withDensity_eq_riemannianVolume`: rescaled
  stereographic pushforward of `U_{t,b} ^ pₙ dx` onto `Sⁿ \ {v}`, and onto `Sⁿ` for `n > 0`.
* `TauCeti.Yamabe.integrable_riemannianVolume_sphere_iff_bubble_rpow_criticalExponent` and
  `TauCeti.Yamabe.integral_abs_rpow_criticalExponent_sphere_eq_bubble_mul`: integrability and
  critical `L^{pₙ}` isometry on `Sⁿ` against `U_{t,b} ^ pₙ dx` on `ℝⁿ`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 3.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
-/

public section

open Bundle InnerProductSpace MeasureTheory Metric Module Set
open scoped ContDiff ENNReal Manifold

noncomputable section

namespace TauCeti.Yamabe

section BubbleMetric

/-- The bubble conformal metric `U_{t,b} ^ (4 / (n - 2)) δ` on `ℝⁿ`, obtained by rescaling the
Euclidean metric by the Yamabe conformal factor of `TauCeti.Yamabe.bubble`. -/
def bubbleMetric {n : ℕ} {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) :
    ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : EuclideanSpace ℝ (Fin n) ↦ TangentSpace (𝓡 n) x) :=
  ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
    (fun y ↦ bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)))
    ((contDiff_bubble t b (m := ∞)).contMDiff.rpow_const_of_ne
      (fun y ↦ (bubble_pos ht b y).ne') _)
    fun y ↦ Real.rpow_pos_of_pos (bubble_pos ht b y) _

/-- Unfolding lemma for `TauCeti.Yamabe.bubbleMetric`. -/
theorem bubbleMetric_def {n : ℕ} {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) :
    bubbleMetric ht b =
      ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
        (fun y ↦ bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)))
        ((contDiff_bubble t b (m := ∞)).contMDiff.rpow_const_of_ne
          (fun y ↦ (bubble_pos ht b y).ne') _)
        fun y ↦ Real.rpow_pos_of_pos (bubble_pos ht b y) _ :=
  (rfl)

/-- The bubble conformal metric on `ℝⁿ` is `U_{t,b} ^ (4 / (n - 2))` times the Euclidean inner
product. -/
@[simp]
theorem bubbleMetric_inner {n : ℕ} {t : ℝ} (ht : 0 < t) (b y : EuclideanSpace ℝ (Fin n))
    (v w : TangentSpace (𝓡 n) y) :
    (bubbleMetric ht b).inner y v w =
      bubble t b y ^ (4 / ((n : ℝ) - 2)) * inner ℝ v w := by
  rw [bubbleMetric_def, ContMDiffRiemannianMetric.rescale_inner,
    ContMDiffRiemannianMetric.ofLE_inner, riemannianMetricVectorSpace_inner,
    finrank_euclideanSpace_fin, TauCeti.Manifold.inner_tangentSpace_vectorSpace]

/-- The conformal Laplacian of `bubbleMetric ht b` at `w` is `U_{t,b} ^ (-(n + 2) / (n - 2))` times
the Euclidean conformal Laplacian of `U_{t,b} * w`. -/
theorem conformalLaplacian_bubbleMetric {n : ℕ} (hn : n ≠ 2) {t : ℝ} (ht : 0 < t)
    (b : EuclideanSpace ℝ (Fin n)) {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : ContMDiff (𝓡 n) 𝓘(ℝ) 2 w) (x : EuclideanSpace ℝ (Fin n)) :
    (letI : RiemannianBundle (fun y : EuclideanSpace ℝ (Fin n) ↦ TangentSpace (𝓡 n) y) :=
       ⟨(bubbleMetric ht b).toRiemannianMetric⟩;
     conformalLaplacian (𝓡 n) w x) =
      bubble t b x ^ (-((n : ℝ) + 2) / ((n : ℝ) - 2)) *
        (letI : RiemannianBundle (fun y : EuclideanSpace ℝ (Fin n) ↦ TangentSpace (𝓡 n) y) :=
           ⟨((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE
             (m := ∞) le_top).toRiemannianMetric⟩;
         conformalLaplacian (𝓡 n) (bubble t b * w) x) := by
  rw [bubbleMetric_def]
  simpa only [finrank_euclideanSpace_fin] using
    conformalLaplacian_rescale _ (by simpa using hn) (bubble_pos ht b) hw x

end BubbleMetric

section Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The derivative of the rescaled inverse stereographic chart `x ↦ σ⁻¹((2 / t) (x - b))`. -/
private theorem hasMFDerivAt_stereographic'_symm_smul_sub (v : sphere (0 : E) 1) (t : ℝ)
    (b x : EuclideanSpace ℝ (Fin n)) :
    HasMFDerivAt (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x
      ((mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b))).comp
        ((2 / t) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) := by
  have hA : HasMFDerivAt (𝓡 n) (𝓡 n) (fun y ↦ (2 / t) • (y - b)) x
      ((2 / t) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) :=
    (((hasFDerivAt_id x).sub_const b).const_smul (2 / t)).hasMFDerivAt
  have hsymm : MDifferentiableAt (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b)) :=
    mdifferentiableAt_atlas_symm (e := stereographic' n v) (Exists.intro v rfl) (by simp)
  exact hsymm.hasMFDerivAt.comp x hA

/-- **The bubbles are stereographic pullbacks of the round metric.** In dimension `n ≠ 2`, let
`σ = stereographic' n v` be a stereographic chart of the unit sphere `Sⁿ`. The round metric pulled
back along `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ (4 / (n - 2))` times the Euclidean metric of
`ℝⁿ`, where `U_{t,b}` is the bubble of scale `t > 0` centred at `b`. -/
theorem inner_mfderiv_stereographic'_symm_smul_sub (hn : n ≠ 2) (v : sphere (0 : E) 1) {t : ℝ}
    (ht : 0 < t) (b x a c : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (mfderiv (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x a)
        (mfderiv (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x c) =
      bubble t b x ^ (4 / ((n : ℝ) - 2)) * inner ℝ a c := by
  -- The tangent spaces at `x` and at `(2 / t) • (x - b)` are both the model space.
  have hd (d : TangentSpace (𝓡 n) ((2 / t) • (x - b))) :
      mfderiv (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x d =
        (2 / t) • mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b)) d := by
    rw [(hasMFDerivAt_stereographic'_symm_smul_sub v t b x).mfderiv]
    exact (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b))).map_smul (2 / t) d
  rw [hd a, hd c, real_inner_smul_left, real_inner_smul_right, inner_mfderiv_stereographic'_symm]
  have hU := bubble_rpow_four_div_finrank_sub_two (E := EuclideanSpace ℝ (Fin n))
    (by simpa using hn) ht b x
  rw [finrank_euclideanSpace_fin] at hU
  rw [hU, norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp
  ring

/-- **Rescaled inverse stereographic projection is a local Riemannian isometry.** In dimension
`n ≠ 2`, for `t > 0`, `x ↦ σ⁻¹((2 / t) (x - b))` is a smooth local Riemannian isometry from the
metric-indexed copy of `ℝⁿ` carrying the bubble conformal metric `U_{t,b} ^ (4 / (n - 2)) δ` into
the unit round sphere `Sⁿ`. -/
theorem isLocalRiemannianIsometry_stereographic'_symm_smul_sub (hn : n ≠ 2) (v : sphere (0 : E) 1)
    {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) :
    IsLocalRiemannianIsometry (𝓡 n) (𝓡 n)
      (((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) ∘
        (WithMetric.ofWithMetric : WithMetric (bubbleMetric ht b) → _)) := by
  let Φ : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1 :=
    (stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)
  have hinner (y : WithMetric (bubbleMetric ht b)) (a c : TangentSpace (𝓡 n) y) :
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) (Φ ∘ WithMetric.ofWithMetric) y a)
          (mfderiv (𝓡 n) (𝓡 n) (Φ ∘ WithMetric.ofWithMetric) y c) =
        inner ℝ a c := by
    rw [WithMetric.mfderiv_comp_ofWithMetric Φ y, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, WithMetric.inner_def, bubbleMetric_inner]
    exact inner_mfderiv_stereographic'_symm_smul_sub hn v ht b y.ofWithMetric _ _
  refine
    { contMDiff := ((isSmoothEmbedding_stereographic'_symm (k := ∞) v).contMDiff.comp
        (((contDiff_id.sub contDiff_const).const_smul (2 / t)).contMDiff)).comp
        WithMetric.contMDiff_ofWithMetric
      isInvertible_mfderiv := fun y ↦ ?_
      inner_mfderiv := hinner }
  set L := mfderiv (𝓡 n) (𝓡 n) (Φ ∘ WithMetric.ofWithMetric) y
  let eL := (L.toLinearMap.isometryOfInner (hinner y)).toLinearIsometryEquiv
    ((finrank_tangentSpace (I := 𝓡 n) y).trans (finrank_tangentSpace (I := 𝓡 n) _).symm)
  exact ⟨eL.toContinuousLinearEquiv, ContinuousLinearMap.ext fun w ↦ by
    simp only [eL, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometry.coe_toLinearIsometryEquiv,
      LinearMap.coe_isometryOfInner, ContinuousLinearMap.coe_coe]⟩

omit [Fact (finrank ℝ E = n + 1)] in
private theorem mul_stereographic_density_eq_bubble_rpow (hn : n ≠ 2) {t : ℝ} (ht : 0 < t)
    (b x : EuclideanSpace ℝ (Fin n)) :
    (2 / t) ^ n * (4 / (‖(2 / t) • (x - b)‖ ^ 2 + 4)) ^ n =
      bubble t b x ^ criticalExponent n := by
  have hU :=
    bubble_rpow_criticalExponent (E := EuclideanSpace ℝ (Fin n)) (by simpa using hn) ht b x
  rw [finrank_euclideanSpace_fin] at hU
  rw [hU, ← mul_pow, norm_smul, Real.norm_of_nonneg (by positivity)]
  congr 1
  field_simp
  ring

/-- **The round volume density in stereographic coordinates.** In dimension `n ≠ 2`, the Riemannian
Jacobian of `x ↦ σ⁻¹((2 / t) (x - b))` into the round sphere, for the standard orthonormal basis of
`ℝⁿ`, is the critical power `U_{t,b}(x) ^ pₙ` of the bubble of scale `t > 0` centred at `b`. -/
theorem riemannianJacobian_stereographic'_symm_smul_sub (hn : n ≠ 2) (v : sphere (0 : E) 1)
    {t : ℝ} (ht : 0 < t) (b x : EuclideanSpace ℝ (Fin n)) :
    riemannianJacobian (I := 𝓡 n) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x =
      bubble t b x ^ criticalExponent n := by
  have hn' : finrank ℝ (EuclideanSpace ℝ (Fin n)) ≠ 2 := by simpa using hn
  have hU4 := bubble_rpow_four_div_finrank_sub_two hn' ht b x
  have hUp := bubble_rpow_criticalExponent hn' ht b x
  rw [finrank_euclideanSpace_fin] at hU4 hUp
  rw [riemannianJacobian_eq_sqrt_pow_of_inner_mfderiv _
      (inner_mfderiv_stereographic'_symm_smul_sub hn v ht b x), hU4, Fintype.card_fin,
    Real.sqrt_sq (by positivity), hUp]

/-- The rescaled inverse stereographic chart `x ↦ σ⁻¹((2 / t) (x - b))` is injective, with image
the sphere minus the pole `v`. -/
private theorem injective_and_image_univ_stereographic'_symm_smul_sub (v : sphere (0 : E) 1)
    {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) :
    Function.Injective ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) ∧
      ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) '' univ = {v}ᶜ := by
  have hA : Function.Bijective fun y : EuclideanSpace ℝ (Fin n) ↦ (2 / t) • (y - b) :=
    ⟨fun y y' h ↦ sub_left_injective (smul_right_injective _ (by positivity) h),
      fun z ↦ ⟨(t / 2) • z + b, by simp [smul_smul, ht.ne']⟩⟩
  refine ⟨fun y y' h ↦ hA.injective ((stereographic' n v).symm.injOn (by simp) (by simp) h), ?_⟩
  rw [image_comp, image_univ_of_surjective hA.surjective, ← stereographic'_target v,
    (stereographic' n v).symm_image_target_eq_source, stereographic'_source]

end Metric

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]
  [LindelofSpace (sphere (0 : E) 1)]
  [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)]

/-- **Stereographic change of variables on the round sphere.** In dimension `n ≠ 0, 2`, integrating
a nonnegative function over the round sphere `Sⁿ` is integrating its pullback along
`x ↦ σ⁻¹((2 / t) (x - b))` over `ℝⁿ` against the density `U_{t,b} ^ pₙ`, where `σ` is a
stereographic chart, `t > 0` and `U_{t,b}` is the bubble of scale `t` centred at `b`. The function
need not be measurable. -/
theorem lintegral_riemannianVolume_sphere_eq_lintegral_bubble_rpow_mul (hn₀ : n ≠ 0)
    (hn : n ≠ 2) (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n))
    (φ : sphere (0 : E) 1 → ℝ≥0∞) :
    ∫⁻ y, φ y ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫⁻ x, ENNReal.ofReal (bubble t b x ^ criticalExponent n) *
        φ ((stereographic' n v).symm ((2 / t) • (x - b))) := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn₀⟩⟩
  obtain ⟨hinj, himage⟩ := injective_and_image_univ_stereographic'_symm_smul_sub v ht b
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.setLIntegral_riemannianVolume_image_of_injOn
    (I := 𝓡 n) rfl MeasurableSet.univ hinj.injOn
    (fun x _ ↦ (hasMFDerivAt_stereographic'_symm_smul_sub v t b x).mdifferentiableAt) φ
  rw [himage, restrict_compl_singleton] at h
  simpa only [Measure.restrict_univ, OrthonormalBasis.addHaar_eq_volume,
    riemannianJacobian_stereographic'_symm_smul_sub hn v ht, Function.comp_apply] using h

/-- **Stereographic change of variables on the round sphere.** In dimension `n ≠ 0, 2`, the
integral of a function over the round sphere `Sⁿ` is the integral of its pullback along
`x ↦ σ⁻¹((2 / t) (x - b))` over `ℝⁿ` against the density `U_{t,b} ^ pₙ`, where `σ` is a
stereographic chart, `t > 0` and `U_{t,b}` is the bubble of scale `t` centred at `b`. The function
need not be measurable or integrable. -/
theorem integral_riemannianVolume_sphere_eq_integral_bubble_rpow_smul {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (hn₀ : n ≠ 0) (hn : n ≠ 2) (v : sphere (0 : E) 1)
    {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) (φ : sphere (0 : E) 1 → G) :
    ∫ y, φ y ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫ x, bubble t b x ^ criticalExponent n •
        φ ((stereographic' n v).symm ((2 / t) • (x - b))) := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn₀⟩⟩
  obtain ⟨hinj, himage⟩ := injective_and_image_univ_stereographic'_symm_smul_sub v ht b
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.setIntegral_riemannianVolume_image_of_injOn
    (I := 𝓡 n) rfl MeasurableSet.univ hinj.injOn
    (fun x _ ↦ (hasMFDerivAt_stereographic'_symm_smul_sub v t b x).mdifferentiableAt) φ
  rw [himage, restrict_compl_singleton] at h
  simpa only [Measure.restrict_univ, OrthonormalBasis.addHaar_eq_volume,
    riemannianJacobian_stereographic'_symm_smul_sub hn v ht, Function.comp_apply] using h

end ChangeOfVariables

section Measure

/-- The linear scaling `x ↦ (2 / t) • x` on `ℝⁿ`, used to express `x ↦ (2 / t) • (x - b)` as an
invertible affine map. -/
private def bubbleScaleEquiv {n : ℕ} {t : ℝ} (ht : 0 < t) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (2 / t) (by positivity))

private theorem bubbleScaleEquiv_affine_apply {n : ℕ} {t : ℝ} (ht : 0 < t)
    (b x : EuclideanSpace ℝ (Fin n)) :
    -((2 / t) • b) + bubbleScaleEquiv ht x = (2 / t) • (x - b) := by
  simp [bubbleScaleEquiv, sub_eq_neg_add]

private theorem bubbleScaleEquiv_affine_symm_apply {n : ℕ} {t : ℝ} (ht : 0 < t)
    (b y : EuclideanSpace ℝ (Fin n)) :
    (2 / t) • ((bubbleScaleEquiv ht).symm (y - -((2 / t) • b)) - b) = y := by
  rw [← bubbleScaleEquiv_affine_apply ht, (bubbleScaleEquiv ht).apply_symm_apply]
  abel

private theorem image_bubbleScaleEquiv_affine_univ {n : ℕ} {t : ℝ} (ht : 0 < t)
    (b : EuclideanSpace ℝ (Fin n)) :
    (fun x : EuclideanSpace ℝ (Fin n) ↦ -((2 / t) • b) + bubbleScaleEquiv ht x) '' univ =
      univ :=
  eq_univ_of_forall fun y ↦ ⟨(bubbleScaleEquiv ht).symm (y - -((2 / t) • b)), mem_univ _, by
    dsimp only
    rw [bubbleScaleEquiv_affine_apply ht, bubbleScaleEquiv_affine_symm_apply ht]⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]
  [LindelofSpace (sphere (0 : E) 1)]
  [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)]

/-- **Rescaled stereographic pushforward onto the punctured sphere.** In dimension `n ≠ 2`, for
`t > 0`, `x ↦ σ⁻¹((2 / t) (x - b))` pushes Lebesgue measure weighted by `U_{t,b} ^ pₙ` forward to
the Riemannian volume of `Sⁿ` restricted to `{v}ᶜ`. -/
theorem map_stereographic'_symm_smul_sub_withDensity_eq_restrict_riemannianVolume (hn : n ≠ 2)
    (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) :
    Measure.map ((stereographic' n v).symm ∘ fun x ↦ (2 / t) • (x - b))
        (volume.withDensity fun x : EuclideanSpace ℝ (Fin n) ↦
          ENNReal.ofReal (bubble t b x ^ criticalExponent n)) =
      (riemannianVolume (𝓡 n) (sphere (0 : E) 1)).restrict {v}ᶜ := by
  let A := bubbleScaleEquiv (n := n) ht
  have haff : (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 / t) • (x - b)) =
      fun x ↦ -((2 / t) • b) + A x :=
    funext fun x ↦ (bubbleScaleEquiv_affine_apply ht b x).symm
  have hdet : |(LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))⁻¹| =
      ((2 / t) ^ n)⁻¹ := by
    have hA : (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
        (2 / t) • LinearMap.id := by
      ext x
      simp [A, bubbleScaleEquiv]
    rw [hA, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_euclideanSpace_fin,
      abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  have hcomp : ((stereographic' n v).symm ∘ fun x ↦ (2 / t) • (x - b)) =
      (stereographic' n v).symm ∘ (fun x ↦ -((2 / t) • b) + A x) := by
    rw [haff]
  rw [hcomp,
    ← Measure.map_map ((stereographic' n v).symm.isOpenEmbedding (by simp)).continuous.measurable
      (by fun_prop),
    Measure.map_affine_withDensity volume A (-((2 / t) • b))]
  have hdens : (fun y : EuclideanSpace ℝ (Fin n) ↦
      ENNReal.ofReal
          |(LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))⁻¹| *
        ENNReal.ofReal (bubble t b (A.symm (y - -((2 / t) • b))) ^ criticalExponent n)) =
      fun y : EuclideanSpace ℝ (Fin n) ↦ ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n) := by
    funext y
    let x := A.symm (y - -((2 / t) • b))
    have hmul := mul_stereographic_density_eq_bubble_rpow hn ht b x
    rw [bubbleScaleEquiv_affine_symm_apply ht b y] at hmul
    rw [hdet, ← ENNReal.ofReal_mul (by positivity), ← hmul, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n (by positivity)), one_mul]
  rw [hdens, map_stereographic'_symm_withDensity_eq_restrict_riemannianVolume v]

/-- **Rescaled stereographic pushforward onto the round sphere.** In positive dimension `n ≠ 2`,
for `t > 0`, `x ↦ σ⁻¹((2 / t) (x - b))` pushes Lebesgue measure weighted by `U_{t,b} ^ pₙ` forward
to the full Riemannian volume of `Sⁿ`. -/
theorem map_stereographic'_symm_smul_sub_withDensity_eq_riemannianVolume (hn₀ : 0 < n)
    (hn : n ≠ 2) (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) :
    Measure.map ((stereographic' n v).symm ∘ fun x ↦ (2 / t) • (x - b))
        (volume.withDensity fun x : EuclideanSpace ℝ (Fin n) ↦
          ENNReal.ofReal (bubble t b x ^ criticalExponent n)) =
      riemannianVolume (𝓡 n) (sphere (0 : E) 1) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn₀)
  rw [map_stereographic'_symm_smul_sub_withDensity_eq_restrict_riemannianVolume hn v ht b,
    restrict_compl_singleton v]

/-- **Integrability on `Sⁿ` via a Yamabe bubble.** In dimension `n ≠ 2` (including `n = 0`), for
`t > 0`, a function `f` on `Sⁿ` is integrable for the Riemannian volume if and only if
`x ↦ (U_{t,b}(x) ^ pₙ) • f (σ⁻¹((2 / t) (x - b)))` is Lebesgue integrable on `ℝⁿ`. -/
theorem integrable_riemannianVolume_sphere_iff_bubble_rpow_criticalExponent (hn : n ≠ 2)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (v : sphere (0 : E) 1) {t : ℝ}
    (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) (f : sphere (0 : E) 1 → F) :
    Integrable f (riemannianVolume (𝓡 n) (sphere (0 : E) 1)) ↔
      Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦
        (bubble t b x ^ criticalExponent n) •
          f ((stereographic' n v).symm ((2 / t) • (x - b)))) := by
  rw [integrable_riemannianVolume_sphere_iff_stereographic' v f]
  have haff := (bubbleScaleEquiv (n := n) ht).integrableOn_image_affine_iff (-((2 / t) • b))
    (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((4 / (‖y‖ ^ 2 + 4)) ^ n) • f ((stereographic' n v).symm y)) univ volume
  rw [image_bubbleScaleEquiv_affine_univ ht b, integrableOn_univ, integrableOn_univ] at haff
  rw [haff, ← integrable_smul_iff (c := (2 / t) ^ n) (pow_ne_zero n (by positivity))]
  refine integrable_congr (ae_of_all _ fun x ↦ ?_)
  rw [Pi.smul_apply, bubbleScaleEquiv_affine_apply ht b x, smul_smul,
    mul_stereographic_density_eq_bubble_rpow hn ht b x]

/-- **Critical `L^{pₙ}` isometry of the bubble pullback.** In positive dimension `n ≠ 2`, for
`t > 0` and every `u : Sⁿ → ℝ`, the integral of `|u| ^ pₙ` on the unit round sphere equals the
Euclidean integral of `|U_{t,b} · (u ∘ Φ)| ^ pₙ`. -/
theorem integral_abs_rpow_criticalExponent_sphere_eq_bubble_mul (hn₀ : 0 < n) (hn : n ≠ 2)
    (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n))
    (u : sphere (0 : E) 1 → ℝ) :
    ∫ p, |u p| ^ criticalExponent n ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫ x : EuclideanSpace ℝ (Fin n),
        |bubble t b x *
          u ((stereographic' n v).symm ((2 / t) • (x - b)))| ^ criticalExponent n := by
  rw [integral_riemannianVolume_sphere_eq_integral_bubble_rpow_smul hn₀.ne' hn v ht b]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [smul_eq_mul, abs_mul, abs_of_pos (bubble_pos ht b x),
    Real.mul_rpow (bubble_pos ht b x).le (abs_nonneg _)]

end Measure

end TauCeti.Yamabe
