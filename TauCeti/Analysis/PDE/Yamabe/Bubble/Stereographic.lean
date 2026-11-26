/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null

/-!
# The Yamabe bubbles as stereographic pullbacks of the round sphere

Let `n ≠ 2` and let `U_{t,b}` be the Yamabe bubble of scale `t > 0` centred at `b` on `ℝⁿ`
(`TauCeti.Yamabe.bubble`). This file proves that its Yamabe conformal factor
`U_{t,b} ^ (4 / (n - 2))` is the round metric of the unit sphere `Sⁿ` read in rescaled
stereographic coordinates: if `σ = stereographic' n v` is Mathlib's stereographic chart from a
unit vector `v` and `Φ(x) = σ⁻¹((2 / t) (x - b))`, then for all tangent vectors `a`, `c` at `x`,

`⟪dΦ_x a, dΦ_x c⟫_{Sⁿ} = U_{t,b}(x) ^ (4 / (n - 2)) ⟪a, c⟫`.

In other words, `Φ` is an isometry from `(ℝⁿ, U_{t,b} ^ (4 / (n - 2)) δ)` onto the round sphere
minus the point `v`. Classically, this identification explains why the metric
`U_{t,b} ^ (4 / (n - 2)) δ` has constant scalar curvature `n (n - 1)`, matching the bubble
equation `aₙ Δ⁺ U = n (n - 1) U ^ (pₙ - 1)`
(`TauCeti.Yamabe.conformalCoefficient_mul_neg_laplacian_bubble`), and why the Sobolev quotient of
a bubble is the Yamabe constant of the sphere; neither consequence is derived from it here. The
scale `2 / t` reflects Mathlib's normalization
of `σ`, whose inverse chart alone pulls the round metric back to `U_{2,0} ^ (4 / (n - 2)) δ`.

Taking the square root of the Gram determinant, the Riemannian volume density of `Φ` is
`(U_{t,b} ^ (4 / (n - 2))) ^ (n / 2) = U_{t,b} ^ pₙ`, with `pₙ = 2 n / (n - 2)`. Since `Φ` is a
bijection of `ℝⁿ` onto the sphere minus a point of volume zero, this gives the stereographic change
of variables on the round sphere: for every function `f` on `Sⁿ`, with `n ≠ 0, 2`,

`∫_{Sⁿ} f dV = ∫_{ℝⁿ} f(Φ(x)) U_{t,b}(x) ^ pₙ dx`.

This is how integrals over the round sphere, such as the Yamabe quotient of a conformal factor
on `Sⁿ`, become integrals over `ℝⁿ` weighted by bubbles.

## Main results

* `TauCeti.Yamabe.inner_mfderiv_stereographic'_symm_smul_sub`: the pullback of the round metric
  along `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ (4 / (n - 2))` times the Euclidean metric.
* `TauCeti.Yamabe.riemannianJacobian_stereographic'_symm_smul_sub`: the Riemannian Jacobian of
  `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ pₙ`.
* `TauCeti.Yamabe.lintegral_riemannianVolume_sphere_eq_lintegral_bubble_rpow_mul` and
  `TauCeti.Yamabe.integral_riemannianVolume_sphere_eq_integral_bubble_rpow_smul`: the
  stereographic change of variables on the round sphere, for nonnegative and for vector-valued
  functions.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 3.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
-/

public section

noncomputable section

open Bundle MeasureTheory Metric Module Set
open scoped ENNReal Manifold

namespace TauCeti.Yamabe

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

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

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

end TauCeti.Yamabe
