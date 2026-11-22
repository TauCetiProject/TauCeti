/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Volume
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
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
to the full Riemannian volume of `Sⁿ` whenever `n > 0`. In particular, `u ↦ U_{t,b} · (u ∘ Φ)`
preserves `L^{pₙ}` integrals between `Sⁿ` and `ℝⁿ`. The scale `2 / t` reflects Mathlib's
normalization of `σ`, whose inverse chart alone pulls the round metric back to
`U_{2,0} ^ (4 / (n - 2)) δ`.

## Main results

* `TauCeti.Yamabe.inner_mfderiv_stereographic'_symm_smul_sub`: the pullback of the round metric
  along `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ (4 / (n - 2))` times the Euclidean metric.
* `TauCeti.Yamabe.riemannianJacobian_stereographic'_symm_smul_sub`: the Riemannian Jacobian of
  `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ pₙ`.
* `TauCeti.Yamabe.map_stereographic'_symm_smul_sub_withDensity_eq_restrict_riemannianVolume` and
  `TauCeti.Yamabe.map_stereographic'_symm_smul_sub_withDensity_eq_riemannianVolume`: rescaled
  stereographic pushforward of `U_{t,b} ^ pₙ dx` onto `Sⁿ \ {v}`, and onto `Sⁿ` for `n > 0`.
* `TauCeti.Yamabe.lintegral_riemannianVolume_sphere_eq_bubble_rpow_criticalExponent`,
  `TauCeti.Yamabe.integrable_riemannianVolume_sphere_iff_bubble_rpow_criticalExponent`,
  `TauCeti.Yamabe.integral_riemannianVolume_sphere_eq_bubble_rpow_criticalExponent`, and
  `TauCeti.Yamabe.integral_abs_rpow_criticalExponent_sphere_eq_bubble_mul`: integration on `Sⁿ`
  against `U_{t,b} ^ pₙ dx` on `ℝⁿ`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 3.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
-/

public section

open Bundle MeasureTheory Metric Module Set
open scoped ENNReal Manifold

noncomputable section

namespace TauCeti.Yamabe

section Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The bubbles are stereographic pullbacks of the round metric.** In dimension `n ≠ 2`, let
`σ = stereographic' n v` be a stereographic chart of the unit sphere `Sⁿ`. The round metric pulled
back along `x ↦ σ⁻¹((2 / t) (x - b))` is `U_{t,b} ^ (4 / (n - 2))` times the Euclidean metric of
`ℝⁿ`, where `U_{t,b}` is the bubble of scale `t > 0` centred at `b`. -/
theorem inner_mfderiv_stereographic'_symm_smul_sub (hn : n ≠ 2) (v : sphere (0 : E) 1) {t : ℝ}
    (ht : 0 < t) (b x a c : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (mfderiv (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x a)
        (mfderiv (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x c) =
      bubble t b x ^ (4 / ((n : ℝ) - 2)) * inner ℝ a c := by
  have hA : HasMFDerivAt (𝓡 n) (𝓡 n) (fun y ↦ (2 / t) • (y - b)) x
      ((2 / t) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) :=
    (((hasFDerivAt_id x).sub_const b).const_smul (2 / t)).hasMFDerivAt
  have hsymm : MDifferentiableAt (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b)) :=
    mdifferentiableAt_atlas_symm (e := stereographic' n v) (Exists.intro v rfl) (by simp)
  -- The tangent spaces at `x` and at `(2 / t) • (x - b)` are both the model space.
  have hd (d : TangentSpace (𝓡 n) ((2 / t) • (x - b))) :
      mfderiv (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x d =
        (2 / t) • mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b)) d := by
    rw [(hsymm.hasMFDerivAt.comp x hA).mfderiv]
    exact (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b))).map_smul (2 / t) d
  rw [hd a, hd c, real_inner_smul_left, real_inner_smul_right, inner_mfderiv_stereographic'_symm]
  have hU := bubble_rpow_four_div_finrank_sub_two (E := EuclideanSpace ℝ (Fin n))
    (by simpa using hn) ht b x
  rw [finrank_euclideanSpace_fin] at hU
  rw [hU, norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp
  ring

/-- **Riemannian Jacobian of rescaled inverse stereographic projection.** In dimension `n ≠ 2`, for
every `t ≥ 0`, the Riemannian Jacobian of `x ↦ σ⁻¹((2 / t) (x - b))` relative to the standard
orthonormal basis of `ℝⁿ` is `U_{t,b}(x) ^ pₙ`. -/
theorem riemannianJacobian_stereographic'_symm_smul_sub (hn : n ≠ 2) (v : sphere (0 : E) 1)
    {t : ℝ} (ht : 0 ≤ t) (b x : EuclideanSpace ℝ (Fin n)) :
    riemannianJacobian (I := 𝓡 n) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x =
      bubble t b x ^ criticalExponent n := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rcases ht.eq_or_lt with rfl | ht
  · have hconst : ((stereographic' n v).symm ∘ fun y : EuclideanSpace ℝ (Fin n) ↦
        (2 / (0 : ℝ)) • (y - b)) = fun _ ↦ (stereographic' n v).symm 0 := by
      ext y
      simp
    rw [hconst, riemannianJacobian_eq_normDet e, mfderiv_const,
      ContinuousLinearMap.toLinearMap_zero]
    change LinearMap.normDet (0 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) = _
    rw [LinearMap.normDet_zero, finrank_euclideanSpace_fin, bubble_zero_left,
      finrank_euclideanSpace_fin, criticalExponent_def]
    rcases eq_or_ne n 0 with rfl | hn₀
    · simp
    · have hn' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
      have hn₀' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn₀
      simp [hn₀, Real.zero_rpow (div_ne_zero hn' two_ne_zero),
        Real.zero_rpow (div_ne_zero (mul_ne_zero two_ne_zero hn₀') hn')]
  · have hA : HasMFDerivAt (𝓡 n) (𝓡 n) (fun y ↦ (2 / t) • (y - b)) x
        ((2 / t) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) :=
      (((hasFDerivAt_id x).sub_const b).const_smul (2 / t)).hasMFDerivAt
    have hsymm : MDifferentiableAt (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b)) :=
      mdifferentiableAt_atlas_symm (e := stereographic' n v) (Exists.intro v rfl) (by simp)
    let J : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        TangentSpace (𝓡 n) ((stereographic' n v).symm ((2 / t) • (x - b))) :=
      (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b))).toLinearMap
    have hcomp :
        (mfderiv (𝓡 n) (𝓡 n)
            ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x).toLinearMap =
          (2 / t) • J := by
      ext d
      rw [(hsymm.hasMFDerivAt.comp x hA).mfderiv]
      exact (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b))).map_smul (2 / t) d
    rw [riemannianJacobian_eq_normDet e, hcomp, LinearMap.normDet_smul,
      ← riemannianJacobian_eq_normDet e, riemannianJacobian_stereographic'_symm,
      finrank_euclideanSpace_fin, Real.norm_of_nonneg (by positivity)]
    have h :=
      bubble_rpow_criticalExponent (E := EuclideanSpace ℝ (Fin n)) (by simpa using hn) ht b x
    rw [finrank_euclideanSpace_fin] at h
    rw [h, ← mul_pow, norm_smul, Real.norm_of_nonneg (by positivity)]
    congr 1
    field_simp
    ring

end Metric

section Measure

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
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (2 / t) (by positivity))
  let c : EuclideanSpace ℝ (Fin n) := -((2 / t) • b)
  have hfun : ((stereographic' n v).symm ∘ fun x ↦ (2 / t) • (x - b)) =
      (stereographic' n v).symm ∘ fun x ↦ c + A x := by
    ext x
    simp [c, A, sub_eq_add_neg, add_comm]
  have hdet : |(LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)))⁻¹| = (t / 2) ^ n := by
    have hA : (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
        (2 / t) • LinearMap.id := by
      ext x
      simp [A]
    rw [hA, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_euclideanSpace_fin,
      ← inv_pow, inv_div, abs_of_nonneg (by positivity)]
  have hweight (y : EuclideanSpace ℝ (Fin n)) :
      ENNReal.ofReal |(LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n)))⁻¹| *
        ENNReal.ofReal (bubble t b (A.symm (y - c)) ^ criticalExponent n) =
      ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n) := by
    have hAsymm : A.symm (y - c) = (t / 2) • y + b :=
      A.symm_apply_eq.mpr <| by
        simp [A, c, smul_add, smul_smul, div_mul_div_cancel₀ ht.ne', sub_neg_eq_add]
    have hb := bubble_rpow_criticalExponent (E := EuclideanSpace ℝ (Fin n))
      (by simpa using hn) ht b (A.symm (y - c))
    rw [finrank_euclideanSpace_fin, hAsymm, add_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg (by positivity)] at hb
    rw [hdet, hAsymm, hb, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  rw [hfun, ← Measure.map_map
      ((stereographic' n v).symm.isOpenEmbedding (by simp)).continuous.measurable
      (by fun_prop : Measurable fun x ↦ c + A x),
    Measure.map_affine_withDensity volume A c]
  simp_rw [hweight]
  exact map_stereographic'_symm_withDensity_eq_restrict_riemannianVolume v

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
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (by simp))]

omit [LindelofSpace (sphere (0 : E) 1)] [MeasurableSpace (sphere (0 : E) 1)]
  [BorelSpace (sphere (0 : E) 1)] in
private theorem injOn_stereographic'_symm_smul_sub (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t)
    (b : EuclideanSpace ℝ (Fin n)) :
    InjOn ((stereographic' n v).symm ∘ fun x ↦ (2 / t) • (x - b)) univ := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (Homeomorph.subRight b).trans (Homeomorph.smulOfNeZero (2 / t) (by positivity))
  exact ((isSmoothEmbedding_stereographic'_symm (k := 1) v).isEmbedding.injective.comp
    e.injective).injOn

omit [LindelofSpace (sphere (0 : E) 1)] [MeasurableSpace (sphere (0 : E) 1)]
  [BorelSpace (sphere (0 : E) 1)] in
private theorem mdifferentiableAt_stereographic'_symm_smul_sub (v : sphere (0 : E) 1) (t : ℝ)
    (b x : EuclideanSpace ℝ (Fin n)) :
    MDifferentiableAt (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x :=
  (mdifferentiableAt_atlas_symm (e := stereographic' n v) (Exists.intro v rfl) (by simp)).comp x
    (((hasFDerivAt_id x).sub_const b).const_smul (2 / t)).hasMFDerivAt.mdifferentiableAt

omit [LindelofSpace (sphere (0 : E) 1)] [MeasurableSpace (sphere (0 : E) 1)]
  [BorelSpace (sphere (0 : E) 1)] in
private theorem image_stereographic'_symm_smul_sub_univ (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t)
    (b : EuclideanSpace ℝ (Fin n)) :
    ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) '' univ = {v}ᶜ := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (Homeomorph.subRight b).trans (Homeomorph.smulOfNeZero (2 / t) (by positivity))
  rw [image_comp, image_univ, show (fun y ↦ (2 / t) • (y - b)) = e from rfl, e.surjective.range_eq]
  simpa using (stereographic' n v).symm.image_source_eq_target

/-- **Lower Lebesgue integration on `Sⁿ` via a Yamabe bubble.** In positive dimension `n ≠ 2`, for
`t > 0`, the lower Lebesgue integral of any `f : Sⁿ → ℝ≥0∞` against the Riemannian volume is its
rescaled stereographic integral weighted by `U_{t,b} ^ pₙ`. No measurability assumption on `f` is
required. -/
theorem lintegral_riemannianVolume_sphere_eq_bubble_rpow_criticalExponent (hn₀ : 0 < n)
    (hn : n ≠ 2) (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n))
    (f : sphere (0 : E) 1 → ℝ≥0∞) :
    ∫⁻ p, f p ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫⁻ x : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (bubble t b x ^ criticalExponent n) *
          f ((stereographic' n v).symm ((2 / t) • (x - b))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn₀)
  have hcov := e.toBasis.setLIntegral_riemannianVolume_image_of_injOn (I := 𝓡 n) rfl
    MeasurableSet.univ (injOn_stereographic'_symm_smul_sub v ht b)
    (fun x _ ↦ mdifferentiableAt_stereographic'_symm_smul_sub v t b x) f
  rwa [image_stereographic'_symm_smul_sub_univ v ht b,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (by simp)), Measure.restrict_univ,
    e.addHaar_eq_volume, funext (riemannianJacobian_stereographic'_symm_smul_sub hn v ht.le b)]
    at hcov

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
  rcases Nat.eq_zero_or_pos n with rfl | hn₀
  · exact ⟨fun _ ↦ .of_finite,
      fun _ ↦ (integrable_riemannianVolume_sphere_iff_stereographic' v f).mpr .of_finite⟩
  · let e := EuclideanSpace.basisFun (Fin n) ℝ
    have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn₀)
    have hcov := e.toBasis.integrableOn_riemannianVolume_image_iff_of_injOn (I := 𝓡 n) rfl
      MeasurableSet.univ (injOn_stereographic'_symm_smul_sub v ht b)
      (fun x _ ↦ mdifferentiableAt_stereographic'_symm_smul_sub v t b x) f
    rw [image_stereographic'_symm_smul_sub_univ v ht b, IntegrableOn,
      Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (by simp)), integrableOn_univ,
      e.addHaar_eq_volume] at hcov
    dsimp only [e, Function.comp_apply] at hcov
    simpa only [riemannianJacobian_stereographic'_symm_smul_sub hn v ht.le b] using hcov

/-- **Bochner integration on `Sⁿ` via a Yamabe bubble.** In positive dimension `n ≠ 2`, for
`t > 0`, the integral of any `f : Sⁿ → F` against the Riemannian volume is its rescaled
stereographic integral weighted by `U_{t,b} ^ pₙ`. Neither integrability of `f` nor completeness of
`F` is required. -/
theorem integral_riemannianVolume_sphere_eq_bubble_rpow_criticalExponent (hn₀ : 0 < n)
    (hn : n ≠ 2) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n))
    (f : sphere (0 : E) 1 → F) :
    ∫ p, f p ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) =
      ∫ x : EuclideanSpace ℝ (Fin n),
        (bubble t b x ^ criticalExponent n) •
          f ((stereographic' n v).symm ((2 / t) • (x - b))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn₀)
  have hcov := e.toBasis.setIntegral_riemannianVolume_image_of_injOn (I := 𝓡 n) rfl
    MeasurableSet.univ (injOn_stereographic'_symm_smul_sub v ht b)
    (fun x _ ↦ mdifferentiableAt_stereographic'_symm_smul_sub v t b x) f
  rw [image_stereographic'_symm_smul_sub_univ v ht b,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (by simp)), Measure.restrict_univ,
    e.addHaar_eq_volume] at hcov
  dsimp only [e, Function.comp_apply] at hcov
  simpa only [riemannianJacobian_stereographic'_symm_smul_sub hn v ht.le b] using hcov

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
  rw [integral_riemannianVolume_sphere_eq_bubble_rpow_criticalExponent hn₀ hn v ht b]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [smul_eq_mul, abs_mul, abs_of_pos (bubble_pos ht b x),
    Real.mul_rpow (bubble_pos ht b x).le (abs_nonneg _)]

end Measure

end TauCeti.Yamabe
