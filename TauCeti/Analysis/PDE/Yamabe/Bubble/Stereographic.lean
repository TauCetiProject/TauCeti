/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Volume
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import TauCeti.MeasureTheory.Integral.Bochner.Affine
import TauCeti.MeasureTheory.Integral.Dilation
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
    have hmf : mfderiv (𝓡 n) (𝓡 n) ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x =
        (2 / t) • mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b)) := by
      rw [mfderiv_comp x hsymm hA.mdifferentiableAt, hA.mfderiv]
      ext d
      exact (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b))).map_smul
        (2 / t) d
    let J : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        TangentSpace (𝓡 n) ((stereographic' n v).symm ((2 / t) • (x - b))) :=
      (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm ((2 / t) • (x - b))).toLinearMap
    have hJ : (mfderiv (𝓡 n) (𝓡 n)
          ((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) x).toLinearMap =
        (2 / t) • J := by
      ext d
      rw [ContinuousLinearMap.coe_coe, hmf]
      rfl
    rw [riemannianJacobian_eq_normDet e, hJ, LinearMap.normDet_smul, finrank_euclideanSpace_fin,
      Real.norm_of_nonneg (by positivity),
      ← riemannianJacobian_eq_normDet e (stereographic' n v).symm ((2 / t) • (x - b)),
      riemannianJacobian_stereographic'_symm]
    exact mul_stereographic_density_eq_bubble_rpow hn ht b x

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
  have haff : (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 / t) • (x - b)) =
      fun x ↦ -((2 / t) • b) + A x := by
    funext x
    simp [A, sub_eq_neg_add]
  have hdet : |(LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))⁻¹| =
      ((2 / t) ^ n)⁻¹ := by
    have hA : (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
        (2 / t) • LinearMap.id := by
      ext x
      simp [A]
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
    have hx : (2 / t) • (x - b) = y := by
      rw [congrFun haff x]
      dsimp only [x]
      rw [A.apply_symm_apply]
      abel
    have hmul := mul_stereographic_density_eq_bubble_rpow hn ht b x
    rw [hx] at hmul
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
  rw [lintegral_riemannianVolume_sphere_eq_stereographic' hn₀ v f]
  have hscale := Measure.lintegral_comp_smul volume
    (fun y : EuclideanSpace ℝ (Fin n) ↦
      ENNReal.ofReal ((4 / (‖y‖ ^ 2 + 4)) ^ n) * f ((stereographic' n v).symm y))
    (show (2 / t) ≠ 0 by positivity)
  rw [finrank_euclideanSpace_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity) n)),
    ← lintegral_sub_right_eq_self _ b] at hscale
  have hmul := congrArg (ENNReal.ofReal ((2 / t) ^ n) * ·) hscale
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (pow_ne_zero n (by positivity)), ENNReal.ofReal_one, one_mul] at hmul
  rw [← hmul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x ↦ ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_stereographic_density_eq_bubble_rpow hn ht b x]

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
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (2 / t) (by positivity))
  have himg : (fun x : EuclideanSpace ℝ (Fin n) ↦ -((2 / t) • b) + A x) '' univ = univ := by
    refine eq_univ_of_forall fun y ↦ ⟨A.symm (y + (2 / t) • b), mem_univ _, ?_⟩
    dsimp only
    rw [A.apply_symm_apply]
    abel
  have haff := A.integrableOn_image_affine_iff (-((2 / t) • b))
    (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((4 / (‖y‖ ^ 2 + 4)) ^ n) • f ((stereographic' n v).symm y)) univ volume
  rw [himg, integrableOn_univ, integrableOn_univ] at haff
  rw [haff, ← integrable_smul_iff (c := (2 / t) ^ n) (pow_ne_zero n (by positivity))]
  refine integrable_congr (ae_of_all _ fun x ↦ ?_)
  have hsub : -((2 / t) • b) + A x = (2 / t) • (x - b) := by
    simp [A, sub_eq_neg_add]
  rw [Pi.smul_apply, hsub, smul_smul, mul_stereographic_density_eq_bubble_rpow hn ht b x]

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
  rw [integral_riemannianVolume_sphere_eq_stereographic' hn₀ v f]
  have hscale := Measure.integral_comp_smul_of_nonneg volume
    (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((4 / (‖y‖ ^ 2 + 4)) ^ n) • f ((stereographic' n v).symm y))
    (2 / t) (hR := by positivity)
  rw [finrank_euclideanSpace_fin, ← integral_sub_right_eq_self _ b] at hscale
  have hmul := congrArg ((2 / t) ^ n • ·) hscale
  rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero n (by positivity)), one_smul,
    ← integral_smul] at hmul
  rw [← hmul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [smul_smul, mul_stereographic_density_eq_bubble_rpow hn ht b x]

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
