/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic

/-!
# The Riemann sphere is the round sphere

Let `E` be a three-dimensional real inner product space, `v` a point of its unit sphere `S²`, and
`ι : ℂ ≃ₗᵢ[ℝ] vᗮ` a linear isometry of `ℂ` onto the plane orthogonal to `v`, such as
`TauCeti.complexIsometryOrthogonalSpanSingleton`. Inverse stereographic projection from `v`, read
on that plane through `z ↦ 2 ι z`, sends `z ∈ ℂ` to

`σ(z) = (1 + |z|²)⁻¹ (2 ι z + (|z|² - 1) v)`,

and `∞` to `v`. This file shows that `σ` is a real-analytic diffeomorphism
`OnePoint.diffeomorphSphere v ι` from the Riemann sphere `OnePoint ℂ`, regarded as a real surface
through its holomorphic charts, onto the unit sphere `S²` with Mathlib's stereographic atlas. In
the inverted coordinate `w = 1 / z` it reads `w ↦ (1 + |w|²)⁻¹ (2 ι (conj w) + (1 - |w|²) v)`, which
is inverse stereographic projection from `-v`; this is how smoothness at `∞` is checked. The
underlying homeomorphism is Mathlib's `onePointHyperplaneHomeoUnitSphere`, transported along
`z ↦ 2 ι z` by `Homeomorph.onePointCongr`.

The main result compares the two natural metrics on the sphere. The round metric of `S²`
(`TauCeti.sphereRoundMetric`, induced from `E`) pulls back along `σ` to `4π` times the
Fubini–Study metric `g_FS(a, b) = ω_FS(a, i b)` of the Riemann sphere
(`OnePoint.inner_mfderiv_diffeomorphSphere`):

`⟪dσ a, dσ b⟫ = 4π ω_FS(a, i b)`.

In a chart coordinate `c` both sides are `4 (1 + |c|²)⁻² Re (conj a * b)`: on the round side this
is the conformal factor of inverse stereographic projection
(`TauCeti.inner_fderiv_stereoInvFunAux`), and on the Fubini–Study side it is `4π` times the density
`(π (1 + |c|²)²)⁻¹`. The factor `4π` is the area of the unit sphere, matching the normalization of
`ω_FS` to total area one (`OnePoint.integral_fubiniStudyDensity`); the comparison of areas is not
carried out here.

## Main definitions

* `OnePoint.diffeomorphSphere v ι`: the analytic diffeomorphism from the Riemann sphere onto the
  unit sphere of `E`, sending `∞` to `v`.

## Main results

* `OnePoint.diffeomorphSphere_infty`, `OnePoint.coe_diffeomorphSphere_coe`,
  `OnePoint.diffeomorphSphere_zero`: its values.
* `OnePoint.diffeomorphSphere_symm_self`, `OnePoint.diffeomorphSphere_symm_neg`,
  `OnePoint.diffeomorphSphere_symm_apply_of_ne`: the values of its inverse, stereographic
  projection from `v`.
* `OnePoint.inner_mfderiv_diffeomorphSphere`: the round metric pulls back to `4π` times the
  Fubini–Study metric.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (stereographic coordinates on the round sphere).
-/

public section

open Metric Module Set Filter ComplexConjugate TauCeti
open scoped Bundle InnerProductSpace Manifold Topology ContDiff TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : sphere (0 : E) 1) (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ)

/-! ### The two coordinate expressions -/

/-- Inverse stereographic projection from `v`, read in the affine coordinate:
`z ↦ σ⁻¹ (2 ι z)`. -/
private def affineExpr (z : ℂ) : E :=
  stereoInvFunAux (v : E) ((2 : ℝ) • (ι z : E))

/-- Inverse stereographic projection from `-v`, read in the inverted coordinate:
`w ↦ σ⁻¹ (2 ι (conj w))`. -/
private def invExpr (w : ℂ) : E :=
  stereoInvFunAux (-(v : E)) ((2 : ℝ) • (ι (conj w) : E))

private theorem contDiff_affineExpr : ContDiff ℝ ω (affineExpr v ι) :=
  contDiff_stereoInvFunAux.comp
    (contDiff_const.smul ((ℝ ∙ (v : E))ᗮ.subtypeL.contDiff.comp ι.contDiff))

private theorem contDiff_invExpr : ContDiff ℝ ω (invExpr v ι) :=
  contDiff_stereoInvFunAux.comp (contDiff_const.smul
    ((ℝ ∙ (v : E))ᗮ.subtypeL.contDiff.comp (ι.contDiff.comp Complex.conjCLE.contDiff)))

private theorem invExpr_zero : invExpr v ι 0 = v := by
  simp [invExpr]

/-- The two coordinate expressions agree under the chart transition `w = z⁻¹`. -/
private theorem invExpr_inv {z : ℂ} (hz : z ≠ 0) : invExpr v ι z⁻¹ = affineExpr v ι z := by
  have hv : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  -- `conj z⁻¹ = |z|⁻² z`, so both sides are combinations of `ι z` and `v`.
  have hconj : conj z⁻¹ = (‖z‖ ^ 2)⁻¹ • z := by
    rw [map_inv₀, Complex.inv_def]
    simp [Complex.normSq_eq_norm_sq, Complex.real_smul, mul_comm]
  have hι : (ι (conj z⁻¹) : E) = (‖z‖ ^ 2)⁻¹ • (ι z : E) := by
    rw [hconj, map_smul, Submodule.coe_smul]
  simp only [invExpr, affineExpr, stereoInvFunAux_apply, hι, norm_smul, Submodule.norm_coe,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_two, abs_inv, abs_pow, abs_norm]
  match_scalars <;> field_simp <;> ring

/-! ### The map and its inverse -/

variable [Fact (finrank ℝ E = 2 + 1)]

/-- The homeomorphism from the Riemann sphere to the unit sphere: Mathlib's inverse stereographic
projection `onePointHyperplaneHomeoUnitSphere` from `v`, read on `vᗮ` through `z ↦ 2 ι z`. -/
private def toSphere : OnePoint ℂ ≃ₜ sphere (0 : E) 1 :=
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 2
  ((Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).trans ι.toHomeomorph).onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere (norm_eq_of_mem_sphere v))

private theorem coe_toSphere_coe (z : ℂ) : (toSphere v ι z : E) = affineExpr v ι z := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 2
  rw [toSphere, Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, map_some,
    coe_onePointHyperplaneHomeoUnitSphere_coe, Homeomorph.trans_apply,
    Homeomorph.smulOfNeZero_apply, LinearIsometryEquiv.coe_toHomeomorph, map_smul,
    Submodule.coe_smul, affineExpr, stereoInvFunAux_apply]
  simp only [norm_smul, Submodule.norm_coe]

private theorem toSphere_infty : toSphere v ι ∞ = v := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 2
  ext
  simp [toSphere]

private theorem coe_toSphere_eq_invExpr {x : OnePoint ℂ} (hx : x ≠ ((0 : ℂ) : OnePoint ℂ)) :
    (toSphere v ι x : E) = invExpr v ι (invChart x) := by
  induction x using OnePoint.rec with
  | infty => rw [toSphere_infty, invChart_infty, invExpr_zero]
  | coe z =>
    have hz : z ≠ 0 := fun h ↦ hx (by rw [h])
    rw [coe_toSphere_coe, invChart_coe, invExpr_inv v ι hz]

private theorem toSphere_symm_self : (toSphere v ι).symm v = (∞ : OnePoint ℂ) :=
  (toSphere v ι).symm_apply_eq.2 (toSphere_infty v ι).symm

/-- Away from `v`, the inverse is stereographic projection from `v`, read through `ι` and rescaled
by `1 / 2`. -/
private theorem toSphere_symm_eq_stereoToFun {p : sphere (0 : E) 1} (hp : p ≠ v) :
    (toSphere v ι).symm p = ((ι.symm ((2 : ℝ)⁻¹ • stereoToFun (v : E) p) : ℂ) : OnePoint ℂ) := by
  refine (toSphere v ι).symm_apply_eq.2 (Subtype.ext ?_)
  rw [coe_toSphere_coe, affineExpr, LinearIsometryEquiv.apply_symm_apply, Submodule.coe_smul,
    smul_inv_smul₀ two_ne_zero]
  exact (congrArg Subtype.val
    (stereo_left_inv (norm_eq_of_mem_sphere v) fun h ↦ hp (Subtype.ext h))).symm

/-- In the affine coordinate, stereographic projection from `v` reads `(1 - ⟪v, p⟫)⁻¹ ι⁻¹ (P p)`,
where `P` is the orthogonal projection onto `vᗮ`. -/
private theorem toSphere_symm_eq_of_ne {p : sphere (0 : E) 1} (hp : p ≠ v) :
    (toSphere v ι).symm p = (((1 - ⟪(v : E), p⟫_ℝ)⁻¹ •
      ι.symm ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto p) : ℂ) : OnePoint ℂ) := by
  rw [toSphere_symm_eq_stereoToFun v ι hp, stereoToFun_apply, smul_smul,
    LinearIsometryEquiv.map_smul]
  congr 3
  simp only [innerSL_apply_apply]
  field_simp

/-- The inverted coordinate of stereographic projection from `v`:
`p ↦ (1 + ⟪v, p⟫)⁻¹ conj (ι⁻¹ (P p))`. -/
private def invCoord (x : E) : ℂ :=
  (1 + ⟪(v : E), x⟫_ℝ)⁻¹ • conj (ι.symm ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x))

/-- Near `v`, the inverse map is the inverse of the inverted chart applied to `invCoord`. -/
private theorem toSphere_symm_eq_invChart_symm {p : sphere (0 : E) 1} (hp : p ≠ -v) :
    (toSphere v ι).symm p = invChart.symm (invCoord v ι p) := by
  have hv : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  by_cases hpv : p = v
  · subst hpv
    simp [toSphere_symm_self, invCoord,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
  set t : ℝ := ⟪(v : E), p⟫_ℝ
  set y := (ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto p
  -- The Pythagorean relation `t² + ‖y‖² = 1` on the unit sphere.
  have split : (p : E) = t • (v : E) + (y : E) := by
    rw [← ((ℝ ∙ (v : E)).starProjection_add_starProjection_orthogonal p),
      Submodule.starProjection_unit_singleton ℝ hv p, Submodule.starProjection_apply]
  have hvy : ⟪(v : E), y⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2
  have pythag : t ^ 2 + ‖y‖ ^ 2 = 1 := by
    have hvy' : ⟪t • (v : E), (y : E)⟫_ℝ = 0 := by simp only [inner_smul_left, hvy, mul_zero]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy'
    rw [← split, norm_eq_of_mem_sphere p, norm_smul, hv, Real.norm_eq_abs] at h
    simp only [mul_one, abs_mul_abs_self, Submodule.norm_coe] at h
    linear_combination -h
  have ht1 : t ≠ 1 := fun h ↦ hpv
    (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one hv (norm_eq_of_mem_sphere p)).1 h).symm)
  have ht2 : 1 + t ≠ 0 := by
    intro h
    have h' : ⟪-(v : E), p⟫_ℝ = 1 := by rw [inner_neg_left]; linarith
    exact hp (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one (by rwa [norm_neg])
      (norm_eq_of_mem_sphere p)).1 h').symm)
  have ht3 : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht1)
  set α := ι.symm y
  have hα : ‖α‖ ^ 2 = ‖y‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]
  -- The two coordinates are mutually inverse: their product is `‖y‖² / (1 - t²) = 1`.
  have hprod : ((1 - t)⁻¹ • α) * invCoord v ι p = 1 := by
    have hmul : α * conj α = (‖α‖ : ℂ) ^ 2 := Complex.mul_conj' α
    have hreal : (1 - t)⁻¹ * (1 + t)⁻¹ * ‖α‖ ^ 2 = 1 := by
      rw [hα]
      field_simp
      linear_combination pythag
    simp only [invCoord, Complex.real_smul]
    calc ((1 - t)⁻¹ : ℝ) * α * (((1 + t)⁻¹ : ℝ) * conj α)
        = (((1 - t)⁻¹ * (1 + t)⁻¹ * ‖α‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          linear_combination ((1 - (t : ℂ))⁻¹ * (1 + (t : ℂ))⁻¹) * hmul
      _ = 1 := by rw [hreal, Complex.ofReal_one]
  have hne : invCoord v ι p ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  rw [toSphere_symm_eq_of_ne v ι hpv, invChart_symm_of_ne_zero hne,
    eq_inv_of_mul_eq_one_left hprod]

/-! ### Smoothness -/

/-- The inclusion `ℂ → OnePoint ℂ` is smooth for the underlying real structure. -/
private theorem contMDiff_coe_real : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ω ((↑) : ℂ → OnePoint ℂ) := by
  simpa using (contMDiff_coe (𝕜 := ℂ)).restrictScalars ℝ

/-- The inverse of the inverted chart is smooth for the underlying real structure. -/
private theorem contMDiff_invChart_symm_real :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ω (invChart.symm : ℂ → OnePoint ℂ) := by
  simpa using (contMDiff_invChart_symm (𝕜 := ℂ)).restrictScalars ℝ

private theorem contMDiff_coe_toSphere :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ω fun x : OnePoint ℂ ↦ (toSphere v ι x : E) := by
  intro x
  induction x using OnePoint.rec with
  | coe z =>
    refine ((contDiff_affineExpr v ι).comp_contMDiffAt
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)) (x := (z : OnePoint ℂ)))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (coe_ne_infty z)] with y hy
    induction y using OnePoint.rec with
    | infty => exact absurd rfl hy
    | coe w => simp [coe_toSphere_coe]
  | infty =>
    refine ((contDiff_invExpr v ι).comp_contMDiffAt
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)) (x := (∞ : OnePoint ℂ)))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (infty_ne_coe 0)] with y hy
    simp [coe_toSphere_eq_invExpr v ι hy]

private theorem contMDiff_toSphere : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ω (toSphere v ι) :=
  (contMDiff_coe_toSphere v ι).codRestrict_sphere fun x ↦ (toSphere v ι x).2

private theorem contMDiff_toSphere_symm : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ω (toSphere v ι).symm := by
  have hv : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  intro p
  by_cases hp : p = v
  · subst hp
    -- Near `v`, read the map through the inverse of the inverted chart.
    have hW : ContDiffAt ℝ ω (invCoord p ι) (p : E) := by
      have hden : (1 + ⟪(p : E), (p : E)⟫_ℝ) ≠ 0 := by
        rw [real_inner_self_eq_norm_sq, hv]
        norm_num
      exact ((contDiff_const.add (innerSL ℝ (p : E)).contDiff).contDiffAt.inv hden).smul
        (Complex.conjCLE.contDiff.comp (ι.symm.contDiff.comp
          (ℝ ∙ (p : E))ᗮ.orthogonalProjectionOnto.contDiff)).contDiffAt
    have hne : p ≠ -p := fun h ↦ ne_neg_of_mem_unit_sphere ℝ p h
    refine ((contMDiff_invChart_symm_real _).comp p (hW.comp_contMDiffAt
      contMDiff_coe_sphere.contMDiffAt)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hne] with q hq
    exact toSphere_symm_eq_invChart_symm p ι hq
  · -- Away from `v`, read the map through the inclusion `ℂ → OnePoint ℂ`.
    have hp' : innerSL ℝ (v : E) p ≠ 1 := by
      rw [innerSL_apply_apply]
      intro h
      exact hp (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one hv
        (norm_eq_of_mem_sphere p)).1 h).symm)
    have hS : ContDiffAt ℝ ω (stereoToFun (v : E)) (p : E) :=
      contDiffOn_stereoToFun.contDiffAt
        ((isOpen_ne_fun (innerSL ℝ (v : E)).continuous continuous_const).mem_nhds hp')
    have hZ : ContDiffAt ℝ ω (fun x : E ↦ ι.symm ((2 : ℝ)⁻¹ • stereoToFun (v : E) x)) (p : E) :=
      (ι.symm.contDiff.comp (contDiff_const_smul _)).contDiffAt.comp (p : E) hS
    refine ((contMDiff_coe_real _).comp p (hZ.comp_contMDiffAt
      contMDiff_coe_sphere.contMDiffAt)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hp] with q hq
    simp [toSphere_symm_eq_stereoToFun v ι (show q ≠ v from hq)]

/-! ### The diffeomorphism -/

/-- **The Riemann sphere is diffeomorphic to the unit sphere.** Inverse stereographic projection
from `v`, read on the plane `vᗮ` through `z ↦ 2 ι z`, is a real-analytic diffeomorphism from the
Riemann sphere `OnePoint ℂ` onto the unit sphere of the three-dimensional space `E`, sending `∞` to
`v` and `z` to `(1 + |z|²)⁻¹ (2 ι z + (|z|² - 1) v)`. Its underlying homeomorphism is
`onePointHyperplaneHomeoUnitSphere`, transported along `z ↦ 2 ι z` by `Homeomorph.onePointCongr`.
-/
def diffeomorphSphere : OnePoint ℂ ≃ₘ^ω⟮𝓘(ℝ, ℂ), 𝓡 2⟯ sphere (0 : E) 1 where
  toEquiv := (toSphere v ι).toEquiv
  contMDiff_toFun := contMDiff_toSphere v ι
  contMDiff_invFun := contMDiff_toSphere_symm v ι

@[simp]
theorem diffeomorphSphere_infty : diffeomorphSphere v ι ∞ = v :=
  toSphere_infty v ι

/-- A finite point `z` goes to `(1 + |z|²)⁻¹ (2 ι z + (|z|² - 1) v)`. -/
@[simp]
theorem coe_diffeomorphSphere_coe (z : ℂ) :
    (diffeomorphSphere v ι z : E) =
      (1 + ‖z‖ ^ 2)⁻¹ • ((2 : ℝ) • (ι z : E) + (‖z‖ ^ 2 - 1) • (v : E)) := by
  refine (coe_toSphere_coe v ι z).trans ?_
  simp only [affineExpr, stereoInvFunAux_apply, norm_smul, Submodule.norm_coe,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_two]
  match_scalars <;> field_simp <;> ring

/-- The origin goes to the antipode `-v` of the image of `∞`. -/
@[simp]
theorem diffeomorphSphere_zero : diffeomorphSphere v ι (0 : ℂ) = -v := by
  ext
  simp

@[simp]
theorem diffeomorphSphere_symm_self : (diffeomorphSphere v ι).symm v = (∞ : OnePoint ℂ) :=
  (diffeomorphSphere v ι).toEquiv.symm_apply_eq.2 (diffeomorphSphere_infty v ι).symm

@[simp]
theorem diffeomorphSphere_symm_neg : (diffeomorphSphere v ι).symm (-v) = ((0 : ℂ) : OnePoint ℂ) :=
  (diffeomorphSphere v ι).toEquiv.symm_apply_eq.2 (diffeomorphSphere_zero v ι).symm

/-- Away from `v`, the inverse is stereographic projection from `v`, read through `ι`:
`p ↦ (1 - ⟪v, p⟫)⁻¹ ι⁻¹ (P p)`, where `P` is the orthogonal projection onto `vᗮ`. -/
theorem diffeomorphSphere_symm_apply_of_ne {p : sphere (0 : E) 1} (hp : p ≠ v) :
    (diffeomorphSphere v ι).symm p = (((1 - ⟪(v : E), p⟫_ℝ)⁻¹ •
      ι.symm ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto p) : ℂ) : OnePoint ℂ) :=
  toSphere_symm_eq_of_ne v ι hp

/-! ### The round metric is `4π` times the Fubini–Study metric -/

/-- The differential of `σ`, read in `E`, is the derivative of its expression in the preferred
chart: `affineExpr` at a finite point and `invExpr` at `∞`. -/
private theorem mfderiv_coe_toSphere (x : OnePoint ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y ↦ (toSphere v ι y : E)) x =
      fderiv ℝ (x.elim (invExpr v ι) fun _ ↦ affineExpr v ι) (chartAt ℂ x x) := by
  -- The tangent spaces of `OnePoint ℂ` and of `E` are `ℂ` and `E`, so the derivative is the
  -- derivative of the map read in charts, with no cast between tangent and model spaces.
  rw [((contMDiff_coe_toSphere v ι x).mdifferentiableAt (by simp)).mfderiv_abuse]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ, writtenInExtChartAt,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp]
  congr 1
  induction x using OnePoint.rec with
  | coe z =>
    funext w
    simp [coe_toSphere_coe]
  | infty =>
    funext w
    by_cases hw : w = 0
    · simp [hw, toSphere_infty, invExpr_zero]
    · simp only [chartAt_infty, elim_infty, Function.comp_apply, invChart_symm_of_ne_zero hw]
      rw [coe_toSphere_eq_invExpr v ι (by simpa using inv_ne_zero hw), invChart_coe, inv_inv]

/-- The conformal factor of `σ` in a chart: for the chart coordinate `c` of `x`,
`⟪dσ a, dσ b⟫ = 4 (1 + |c|²)⁻² Re (conj a * b)`. -/
private theorem inner_mvfderiv_coe_toSphere (x : OnePoint ℂ) (a b : ℂ) :
    ⟪mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x a,
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x b⟫_ℝ =
      4 * ((1 + ‖chartAt ℂ x x‖ ^ 2) ^ 2)⁻¹ * (conj a * b).re := by
  have hv : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  have e (c : ℂ) : mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x c =
      fderiv ℝ (x.elim (invExpr v ι) fun _ ↦ affineExpr v ι) (chartAt ℂ x x) c :=
    -- `mvfderiv` differs from `mfderiv` only by `NormedSpace.fromTangentSpace`, the identity.
    DFunLike.congr_fun (mfderiv_coe_toSphere v ι x) c
  rw [e, e]
  clear e
  -- The conformal factor `(2 / (1 + |c|²))²` times `⟪a, b⟫ = Re (conj a * b)`.
  have h4 (r : ℝ) : (2 / (1 + r)) ^ 2 * ⟪a, b⟫_ℝ = 4 * ((1 + r) ^ 2)⁻¹ * (conj a * b).re := by
    rw [Complex.inner, mul_comm b, div_pow]
    ring
  induction x using OnePoint.rec with
  | coe z =>
    -- `affineExpr` is inverse stereographic projection from `v` read through `2 ι`.
    simp only [elim_some, chartAt_coe, affineChart_coe]
    exact (inner_fderiv_stereoInvFunAux_two_smul hv
      ((ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp ι.toLinearIsometry) (fun c ↦ (ι c).2) z a b).trans (h4 _)
  | infty =>
    -- `invExpr` is inverse stereographic projection from `-v` read through `2 ι ∘ conj`.
    simp only [elim_infty, chartAt_infty, invChart_infty]
    refine (inner_fderiv_stereoInvFunAux_two_smul (by rwa [norm_neg])
      ((ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp (ι.toLinearIsometry.comp Complex.conjLIE.toLinearIsometry))
      (fun c ↦ ?_) 0 a b).trans (h4 _)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_neg_left, neg_eq_zero,
      ← Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact (ι _).2

/-- **The round metric is `4π` times the Fubini–Study metric.** Along the diffeomorphism
`σ = diffeomorphSphere v ι`, the round metric of the unit sphere pulls back to `4π` times the
Fubini–Study metric `g_FS(a, b) = ω_FS(a, i b)` of the Riemann sphere: for tangent vectors `a`, `b`
at `x`, identified with `ℂ` through the preferred chart, `⟪dσ a, dσ b⟫ = 4π ω_FS(a, i b)`. -/
theorem inner_mfderiv_diffeomorphSphere (x : OnePoint ℂ) (a b : ℂ) :
    ⟪mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x a,
      mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x b⟫_ℝ =
      4 * Real.pi * SmoothBundleForm.eval₂ fubiniStudyForm x a (Complex.I * b) := by
  have hσ : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x :=
    (diffeomorphSphere v ι).mdifferentiable (by simp) x
  have hcoe : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)
      (diffeomorphSphere v ι x) := (contMDiff_coe_sphere _).mdifferentiableAt one_ne_zero
  have hd (c : ℂ) : mvfderiv (𝓡 2) ((↑) : sphere (0 : E) 1 → E) (diffeomorphSphere v ι x)
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x c) =
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x c :=
    -- The composite `(↑) ∘ diffeomorphSphere v ι` is `fun y ↦ (toSphere v ι y : E)` by definition.
    (mvfderiv_comp_apply x hcoe hσ c).symm
  rw [inner_tangentSpace_sphere, hd a, hd b, inner_mvfderiv_coe_toSphere]
  rw [eval₂_fubiniStudyForm_I_mul, fubiniStudyDensity_def]
  field_simp

end OnePoint
