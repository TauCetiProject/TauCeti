/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Orientation.Pullback
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
`ω_FS` to total area one (`OnePoint.integral_fubiniStudyDensity`).

The area forms compare in the same way, up to orientation. For an orientation `o` of `E`, the
outward-normal area form `(a, b) ↦ vol(u, a, b)` of `S²` (`Orientation.sphereVolumeForm`) pulls
back along `σ` to `-4π ε ω_FS`, where `ε = ±1` is the volume of the orthonormal frame
`(v, ι 1, ι i)` (`OnePoint.mpullback_diffeomorphSphere_sphereVolumeForm`). Its absolute value at
a point is `4π ρ(c)`, since `dσ` is conformal with the factor above and `dσ 1`, `dσ i` are
orthogonal to each other and to `σ x`. Its sign is constant, because the Riemann sphere is
connected, so the orientation pulled back along `σ` from the outward-normal orientation is the
complex orientation or its opposite. At the origin, where `σ 0 = -v` and `dσ a = 2 ι a`, the sign
is that of `vol(-v, ι 1, ι i) = -ε`.

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
* `OnePoint.mpullback_diffeomorphSphere_sphereVolumeForm`: the outward-normal area form pulls back
  to `∓4π` times the Fubini–Study form.

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
  have hvy : ⟪(v : E), y⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
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
  (contMDiff_coe_toSphere v ι).codRestrict_sphere fun x ↦ (toSphere v ι x).property

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
      ((ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp ι.toLinearIsometry) (fun c ↦ (ι c).property) z a b).trans
          (h4 _)
  | infty =>
    -- `invExpr` is inverse stereographic projection from `-v` read through `2 ι ∘ conj`.
    simp only [elim_infty, chartAt_infty, invChart_infty]
    refine (inner_fderiv_stereoInvFunAux_two_smul (by rwa [norm_neg])
      ((ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp (ι.toLinearIsometry.comp Complex.conjLIE.toLinearIsometry))
      (fun c ↦ ?_) 0 a b).trans (h4 _)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_neg_left, neg_eq_zero,
      ← Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact (ι _).property

/-- The differential of `σ = diffeomorphSphere v ι` read in `E` is the differential of `σ` followed
by that of the inclusion of the sphere into `E`. -/
private theorem mvfderiv_coe_toSphere_eq_comp (x : OnePoint ℂ) (c : TangentSpace 𝓘(ℝ, ℂ) x) :
    mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x c =
      mvfderiv (𝓡 2) ((↑) : sphere (0 : E) 1 → E) (diffeomorphSphere v ι x)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x c) :=
  -- The composite `(↑) ∘ diffeomorphSphere v ι` is `fun y ↦ (toSphere v ι y : E)` by definition.
  mvfderiv_comp_apply x ((contMDiff_coe_sphere _).mdifferentiableAt one_ne_zero)
    ((diffeomorphSphere v ι).mdifferentiable (by simp) x) c

/-- **The round metric is `4π` times the Fubini–Study metric.** Along the diffeomorphism
`σ = diffeomorphSphere v ι`, the round metric of the unit sphere pulls back to `4π` times the
Fubini–Study metric `g_FS(a, b) = ω_FS(a, i b)` of the Riemann sphere: for tangent vectors `a`, `b`
at `x`, identified with `ℂ` through the preferred chart, `⟪dσ a, dσ b⟫ = 4π ω_FS(a, i b)`. -/
theorem inner_mfderiv_diffeomorphSphere (x : OnePoint ℂ) (a b : ℂ) :
    ⟪mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x a,
      mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x b⟫_ℝ =
      4 * Real.pi * SmoothBundleForm.eval₂ fubiniStudyForm x a (Complex.I * b) := by
  rw [inner_tangentSpace_sphere, ← mvfderiv_coe_toSphere_eq_comp v ι x a,
    ← mvfderiv_coe_toSphere_eq_comp v ι x b, inner_mvfderiv_coe_toSphere]
  rw [eval₂_fubiniStudyForm_I_mul, fubiniStudyDensity_def]
  field_simp

/-! ### The round area form is `±4π` times the Fubini–Study form -/

section Area

variable (o : Orientation ℝ E (Fin 3))

/-- The pulled-back area form, read in `E`: `vol(σ x, dσ a, dσ b)`. -/
private theorem mpullback_sphereVolumeForm_apply (x : OnePoint ℂ) (a b : TangentSpace 𝓘(ℝ, ℂ) x) :
    mpullback 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) o.sphereVolumeForm.val x ![a, b] =
      o.volumeForm ![(toSphere v ι x : E),
        mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x a,
        mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x b] := by
  rw [mpullback_apply_pair, Orientation.sphereVolumeForm_apply]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact (mvfderiv_coe_toSphere_eq_comp v ι x a).symm
  · exact (mvfderiv_coe_toSphere_eq_comp v ι x b).symm

/-- The differential of `σ` read in `E` takes values orthogonal to the point `σ x`. -/
private theorem inner_coe_toSphere_mvfderiv (x : OnePoint ℂ) (c : TangentSpace 𝓘(ℝ, ℂ) x) :
    ⟪(toSphere v ι x : E), mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x c⟫_ℝ = 0 := by
  rw [mvfderiv_coe_toSphere_eq_comp]
  exact inner_coe_mvfderiv_subtypeVal_sphere (diffeomorphSphere v ι x) _

/-- The area of the image of the square spanned by `1` and `i`:
`|vol(σ x, dσ 1, dσ i)| = 4 (1 + |c|²)⁻²` for the chart coordinate `c` of `x`. -/
private theorem abs_volumeForm_mvfderiv_coe_toSphere (x : OnePoint ℂ) :
    |o.volumeForm ![(toSphere v ι x : E),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x (1 : ℂ),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x Complex.I]| =
      4 * ((1 + ‖chartAt ℂ x x‖ ^ 2) ^ 2)⁻¹ := by
  set D := mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x
  set r := 4 * ((1 + ‖chartAt ℂ x x‖ ^ 2) ^ 2)⁻¹
  have hr : 0 ≤ r := by positivity
  have hD1 : ⟪D (1 : ℂ), D Complex.I⟫_ℝ = 0 := by
    rw [inner_mvfderiv_coe_toSphere]
    simp
  have hn (c : ℂ) (hc : ‖c‖ = 1) : ‖D c‖ ^ 2 = r := by
    rw [← real_inner_self_eq_norm_sq, inner_mvfderiv_coe_toSphere, Complex.conj_mul',
      ← Complex.ofReal_pow, Complex.ofReal_re, hc, one_pow, mul_one]
  have horth : Pairwise fun i j ↦
      ⟪![(toSphere v ι x : E), D (1 : ℂ), D Complex.I] i,
        ![(toSphere v ι x : E), D (1 : ℂ), D Complex.I] j⟫_ℝ = 0 := by
    have h0 (c : ℂ) : ⟪(toSphere v ι x : E), D c⟫_ℝ = 0 := inner_coe_toSphere_mvfderiv v ι x c
    have h0' (c : ℂ) : ⟪D c, (toSphere v ι x : E)⟫_ℝ = 0 := by rw [real_inner_comm]; exact h0 c
    have hD1' : ⟪D Complex.I, D (1 : ℂ)⟫_ℝ = 0 := by rw [real_inner_comm]; exact hD1
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  rw [o.abs_volumeForm_apply_of_pairwise_orthogonal horth, Fin.prod_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, norm_eq_of_mem_sphere, one_mul]
  have hprod : (‖D (1 : ℂ)‖ * ‖D Complex.I‖) ^ 2 = r ^ 2 := by
    rw [mul_pow, hn (1 : ℂ) norm_one, hn Complex.I Complex.norm_I, sq]
  exact (sq_eq_sq₀ (by positivity) hr).1 hprod

/-- At the origin, the differential of `σ` read in `E` is `a ↦ 2 ι a`. -/
private theorem mvfderiv_coe_toSphere_zero (a : ℂ) :
    mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) ((0 : ℂ) : OnePoint ℂ) a =
      (2 : ℝ) • (ι a : E) := by
  set L : ℂ →L[ℝ] E :=
    (2 : ℝ) • ((ℝ ∙ (v : E))ᗮ.subtypeL.comp ι.toContinuousLinearEquiv.toContinuousLinearMap)
  have hS := ((contDiff_stereoInvFunAux (v := (v : E)) (m := 1)).differentiable one_ne_zero
    (L 0)).hasFDerivAt.comp (0 : ℂ) L.hasFDerivAt
  -- `affineExpr v ι` is the composite of `L` and inverse stereographic projection from `v`.
  have he : affineExpr v ι = stereoInvFunAux (v : E) ∘ L := rfl
  refine (DFunLike.congr_fun (mfderiv_coe_toSphere v ι _) a).trans ?_
  have hval : (fderiv ℝ (stereoInvFunAux (v : E)) (L 0)).comp L a = (2 : ℝ) • (ι a : E) := by
    rw [ContinuousLinearMap.comp_apply, map_zero, fderiv_stereoInvFunAux_apply]
    simp [L]
  simp only [elim_some, chartAt_coe, affineChart_coe]
  rw [he, hS.fderiv]
  exact hval

/-- The frame `(v, ι 1, ι i)` of `E` is orthonormal, so its volume is `±1`. -/
private theorem abs_volumeForm_frame :
    |o.volumeForm ![(v : E), (ι 1 : E), (ι Complex.I : E)]| = 1 := by
  have hv (c : ℂ) : ⟪(v : E), (ι c : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (ι c).property
  have hv' (c : ℂ) : ⟪(ι c : E), (v : E)⟫_ℝ = 0 := by rw [real_inner_comm]; exact hv c
  have hι (c d : ℂ) : ⟪(ι c : E), (ι d : E)⟫_ℝ = ⟪c, d⟫_ℝ := by
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have horth : Pairwise fun i j ↦ ⟪![(v : E), (ι 1 : E), (ι Complex.I : E)] i,
      ![(v : E), (ι 1 : E), (ι Complex.I : E)] j⟫_ℝ = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Complex.inner]
  rw [o.abs_volumeForm_apply_of_pairwise_orthogonal horth, Fin.prod_univ_three]
  simp [norm_eq_of_mem_sphere, Submodule.norm_coe]

/-- At the origin, `vol(σ 0, dσ 1, dσ i) = vol(-v, 2 ι 1, 2 ι i) = -4 vol(v, ι 1, ι i)`. -/
private theorem volumeForm_mvfderiv_coe_toSphere_zero :
    o.volumeForm ![(toSphere v ι ((0 : ℂ) : OnePoint ℂ) : E),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) ((0 : ℂ) : OnePoint ℂ) (1 : ℂ),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) ((0 : ℂ) : OnePoint ℂ) Complex.I] =
      -4 * o.volumeForm ![(v : E), (ι 1 : E), (ι Complex.I : E)] := by
  have h0 : (toSphere v ι ((0 : ℂ) : OnePoint ℂ) : E) = -(v : E) :=
    congrArg Subtype.val (diffeomorphSphere_zero v ι)
  have hcons : ![(toSphere v ι ((0 : ℂ) : OnePoint ℂ) : E),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) ((0 : ℂ) : OnePoint ℂ) (1 : ℂ),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) ((0 : ℂ) : OnePoint ℂ) Complex.I] =
      fun i ↦ ![(-1 : ℝ), 2, 2] i • ![(v : E), (ι 1 : E), (ι Complex.I : E)] i := by
    funext i
    fin_cases i <;> simp [h0, mvfderiv_coe_toSphere_zero]
  rw [hcons, AlternatingMap.map_smul_univ, Fin.prod_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, smul_eq_mul]
  ring

/-- At a point `y`, `vol(σ y, dσ 1, dσ i)` is positive exactly when the orientation of the Riemann
sphere pulled back along `σ` from the outward-normal orientation is that of the basis `(1, i)`
at `y`. -/
private theorem volumeForm_mvfderiv_coe_toSphere_pos_iff_orientationAt
    (hf : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) 1 (diffeomorphSphere v ι))
    (hdf : ∀ y, (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) y).IsInvertible)
    (hcard : Fintype.card (Fin 2) = finrank ℝ ℂ) (y : OnePoint ℂ) :
    0 < o.volumeForm ![(toSphere v ι y : E),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) y (1 : ℂ),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) y Complex.I] ↔
      (o.sphereOrientation.pullback hf hdf hcard).orientationAt y = Complex.orientation := by
  set D := (diffeomorphSphere v ι).mfderivToContinuousLinearEquiv (by simp) y
  have hmap := Manifold.Orientation.map_orientationAt_pullback o.sphereOrientation hf hdf hcard
    y D ((diffeomorphSphere v ι).mfderivToContinuousLinearEquiv_coe (by simp))
  -- The basis `(1, i)` of the tangent space at `y`, which is `ℂ`.
  let b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) y) := Complex.basisOneI
  have h1 := (Orientation.map (Fin 2) D.toLinearEquiv).injective.eq_iff
    (a := (o.sphereOrientation.pullback hf hdf hcard).orientationAt y) (b := b.orientation)
  rw [hmap, ← Module.Basis.orientation_map, eq_comm,
    o.orientation_eq_orientationAt_sphereOrientation_iff] at h1
  refine Iff.trans (iff_of_eq (congrArg (fun w ↦ 0 < o.volumeForm w) (funext fun i ↦ ?_))) h1
  have hb (c : TangentSpace 𝓘(ℝ, ℂ) y) : mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) y c =
      mvfderiv (𝓡 2) ((↑) : sphere (0 : E) 1 → E) (diffeomorphSphere v ι y) (D c) :=
    (mvfderiv_coe_toSphere_eq_comp v ι y c).trans (congrArg _ (DFunLike.congr_fun
      ((diffeomorphSphere v ι).mfderivToContinuousLinearEquiv_coe (by simp)).symm c))
  fin_cases i
  · rfl
  · exact (hb _).trans (congrArg _ (congrArg D (congrFun Complex.coe_basisOneI 0).symm))
  · exact (hb _).trans (congrArg _ (congrArg D (congrFun Complex.coe_basisOneI 1).symm))

/-- The sign of `vol(σ x, dσ 1, dσ i)` is the same at every point: since the Riemann sphere is
connected, the orientation pulled back along `σ` from the outward-normal orientation is the
complex orientation or its opposite. -/
private theorem volumeForm_mvfderiv_coe_toSphere_pos_iff (x : OnePoint ℂ) :
    0 < o.volumeForm ![(toSphere v ι x : E),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x (1 : ℂ),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x Complex.I] ↔
    0 < o.volumeForm ![(toSphere v ι ((0 : ℂ) : OnePoint ℂ) : E),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) ((0 : ℂ) : OnePoint ℂ) (1 : ℂ),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) ((0 : ℂ) : OnePoint ℂ) Complex.I] := by
  have hf : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) 1 (diffeomorphSphere v ι) :=
    (diffeomorphSphere v ι).contMDiff.of_le (by simp)
  have hdf (y : OnePoint ℂ) : (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) y).IsInvertible :=
    (diffeomorphSphere v ι).isInvertible_mfderiv (by simp)
  have hcard : Fintype.card (Fin 2) = finrank ℝ ℂ := by simp
  have h2 : 2 * finrank ℂ ℂ = 2 :=
    (finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex
  rw [volumeForm_mvfderiv_coe_toSphere_pos_iff_orientationAt v ι o hf hdf hcard,
    volumeForm_mvfderiv_coe_toSphere_pos_iff_orientationAt v ι o hf hdf hcard]
  rcases (o.sphereOrientation.pullback hf hdf hcard).eq_or_eq_neg
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex (finCongr h2)) with h | h <;>
    simp only [h, orientationAt_reindex_complexManifoldOrientation_complex,
      Manifold.Orientation.orientationAt_neg]
  -- Both sides now state the same equation of orientations of `ℂ`, read as the tangent spaces at
  -- `x` and at `0`.
  all_goals exact Iff.rfl

/-- On the basis `(1, i)`, `vol(σ x, dσ 1, dσ i) = -4π vol(v, ι 1, ι i) ρ(c)` for the chart
coordinate `c` of `x`. -/
private theorem volumeForm_mvfderiv_coe_toSphere (x : OnePoint ℂ) :
    o.volumeForm ![(toSphere v ι x : E),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x (1 : ℂ),
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (toSphere v ι y : E)) x Complex.I] =
      -(4 * Real.pi * o.volumeForm ![(v : E), (ι 1 : E), (ι Complex.I : E)]) *
        fubiniStudyDensity (chartAt ℂ x x) := by
  have habs := abs_volumeForm_mvfderiv_coe_toSphere v ι o x
  have hpos := volumeForm_mvfderiv_coe_toSphere_pos_iff v ι o x
  rw [volumeForm_mvfderiv_coe_toSphere_zero] at hpos
  have hρ : 4 * ((1 + ‖chartAt ℂ x x‖ ^ 2) ^ 2)⁻¹ =
      4 * Real.pi * fubiniStudyDensity (chartAt ℂ x x) := by
    rw [fubiniStudyDensity_def]
    field_simp
  -- The frame `(v, ι 1, ι i)` has volume `±1`, and the sign at `0` decides the sign everywhere.
  rcases (abs_eq zero_le_one).1 (abs_volumeForm_frame v ι o) with hc | hc <;> rw [hc] at hpos ⊢
  · rw [abs_of_nonpos (not_lt.1 (fun h ↦ by linarith [hpos.1 h])), hρ] at habs
    linarith
  · rw [abs_of_pos (hpos.2 (by norm_num)), hρ] at habs
    linarith

/-- **The round area form is `∓4π` times the Fubini–Study form.** Along the diffeomorphism
`σ = diffeomorphSphere v ι`, the outward-normal area form `(a, b) ↦ vol(u, a, b)` of the unit
sphere of `E`, for an orientation `o` of `E`, pulls back to `-4π ε ω_FS`, where `ε = ±1` is the
volume of the orthonormal frame `(v, ι 1, ι i)`. In particular the pullback is a positive
multiple of `ω_FS` exactly when `(-v, ι 1, ι i)` is a positive basis of `E`, and its absolute value
is the factor `4π` of the comparison `inner_mfderiv_diffeomorphSphere` of metrics. -/
theorem mpullback_diffeomorphSphere_sphereVolumeForm :
    mpullback 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) o.sphereVolumeForm.val =
      (-(4 * Real.pi * o.volumeForm ![(v : E), (ι 1 : E), (ι Complex.I : E)])) •
        fubiniStudyForm.val := by
  funext x
  rw [← sub_eq_zero]
  set F := mpullback 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) o.sphereVolumeForm.val x -
    (-(4 * Real.pi * o.volumeForm ![(v : E), (ι 1 : E), (ι Complex.I : E)])) •
      fubiniStudyForm.val x
  -- Two top-degree alternating maps on `ℂ` agree once they agree on the basis `(1, i)`.
  have h1 := mpullback_sphereVolumeForm_apply v ι o x (1 : ℂ) Complex.I
  have h2 := (SmoothBundleForm.eval₂_apply fubiniStudyForm x (1 : ℂ) Complex.I).symm.trans
    (eval₂_fubiniStudyForm x 1 Complex.I)
  simp only [map_one, one_mul, Complex.I_im, mul_one] at h2
  have hF : F ![(1 : ℂ), Complex.I] = 0 := by
    rw [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, h1, h2,
      volumeForm_mvfderiv_coe_toSphere, smul_eq_mul, sub_self]
  refine ContinuousAlternatingMap.toAlternatingMap_injective
    ((AlternatingMap.map_basis_eq_zero_iff
      (Complex.basisOneI : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) x)) _).1 ?_)
  exact (congrArg F Complex.coe_basisOneI).trans hF

end Area

end OnePoint
