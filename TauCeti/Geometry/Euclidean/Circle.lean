/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import TauCeti.Geometry.Sphere.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Planar circles and arclength parametrizations

This file provides two parametrizations of circles in Euclidean planes:

* `TauCeti.circleSphereHomeomorph` identifies `AddCircle (2 * π)` with the unit sphere in the
  Euclidean plane through cosine and sine. It is complex exponentiation followed by the inverse
  of `TauCeti.EuclideanSpace.sphereHomeomorphCircle`, using real orthonormal coordinates.
  The inner product of two such vectors is the cosine of their angle difference, allowing
  circular kernels to be read as kernels on the planar sphere.
* `Orientation.circleCurve` parametrizes the circle of center `c`, starting radial vector `e`, and
  radius `R` in any oriented two-dimensional real inner product space `E` by
  `s ↦ c + R • (cos (s / R) • e + sin (s / R) • J e) = c + R • o.rotation (s / R) e` using
  Mathlib's `Orientation.rotation` and `Orientation.rightAngleRotation`. It records periodicity,
  sphere membership, derivatives, chord-vector formulas (`Orientation.circleCurve_add_two_mul_sub`),
  the tangent-chord area-form identity (`Orientation.areaForm_deriv_circleCurve_sub`), injectivity
  on `[0, 2 π R)`, and the characterization of double normals as diameters
  (`Orientation.inner_circleCurve_sub_deriv_eq_zero_iff`).

It also records the derivative of a rotating curve `s ↦ o.rotation (θ s) (c s)`
(`Orientation.hasDerivAt_rotation`).
-/

public section

noncomputable section

open Metric Set Real
open scoped InnerProductSpace

namespace TauCeti

/-- Cosine and sine identify the additive circle with the unit sphere in the Euclidean plane. -/
def circleSphereHomeomorph : AddCircle (2 * π) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (AddCircle.homeomorphCircle' : AddCircle (2 * π) ≃ₜ sphere (0 : ℂ) 1).trans
    EuclideanSpace.sphereHomeomorphCircle.symm

/-- The planar parametrization is complex exponentiation followed by real orthonormal
coordinates. -/
theorem coe_circleSphereHomeomorph (t : AddCircle (2 * π)) :
    (circleSphereHomeomorph t : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (Real.Angle.toCircle t) :=
  EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply (Real.Angle.toCircle t)

/-- At a real angle, the planar sphere parametrization has coordinates cosine and sine. -/
@[simp]
theorem circleSphereHomeomorph_coe (t : ℝ) :
    (circleSphereHomeomorph t : EuclideanSpace ℝ (Fin 2)) =
      WithLp.toLp 2 ![cos t, sin t] := by
  have ht : ((Real.Angle.toCircle (t : AddCircle (2 * π))) : ℂ) =
      (cos t : ℂ) + sin t * Complex.I := by
    simpa only [Real.Angle.cos_coe, Real.Angle.sin_coe] using!
      Real.Angle.coe_toCircle (t : Real.Angle)
  rw [coe_circleSphereHomeomorph, WithLp.ext_iff, Complex.orthonormalBasisOneI_repr_apply, ht]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The inner product of the two parametrized directions is the cosine of their angle difference. -/
@[simp]
theorem inner_circleSphereHomeomorph (a b : AddCircle (2 * π)) :
    ⟪(circleSphereHomeomorph a : EuclideanSpace ℝ (Fin 2)),
      (circleSphereHomeomorph b : EuclideanSpace ℝ (Fin 2))⟫_ℝ =
      cos_periodic.lift (b - a) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  induction b using QuotientAddGroup.induction_on with | H b =>
  rw [← AddCircle.coe_sub, Function.Periodic.lift_coe]
  simp [EuclideanSpace.inner_eq_star_dotProduct, cos_sub, mul_comm]

end TauCeti

/-! ### Arclength parametrization of circles in an oriented Euclidean plane -/

namespace Orientation

open Function Filter Topology Module
open scoped RealInnerProductSpace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

/-- The curve `s ↦ c + R • (cos (s / R) • e + sin (s / R) • J e)` in the plane `E` oriented by `o`.
For a unit vector `e` and `R > 0`, this is the positively oriented arclength parametrization of the
circle of center `c` and radius `R` starting at `c + R • e`. -/
def circleCurve (o : Orientation ℝ E (Fin 2)) (c e : E) (R s : ℝ) : E :=
  c + R • (Real.cos (s / R) • e + Real.sin (s / R) • o.rightAngleRotation e)

theorem circleCurve_def (o : Orientation ℝ E (Fin 2)) (c e : E) (R s : ℝ) :
    o.circleCurve c e R s =
      c + R • (Real.cos (s / R) • e + Real.sin (s / R) • o.rightAngleRotation e) :=
  (rfl)

/-- `o.circleCurve` rotates the starting radial vector `e` by the angle `s / R` around `c` and
scales by `R`. -/
theorem circleCurve_eq_add_smul_rotation (o : Orientation ℝ E (Fin 2)) (c e : E) (R s : ℝ) :
    o.circleCurve c e R s = c + R • o.rotation (s / R : ℝ) e := by
  rw [circleCurve_def, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]

@[simp]
theorem circleCurve_zero (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) :
    o.circleCurve c e R 0 = c + R • e := by
  simp [circleCurve]

/-- Quarter a turn `π R / 2` from `0` along `o.circleCurve c e R` lands at `c + R • J e`. -/
theorem circleCurve_pi_mul_div_two (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) :
    o.circleCurve c e R (Real.pi * R / 2) = c + R • o.rightAngleRotation e := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [circleCurve]
  · have hdiv : (Real.pi * R / 2) / R = Real.pi / 2 := by field_simp
    simp [circleCurve_def, hdiv]

/-- Half a turn `π R` along `o.circleCurve c e R` negates the radial vector from `c`. -/
theorem circleCurve_add_pi_mul_sub_center (o : Orientation ℝ E (Fin 2)) (c e : E) (R s : ℝ) :
    o.circleCurve c e R (s + Real.pi * R) - c = -(o.circleCurve c e R s - c) := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [circleCurve]
  · have hdiv : (s + Real.pi * R) / R = s / R + Real.pi := by field_simp
    simp only [circleCurve_def, hdiv, Real.cos_add_pi, Real.sin_add_pi, add_sub_cancel_left,
      neg_smul, ← neg_add, smul_neg]

/-- Half a turn `π R` from `0` along `o.circleCurve c e R` lands at `c - R • e`. -/
theorem circleCurve_pi_mul (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) :
    o.circleCurve c e R (Real.pi * R) = c - R • e := by
  have h := o.circleCurve_add_pi_mul_sub_center c e R 0
  rw [zero_add, circleCurve_zero, add_sub_cancel_left, sub_eq_iff_eq_add', ← sub_eq_add_neg] at h
  exact h

/-- For any vector `e` and radius `R`, `o.circleCurve c e R` lies on `Metric.sphere c ‖R • e‖`. -/
theorem circleCurve_mem_sphere_norm_smul (o : Orientation ℝ E (Fin 2)) (c e : E) (R s : ℝ) :
    o.circleCurve c e R s ∈ Metric.sphere c ‖R • e‖ := by
  rw [Metric.mem_sphere, dist_eq_norm, circleCurve_eq_add_smul_rotation, add_sub_cancel_left,
    norm_smul, LinearIsometryEquiv.norm_map, ← norm_smul]

/-- For a unit vector `e` and `R ≥ 0`, `o.circleCurve c e R` lies on `Metric.sphere c R`. -/
theorem circleCurve_mem_sphere (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 ≤ R) (s : ℝ) :
    o.circleCurve c e R s ∈ Metric.sphere c R := by
  simpa [norm_smul, he, Real.norm_of_nonneg hR] using o.circleCurve_mem_sphere_norm_smul c e R s

/-- `o.circleCurve c e R` has period `2 π R`. -/
theorem periodic_circleCurve (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) :
    Periodic (o.circleCurve c e R) (2 * Real.pi * R) := fun s ↦ by
  rcases eq_or_ne R 0 with rfl | hR
  · simp
  · have hdiv : (s + 2 * Real.pi * R) / R = s / R + 2 * Real.pi := by field_simp
    simp only [circleCurve_def, hdiv, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **Derivative of a rotating curve.** If `θ` and `c` have derivatives `θ'` and `c'` at `t`, then
`s ↦ o.rotation (θ s) (c s)` has derivative `θ' J (o.rotation (θ t) (c t)) + o.rotation (θ t) c'`
at `t`, where `J` is the quarter turn `o.rightAngleRotation`. -/
theorem hasDerivAt_rotation (o : Orientation ℝ E (Fin 2)) {θ : ℝ → ℝ} {c : ℝ → E} {θ' t : ℝ}
    {c' : E} (hθ : HasDerivAt θ θ' t) (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s ↦ o.rotation (θ s) (c s))
      (θ' • o.rightAngleRotation (o.rotation (θ t) (c t)) + o.rotation (θ t) c') t := by
  have hJ : HasDerivAt (fun s ↦ o.rightAngleRotation (c s)) (o.rightAngleRotation c') t :=
    (o.rightAngleRotation : E →L[ℝ] E).hasFDerivAt.comp_hasDerivAt t hc
  convert (hθ.cos.smul hc).add (hθ.sin.smul hJ) using 1
  · ext s
    simp [o.rotation_apply]
  · simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe, map_add, map_smul,
      rightAngleRotation_rightAngleRotation]
    module

/-- Derivative of `o.circleCurve c e R` when `R ≠ 0`. -/
theorem hasDerivAt_circleCurve (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ} (hR : R ≠ 0)
    (s : ℝ) :
    HasDerivAt (o.circleCurve c e R)
      (-Real.sin (s / R) • e + Real.cos (s / R) • o.rightAngleRotation e) s := by
  have hdiv : HasDerivAt (fun t : ℝ ↦ t / R) R⁻¹ s := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id s).mul_const R⁻¹
  have hsum := (((hdiv.cos.smul_const e).add
    (hdiv.sin.smul_const (o.rightAngleRotation e))).const_smul R).const_add c
  refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv ?_
  rw [smul_add, smul_smul, smul_smul]
  have h1 : R * (-Real.sin (s / R) * R⁻¹) = -Real.sin (s / R) := by field_simp
  have h2 : R * (Real.cos (s / R) * R⁻¹) = Real.cos (s / R) := by field_simp
  rw [h1, h2]

theorem deriv_circleCurve (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    deriv (o.circleCurve c e R) s =
      -Real.sin (s / R) • e + Real.cos (s / R) • o.rightAngleRotation e :=
  (o.hasDerivAt_circleCurve c e hR s).deriv

/-- When `R ≠ 0`, the velocity vector of `o.circleCurve c e R` at `0` is `J e`. -/
theorem deriv_circleCurve_zero (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ} (hR : R ≠ 0) :
    deriv (o.circleCurve c e R) 0 = o.rightAngleRotation e := by
  simp [o.deriv_circleCurve c e hR 0]

/-- When `R ≠ 0`, the tangent vector of `o.circleCurve` at `s` is the quarter turn of the rotated
radial vector `o.rotation (s / R) e`. -/
theorem deriv_circleCurve_eq_rightAngleRotation_rotation (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    deriv (o.circleCurve c e R) s = o.rightAngleRotation (o.rotation (s / R : ℝ) e) := by
  rw [o.deriv_circleCurve c e hR s, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
    map_add, map_smul, map_smul, o.rightAngleRotation_rightAngleRotation, smul_neg, neg_smul]
  abel

/-- The velocity vector of `o.circleCurve` is `R⁻¹` times the quarter turn of the radial vector
`χ(s) - c`. -/
theorem deriv_circleCurve_eq_smul_rightAngleRotation (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s : ℝ) :
    deriv (o.circleCurve c e R) s = R⁻¹ • o.rightAngleRotation (o.circleCurve c e R s - c) := by
  rcases eq_or_ne R 0 with rfl | hR
  · have hconst : o.circleCurve c e 0 = fun _ ↦ c := funext fun _ ↦ by simp [circleCurve]
    simp [hconst]
  · rw [o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR s,
      circleCurve_eq_add_smul_rotation, add_sub_cancel_left, map_smul, inv_smul_smul₀ hR]

/-- The radial vector from `c` to `o.circleCurve c e R s` is orthogonal to the tangent there. -/
theorem inner_sub_center_deriv_circleCurve (o : Orientation ℝ E (Fin 2)) (c e : E) (R s : ℝ) :
    ⟪o.circleCurve c e R s - c, deriv (o.circleCurve c e R) s⟫ = 0 := by
  rw [o.deriv_circleCurve_eq_smul_rightAngleRotation c e R s, real_inner_smul_right,
    o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero, mul_zero]

/-- `o.circleCurve` has unit speed whenever `‖e‖ = 1` and `R ≠ 0`. -/
theorem norm_deriv_circleCurve (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : R ≠ 0) (s : ℝ) :
    ‖deriv (o.circleCurve c e R) s‖ = 1 := by
  rw [o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR s,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, he]

/-- Two arclength parameters give the same point of `o.circleCurve` (`e ≠ 0`, `R ≠ 0`) if and only
if they differ by an integer multiple of `2 π R`. -/
theorem circleCurve_eq_iff (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} {R : ℝ} (he : e ≠ 0)
    (hR : R ≠ 0) (t s : ℝ) :
    o.circleCurve c e R t = o.circleCurve c e R s ↔ ∃ k : ℤ, t - s = k * (2 * Real.pi * R) := by
  rw [circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation, add_right_inj,
    smul_right_inj hR, ← (o.rotation (s / R : ℝ)).symm.injective.eq_iff,
    LinearIsometryEquiv.symm_apply_apply, o.rotation_symm, o.rotation_rotation,
    add_comm, ← sub_eq_add_neg, ← Real.Angle.coe_sub, o.rotation_eq_self_iff_angle_eq_zero he,
    Real.Angle.coe_eq_zero_iff]
  refine exists_congr fun k ↦ ?_
  rw [zsmul_eq_mul, ← sub_div, eq_div_iff hR]
  exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

/-- For `e ≠ 0`, `o.circleCurve` is injective on `[0, 2 π R)`. -/
theorem injOn_circleCurve_Ico (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} (he : e ≠ 0) (R : ℝ) :
    InjOn (o.circleCurve c e R) (Ico 0 (2 * Real.pi * R)) := by
  intro t ht s hs hts
  have hL : 0 < 2 * Real.pi * R := lt_of_le_of_lt ht.1 ht.2
  have hR : 0 < R := pos_of_mul_pos_right hL (by positivity)
  obtain ⟨k, hk⟩ := (o.circleCurve_eq_iff c he hR.ne' t s).1 hts
  have hk_lt : (k : ℝ) < 1 := by nlinarith [ht.2, hs.1]
  have hk_gt : (-1 : ℝ) < k := by nlinarith [ht.1, hs.2]
  have hk0 : k = 0 := by
    have h1 : k < 1 := Int.cast_lt.1 (by simpa using hk_lt)
    have h2 : -1 < k := Int.cast_lt.1 (by simpa using hk_gt)
    omega
  subst hk0
  simp at hk
  linarith

/-- On `o.circleCurve`, the area form of the tangent vector with the chord `χ(t) - χ(s)` equals
`(2 R)⁻¹ ‖χ(t) - χ(s)‖²`. -/
theorem areaForm_deriv_circleCurve_sub (o : Orientation ℝ E (Fin 2)) (c e : E) (R s t : ℝ) :
    o.areaForm (deriv (o.circleCurve c e R) s)
        (o.circleCurve c e R t - o.circleCurve c e R s) =
      (2 * R)⁻¹ * ‖o.circleCurve c e R t - o.circleCurve c e R s‖ ^ 2 := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [circleCurve]
  · set u_s := o.rotation (s / R : ℝ) e
    set u_t := o.rotation (t / R : ℝ) e
    have hsub : o.circleCurve c e R t - o.circleCurve c e R s = R • (u_t - u_s) := by
      rw [circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation,
        add_sub_add_left_eq_sub, ← smul_sub]
    have hnorm_s : ‖u_s‖ = ‖e‖ := LinearIsometryEquiv.norm_map _ e
    have hnorm_t : ‖u_t‖ = ‖e‖ := LinearIsometryEquiv.norm_map _ e
    rw [o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR s, hsub,
      ← o.inner_rightAngleRotation_left, o.rightAngleRotation_rightAngleRotation, inner_neg_left,
      real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real, hnorm_s, hnorm_t,
      real_inner_comm u_t u_s]
    field_simp
    ring

/-- Advancing the parameter of `o.circleCurve c e R` by `2 R α` produces the chord
`(2 R sin α) • J (o.rotation (s / R + α) e)`. -/
theorem circleCurve_add_two_mul_sub (o : Orientation ℝ E (Fin 2)) (c e : E) (R s α : ℝ) :
    o.circleCurve c e R (s + 2 * R * α) - o.circleCurve c e R s =
      (2 * R * Real.sin α) • o.rightAngleRotation (o.rotation (s / R + α : ℝ) e) := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [circleCurve]
  · have hadd : ((s + 2 * R * α) / R + s / R) / 2 = s / R + α := by field_simp; ring
    have hsub : ((s + 2 * R * α) / R - s / R) / 2 = α := by field_simp; ring
    rw [circleCurve_def, circleCurve_def, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
      map_add, map_smul, map_smul, o.rightAngleRotation_rightAngleRotation, add_sub_add_left_eq_sub,
      ← smul_sub, ← sub_add_sub_comm, ← sub_smul, ← sub_smul, Real.cos_sub_cos, Real.sin_sub_sin,
      hadd, hsub]
    module

/-- **Double normals of a circle are diameters.** For two distinct points `χ(b) ≠ χ(a)` of
`o.circleCurve c e R`, the chord `χ(b) - χ(a)` is orthogonal to the tangent `χ'(a)` (and hence to
both tangents) if and only if `χ(b)` and `χ(a)` are antipodal across `c`. -/
theorem inner_circleCurve_sub_deriv_eq_zero_iff (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R a b : ℝ} (hne : o.circleCurve c e R b ≠ o.circleCurve c e R a) :
    ⟪o.circleCurve c e R b - o.circleCurve c e R a, deriv (o.circleCurve c e R) a⟫ = 0 ↔
      o.circleCurve c e R b - c = -(o.circleCurve c e R a - c) := by
  have hR : R ≠ 0 := by rintro rfl; simp [circleCurve] at hne
  have hsub : o.circleCurve c e R b - o.circleCurve c e R a =
      R • (o.rotation (b / R : ℝ) e - o.rotation (a / R : ℝ) e) := by
    rw [circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation,
      add_sub_add_left_eq_sub, ← smul_sub]
  have hself : ⟪o.rotation (a / R : ℝ) e, o.rightAngleRotation (o.rotation (a / R : ℝ) e)⟫ = 0 := by
    rw [real_inner_comm, o.inner_rightAngleRotation_self]
  rw [hsub, o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR a,
    real_inner_smul_left, inner_sub_left, hself, sub_zero, o.inner_rightAngleRotation_right,
    mul_eq_zero, neg_eq_zero, or_iff_right hR]
  set u_a := o.rotation (a / R : ℝ) e
  set u_b := o.rotation (b / R : ℝ) e
  have hna : ‖u_a‖ = ‖e‖ := LinearIsometryEquiv.norm_map _ e
  have hnb : ‖u_b‖ = ‖e‖ := LinearIsometryEquiv.norm_map _ e
  constructor
  · intro hω
    have hsq := o.inner_sq_add_areaForm_sq u_b u_a
    rw [hω, zero_pow two_ne_zero, add_zero, hnb, hna, ← sq] at hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | hm1
    · exfalso
      have heq : u_b = u_a := by
        have h0 : ‖u_b - u_a‖ ^ 2 = 0 := by
          rw [norm_sub_sq_real, hnb, hna, h1]
          ring
        exact sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 h0))
      exact hne (by
        rw [circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation]
        exact congrArg (fun u ↦ c + R • u) heq)
    · have hu : u_b = -u_a := by
        have h0 : ‖u_b + u_a‖ ^ 2 = 0 := by
          rw [norm_add_sq_real, hnb, hna, hm1]
          ring
        exact eq_neg_of_add_eq_zero_left (norm_eq_zero.1 (sq_eq_zero_iff.1 h0))
      rw [circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation, add_sub_cancel_left,
        add_sub_cancel_left, ← smul_neg]
      exact congrArg (R • ·) hu
  · intro hant
    have hu : u_b = -u_a := by
      rw [circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation, add_sub_cancel_left,
        add_sub_cancel_left, ← smul_neg] at hant
      exact (smul_right_inj hR).1 hant
    rw [hu, map_neg, LinearMap.neg_apply, o.areaForm_apply_self, neg_zero]

end Orientation
