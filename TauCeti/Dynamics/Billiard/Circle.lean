/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.NumberTheory.Real.Irrational
public import TauCeti.Analysis.Calculus.DifferentialForm.Exact
public import TauCeti.Analysis.Calculus.DifferentialForm.Plane
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Dynamics.Billiard.NextCollision
public import TauCeti.Dynamics.Billiard.SpherePolygon
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import TauCeti.Data.ZMod.Periodic

/-!
# Billiard dynamics and inscribed perimeter maximizers on a circle

For a circular billiard table of center `c` and radius `R > 0` in an oriented Euclidean plane `E`,
the positively oriented arclength parametrization

`χ(s) = c + R • (cos (s / R) • e + sin (s / R) • J e) = c + R • o.rotation (s / R) e`

of period `L = 2 π R` makes the next-collision map completely integrable: the tangential velocity
`v ∈ (-1, 1)` is conserved at every bounce and the arclength parameter advances by `2 R arccos v`.
This file constructs the circular billiard table, computes its strip and quotient billiard maps,
proves the chord-length primitive identity and invariant-measure properties, establishes the
rational-rotation periodicity criterion, and determines the inscribed `N`-gon perimeter maximizers
for `N = 2, 3, 4` together with explicit checks of the equal-angle reflection law.

## Main definitions

* `Orientation.circleCurve`: the curve `s ↦ c + R • (cos (s / R) • e + sin (s / R) • J e)` in an
  oriented Euclidean plane.
* `Orientation.circleBilliardTable`: the circular `TauCeti.StrictConvexBilliardTable` of center `c`,
  starting unit radial vector `e`, and radius `R > 0`, with boundary length `2 π R`.
* `TauCeti.circleBilliardQuotient`: the quotient billiard homeomorphism
  `(q, v) ↦ (q + ↑(2 R arccos v), v)` on `AddCircle (2 π R) × Ioo (-1) 1`.
* `TauCeti.circleDiameter`, `TauCeti.circleDoubledDiameter`, `TauCeti.circleInscribedSquare`,
  `TauCeti.circleEquilateralTriangle`, `TauCeti.circleRightTriangle`: explicit inscribed polygons
  testing perimeter maximization and the reflection law for `N = 2, 3, 4`.

## Main results

* `Orientation.circleBilliardTable_nextCollision`,
  `Orientation.circleBilliardTable_norm_nextParam_sub`: on `ℝ × Ioo (-1) 1`, the next-collision map
  is `(s, v) ↦ (s + 2 R arccos v, v)` and the chord length to the next collision is
  `ℓ(s, v) = 2 R √(1 - v ^ 2)`.
* `Orientation.circleBilliardTable_pullback_liouvilleForm_sub`,
  `Orientation.circleBilliardTable_pullback_symplecticForm`: the exactness identity
  `β*(v ds) - v ds = dℓ` and area preservation `β*(ds ∧ dv) = ds ∧ dv` on the open strip.
* `TauCeti.measurePreserving_circleBilliardQuotient`,
  `TauCeti.isPeriodicPt_circleBilliardQuotient_iff`,
  `TauCeti.minimalPeriod_circleBilliardQuotient`: the quotient billiard map preserves the product
  of Haar measure on `AddCircle (2 π R)` with any vertical measure (of total mass
  `4 π R = 2 L` for Lebesgue measure on `(-1, 1)`), and `(q, v)` is `n`-periodic if and only if
  `n arccos v` is an integer multiple of `π`.
* `Orientation.isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff`,
  `Orientation.not_isMaxOn_circleInscribedSquare`: for `N = 4` the perimeter maximizers on the
  circle are doubled diameters of perimeter `8 R` and period `2`, whereas the inscribed square has
  strictly smaller perimeter `4 √2 R` despite having least period `4`.
* `Orientation.isMaxOn_inscribedPerimeter_circleCurve_zmod_three_iff`,
  `Orientation.inner_incoming_circleEquilateralTriangle`,
  `Orientation.inner_outgoing_circleEquilateralTriangle`,
  `Orientation.inner_incoming_circleRightTriangle_zero`,
  `Orientation.inner_outgoing_circleRightTriangle_zero`: for `N = 3` the perimeter maximizers are
  the equilateral triangles of perimeter `3 √3 R`, where both sides of the equal-angle reflection
  law equal `1 / 2` at every vertex, while the inscribed triangle at angles `0, π / 2, π` has sides
  `0` and `1 / √2` at angle `0` and fails the reflection law there.
* `Orientation.inner_circleCurve_sub_deriv_eq_zero_iff`: on the circle, a chord between distinct
  points is orthogonal to the tangent at its endpoint (hence a double normal) if and only if it is
  a diameter.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2.
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapters 3 and 6.
-/

public section

noncomputable section

open Function Set Filter Topology Module MeasureTheory
open scoped RealInnerProductSpace ENNReal

/-! ### The circular billiard table -/

namespace Orientation

open TauCeti

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

/-- For a unit vector `e` and `R ≥ 0`, `o.circleCurve c e R` lies on `Metric.sphere c R`. -/
theorem circleCurve_mem_sphere (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 ≤ R) (s : ℝ) :
    o.circleCurve c e R s ∈ Metric.sphere c R := by
  rw [Metric.mem_sphere, dist_eq_norm, circleCurve_eq_add_smul_rotation, add_sub_cancel_left,
    norm_smul, LinearIsometryEquiv.norm_map, he, mul_one, Real.norm_of_nonneg hR]

/-- `o.circleCurve c e R` has period `2 π R`. -/
theorem periodic_circleCurve (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) :
    Periodic (o.circleCurve c e R) (2 * Real.pi * R) := fun s ↦ by
  rcases eq_or_ne R 0 with rfl | hR
  · simp
  · have hdiv : (s + 2 * Real.pi * R) / R = s / R + 2 * Real.pi := by field_simp
    simp only [circleCurve_def, hdiv, Real.cos_add_two_pi, Real.sin_add_two_pi]

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

/-- The circular billiard table of center `c`, starting unit radial vector `e`, and radius `R > 0`
in the plane `E` oriented by `o`, with boundary length `2 π R`. -/
def circleBilliardTable (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) (he : ‖e‖ = 1)
    (hR : 0 < R) : StrictConvexBilliardTable o where
  toFun := o.circleCurve c e R
  period := 2 * Real.pi * R
  period_pos := by positivity
  periodic := o.periodic_circleCurve c e R
  norm_deriv := o.norm_deriv_circleCurve c e he hR.ne'
  injOn := o.injOn_circleCurve_Ico c (norm_ne_zero_iff.1 (he.trans_ne one_ne_zero)) R
  areaForm_pos s t hne := by
    rw [o.areaForm_deriv_circleCurve_sub c e R s t]
    have hpos : 0 < ‖o.circleCurve c e R t - o.circleCurve c e R s‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 hne)
    positivity

@[simp]
theorem coe_circleBilliardTable (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) (he : ‖e‖ = 1)
    (hR : 0 < R) :
    ⇑(o.circleBilliardTable c e R he hR) = o.circleCurve c e R :=
  (rfl)

@[simp]
theorem circleBilliardTable_period (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) (he : ‖e‖ = 1)
    (hR : 0 < R) :
    (o.circleBilliardTable c e R he hR).period = 2 * Real.pi * R :=
  (rfl)

/-! ### Next-collision map, chord length, and exactness on the strip -/

/-- On the circular billiard table, the outgoing velocity at `(s, v)` is the unit tangent vector at
angle `s / R + arccos v`. -/
private theorem circleBilliardTable_outgoingDir_eq (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Icc (-1) 1) :
    (o.circleBilliardTable c e R he hR).outgoingDir s v =
      o.rightAngleRotation (o.rotation (s / R + Real.arccos v : ℝ) e) := by
  set α := Real.arccos v
  have hv_sin : √(1 - v ^ 2) = Real.Angle.sin (α : Real.Angle) := by
    rw [Real.Angle.sin_coe, Real.sin_arccos]
  have hv_cos : v = Real.Angle.cos (α : Real.Angle) := by
    rw [Real.Angle.cos_coe, Real.cos_arccos hv.1 hv.2]
  rw [StrictConvexBilliardTable.outgoingDir_def, coe_circleBilliardTable,
    o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR.ne',
    hv_sin, hv_cos, ← map_smul o.rightAngleRotation, ← map_smul o.rightAngleRotation,
    ← map_add o.rightAngleRotation, ← o.rotation_apply, o.rotation_rotation,
    ← Real.Angle.coe_add, add_comm α (s / R)]

/-- Along the circular table, advancing the arclength parameter by `2 R α` moves along the chord of
length `2 R sin α` in the direction `J (o.rotation (s / R + α) e)`. -/
private theorem circleCurve_add_two_mul_sub (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (hR : R ≠ 0) (s α : ℝ) :
    o.circleCurve c e R (s + 2 * R * α) - o.circleCurve c e R s =
      (2 * R * Real.sin α) • o.rightAngleRotation (o.rotation (s / R + α : ℝ) e) := by
  set θ := s / R
  have hdiv : (s + 2 * R * α) / R = (θ + α) + α := by
    dsimp [θ]; field_simp; ring
  have hsR : s / R = (θ + α) - α := by
    dsimp [θ]; ring
  have hcos : Real.cos ((s + 2 * R * α) / R) - Real.cos (s / R) =
      -2 * Real.sin α * Real.sin (θ + α) := by
    rw [hdiv]
    conv_lhs => rhs; rw [hsR]
    rw [Real.cos_add, Real.cos_sub]
    ring
  have hsin : Real.sin ((s + 2 * R * α) / R) - Real.sin (s / R) =
      2 * Real.sin α * Real.cos (θ + α) := by
    rw [hdiv]
    conv_lhs => rhs; rw [hsR]
    rw [Real.sin_add, Real.sin_sub]
    ring
  rw [circleCurve_def, circleCurve_def, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
    map_add, map_smul, map_smul, o.rightAngleRotation_rightAngleRotation, add_sub_add_left_eq_sub,
    ← smul_sub, ← sub_add_sub_comm, ← sub_smul, ← sub_smul, hcos, hsin]
  module

/-- On the circle of radius `R`, the next collision from `(s, v)` with `v ∈ (-1, 1)` occurs at
arclength parameter `s + 2 R arccos v`. -/
@[simp]
theorem circleBilliardTable_nextParam (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    (o.circleBilliardTable c e R he hR).nextParam s v = s + 2 * R * Real.arccos v := by
  have hα_pos : 0 < Real.arccos v := Real.arccos_pos.2 hv.2
  have hα_lt : Real.arccos v < Real.pi := Real.arccos_lt_pi.2 hv.1
  refine ((o.circleBilliardTable c e R he hR).eq_nextParam_of_areaForm_eq_zero hv ?_ ?_).symm
  · rw [circleBilliardTable_period]
    exact ⟨by nlinarith, by nlinarith⟩
  · rw [coe_circleBilliardTable, o.circleBilliardTable_outgoingDir_eq c e he hR ⟨hv.1.le, hv.2.le⟩,
      o.circleCurve_add_two_mul_sub c e hR.ne' s (Real.arccos v), map_smul,
      o.areaForm_apply_self, smul_zero]

/-- On the circle of radius `R`, the Euclidean length of the chord from `(s, v)` with `v ∈ (-1, 1)`
to the next collision is `2 R √(1 - v ^ 2)`. -/
theorem circleBilliardTable_norm_nextParam_sub (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ‖o.circleCurve c e R ((o.circleBilliardTable c e R he hR).nextParam s v) -
        o.circleCurve c e R s‖ =
      2 * R * √(1 - v ^ 2) := by
  have hsqrt : 0 ≤ 2 * R * √(1 - v ^ 2) := by positivity
  rw [o.circleBilliardTable_nextParam c e he hR hv,
    o.circleCurve_add_two_mul_sub c e hR.ne' s (Real.arccos v), Real.sin_arccos, norm_smul,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, he, mul_one,
    Real.norm_of_nonneg hsqrt]

/-- On the circle, the tangential component `v ∈ (-1, 1)` is conserved at the next collision. -/
@[simp]
theorem circleBilliardTable_nextTangential (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    (o.circleBilliardTable c e R he hR).nextTangential s v = v := by
  let α := Real.arccos v
  let u := o.rotation (s / R + α : ℝ) e
  have hu : ⟪u, u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, he, one_pow]
  have hJu : ⟪u, o.rightAngleRotation u⟫ = 0 := by
    rw [real_inner_comm, o.inner_rightAngleRotation_self]
  have hdiv : (s + 2 * R * α) / R = α + (s / R + α) := by field_simp; ring
  rw [StrictConvexBilliardTable.nextTangential_def, o.circleBilliardTable_nextParam c e he hR hv,
    coe_circleBilliardTable, o.circleBilliardTable_outgoingDir_eq c e he hR ⟨hv.1.le, hv.2.le⟩,
    o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR.ne',
    LinearIsometryEquiv.inner_map_map, hdiv, Real.Angle.coe_add α (s / R + α),
    ← o.rotation_rotation (α : Real.Angle) (s / R + α : ℝ) e,
    o.rotation_apply (α : Real.Angle) u, Real.Angle.cos_coe, Real.Angle.sin_coe, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, hu, hJu, mul_one, mul_zero, add_zero,
    Real.cos_arccos hv.1.le hv.2.le]

/-- **The next-collision map of a circle.** On `ℝ × Ioo (-1) 1`, the strip billiard map of a circle
of radius `R` is `(s, v) ↦ (s + 2 R arccos v, v)`. -/
theorem circleBilliardTable_nextCollision (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    (o.circleBilliardTable c e R he hR).nextCollision (s, v) =
      (s + 2 * R * Real.arccos v, v) := by
  rw [StrictConvexBilliardTable.nextCollision_apply, o.circleBilliardTable_nextParam c e he hR hv,
    o.circleBilliardTable_nextTangential c e he hR hv]

/-- The `n`-th iterate of the strip billiard map on the circle advances `s` by `2 n R arccos v` and
preserves `v`. -/
theorem circleBilliardTable_iterate_nextCollision (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) (n : ℕ) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ((o.circleBilliardTable c e R he hR).nextCollision^[n]) (s, v) =
      (s + n * (2 * R * Real.arccos v), v) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, o.circleBilliardTable_nextCollision c e he hR hv, ih]
    refine Prod.ext ?_ rfl
    push_cast
    ring

/-- Fréchet derivative of the strip billiard map of the circle at an interior collision state
`x = (s, v)` with `v ∈ (-1, 1)`. -/
theorem hasFDerivAt_circleBilliardTable_nextCollision (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    HasFDerivAt (o.circleBilliardTable c e R he hR).nextCollision
      ((ContinuousLinearMap.fst ℝ ℝ ℝ -
          (2 * R / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  have harc : HasDerivAt Real.arccos (-(1 / √(1 - x.2 ^ 2))) x.2 :=
    Real.hasDerivAt_arccos hx.1.ne' hx.2.ne
  have hg1 := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).add
    ((harc.comp_hasFDerivAt x (hasFDerivAt_snd (𝕜 := ℝ))).const_mul (2 * R))
  have hg : HasFDerivAt (fun y : ℝ × ℝ ↦ (y.1 + 2 * R * Real.arccos y.2, y.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ -
          (2 * R / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
    refine (hg1.prodMk (hasFDerivAt_snd (𝕜 := ℝ))).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun y ↦ Prod.ext (by simp; ring) rfl
  refine hg.congr_of_eventuallyEq ?_
  have hnhds : (univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1 ∈ 𝓝 x :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hx⟩
  filter_upwards [hnhds] with ⟨s, v⟩ hsv
  exact o.circleBilliardTable_nextCollision c e he hR hsv.2

/-- Fréchet derivative of the chord-length function `ℓ(s, v) = 2 R √(1 - v ^ 2)` on the open strip
`v ∈ (-1, 1)`. -/
theorem hasFDerivAt_circleBilliardTable_norm_nextParam_sub (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    HasFDerivAt
      (fun y : ℝ × ℝ ↦
        ‖o.circleCurve c e R ((o.circleBilliardTable c e R he hR).nextParam y.1 y.2) -
          o.circleCurve c e R y.1‖)
      (-(2 * R * x.2 / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hpos : 0 < 1 - x.2 ^ 2 := by nlinarith [hx.1, hx.2]
  have hpoly : HasDerivAt (fun v : ℝ ↦ 1 - v ^ 2) (-2 * x.2) x.2 := by
    simpa using (hasDerivAt_pow 2 x.2).const_sub 1
  have hsqrt : HasDerivAt (fun v : ℝ ↦ 2 * R * √(1 - v ^ 2))
      (2 * R * ((-2 * x.2) / (2 * √(1 - x.2 ^ 2)))) x.2 :=
    (hpoly.sqrt hpos.ne').const_mul (2 * R)
  have hg : HasFDerivAt (fun y : ℝ × ℝ ↦ 2 * R * √(1 - y.2 ^ 2))
      (-(2 * R * x.2 / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    refine (hsqrt.comp_hasFDerivAt x (hasFDerivAt_snd (𝕜 := ℝ))).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun y ↦ by simp; ring
  refine hg.congr_of_eventuallyEq ?_
  have hnhds : (univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1 ∈ 𝓝 x :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hx⟩
  filter_upwards [hnhds] with ⟨s, v⟩ hsv
  exact o.circleBilliardTable_norm_nextParam_sub c e he hR hsv.2

/-- **Chord-length primitive formula on the circle.** With `λ = v ds` (`x.2 • Prod.realPlaneDx x`)
and `ℓ(s, v) = ‖χ(nextParam s v) - χ(s)‖` the chord length to the next collision, the strip
billiard map `β` of the circle satisfies `β*λ - λ = dℓ` at every `x = (s, v)` with
`v ∈ (-1, 1)`. -/
theorem circleBilliardTable_pullback_liouvilleForm_sub (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (((o.circleBilliardTable c e R he hR).nextCollision x).2 •
          Prod.realPlaneDx ((o.circleBilliardTable c e R he hR).nextCollision x))
        (fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x) -
      x.2 • Prod.realPlaneDx x =
      differentialOneForm ℝ
        (fun y : ℝ × ℝ ↦
          ‖o.circleCurve c e R ((o.circleBilliardTable c e R he hR).nextParam y.1 y.2) -
            o.circleCurve c e R y.1‖) x := by
  have hβ := (o.hasFDerivAt_circleBilliardTable_nextCollision c e he hR hx).fderiv
  have hℓ := (o.hasFDerivAt_circleBilliardTable_norm_nextParam_sub c e he hR hx).fderiv
  have hnext : (o.circleBilliardTable c e R he hR).nextCollision x =
      (x.1 + 2 * R * Real.arccos x.2, x.2) :=
    o.circleBilliardTable_nextCollision c e he hR (s := x.1) hx
  ext u
  rw [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    differentialOneForm_apply, hnext, hβ, hℓ]
  simp only [Prod.realPlaneDx_apply, Function.comp_apply, ContinuousLinearMap.prod_apply,
    FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **Area preservation on the strip.** The strip billiard map `β` of the circle preserves the
two-form `ω = ds ∧ dv` at every `x = (s, v)` with `v ∈ (-1, 1)`. -/
theorem circleBilliardTable_pullback_symplecticForm (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    ContinuousAlternatingMap.compContinuousLinearMap
        ((Prod.realPlaneDx ((o.circleBilliardTable c e R he hR).nextCollision x)).wedge
          (Prod.realPlaneDy ((o.circleBilliardTable c e R he hR).nextCollision x)))
        (fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x) =
      (Prod.realPlaneDx x).wedge (Prod.realPlaneDy x) := by
  have hβ := (o.hasFDerivAt_circleBilliardTable_nextCollision c e he hR hx).fderiv
  ext u
  have hu : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
  have hcomp : fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x ∘ ![u 0, u 1] =
      ![fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x (u 0),
        fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x (u 1)] := by
    funext i; fin_cases i <;> rfl
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hu, hcomp,
    ContinuousAlternatingMap.wedge_apply_one_one, ContinuousAlternatingMap.wedge_apply_one_one, hβ]
  simp only [Prod.realPlaneDx_apply, Prod.realPlaneDy_apply, Matrix.cons_val_zero,
    ContinuousLinearMap.prod_apply, FunLike.coe_sub, Pi.sub_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

end Orientation

/-! ### The quotient billiard map, its invariant measure, and rational-rotation periodicity -/

namespace TauCeti

/-- **The quotient billiard homeomorphism of a circle of radius `R`.** On the topological phase
space `AddCircle (2 π R) × Ioo (-1) 1`, it sends `(q, v)` to `(q + ↑(2 R arccos v), v)`. -/
def circleBilliardQuotient (R : ℝ) :
    AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1 ≃ₜ
      AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1 where
  toFun p := (p.1 + ↑(2 * R * Real.arccos p.2.1), p.2)
  invFun p := (p.1 - ↑(2 * R * Real.arccos p.2.1), p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ continuous_snd
    exact continuous_fst.add
      (QuotientAddGroup.continuous_mk.comp
        (continuous_const.mul (Real.continuous_arccos.comp
          (continuous_subtype_val.comp continuous_snd))))
  continuous_invFun := by
    refine Continuous.prodMk ?_ continuous_snd
    exact continuous_fst.sub
      (QuotientAddGroup.continuous_mk.comp
        (continuous_const.mul (Real.continuous_arccos.comp
          (continuous_subtype_val.comp continuous_snd))))

@[simp]
theorem circleBilliardQuotient_apply (R : ℝ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    circleBilliardQuotient R p = (p.1 + ↑(2 * R * Real.arccos p.2.1), p.2) :=
  (rfl)

@[simp]
theorem circleBilliardQuotient_symm_apply (R : ℝ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    (circleBilliardQuotient R).symm p = (p.1 - ↑(2 * R * Real.arccos p.2.1), p.2) :=
  (rfl)

end TauCeti

namespace Orientation

open TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

/-- `TauCeti.circleBilliardQuotient R` is the quotient of
`(o.circleBilliardTable c e R he hR).nextCollision` modulo deck translations by `2 π R`. -/
theorem circleBilliardQuotient_coe (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ} (he : ‖e‖ = 1)
    (hR : 0 < R) (s : ℝ) (v : Ioo (-1 : ℝ) 1) :
    circleBilliardQuotient R (↑s, v) =
      (↑((o.circleBilliardTable c e R he hR).nextParam s v.1),
        ⟨(o.circleBilliardTable c e R he hR).nextTangential s v.1,
          (o.circleBilliardTable c e R he hR).nextTangential_mem_Ioo v.2⟩) := by
  ext
  · simp [o.circleBilliardTable_nextParam c e he hR v.2, QuotientAddGroup.mk_add]
  · simp [o.circleBilliardTable_nextTangential c e he hR v.2]

end Orientation

namespace TauCeti

/-- **Measure preservation on the quotient.** For any measure `ν` on `Ioo (-1) 1` (in particular
Lebesgue measure), `circleBilliardQuotient R` preserves the product of the Haar measure `volume` on
`AddCircle (2 π R)` with `ν`. -/
theorem measurePreserving_circleBilliardQuotient (R : ℝ) [Fact (0 < 2 * Real.pi * R)]
    (ν : Measure (Ioo (-1 : ℝ) 1)) :
    MeasurePreserving (circleBilliardQuotient R) (volume.prod ν) (volume.prod ν) := by
  by_cases hν : SFinite ν
  · have hgm : Measurable (uncurry fun (v : Ioo (-1 : ℝ) 1) (q : AddCircle (2 * Real.pi * R)) ↦
        q + (↑(2 * R * Real.arccos v.1) : AddCircle (2 * Real.pi * R))) :=
      (continuous_snd.add (QuotientAddGroup.continuous_mk.comp
        (continuous_const.mul (Real.continuous_arccos.comp
          (continuous_subtype_val.comp continuous_fst))))).measurable
    have hshear := MeasurePreserving.skew_product
      (g := fun (v : Ioo (-1 : ℝ) 1) (q : AddCircle (2 * Real.pi * R)) ↦
        q + (↑(2 * R * Real.arccos v.1) : AddCircle (2 * Real.pi * R)))
      (MeasurePreserving.id ν) hgm
      (Eventually.of_forall fun v ↦
        map_add_right_eq_self (volume : Measure (AddCircle (2 * Real.pi * R)))
          (↑(2 * R * Real.arccos v.1) : AddCircle (2 * Real.pi * R)))
    convert Measure.measurePreserving_swap.comp (hshear.comp Measure.measurePreserving_swap)
    ext ⟨q, v⟩ <;> rfl
  · rw [Measure.prod_eq_zero_of_not_sfinite hν]
    exact ⟨(circleBilliardQuotient R).continuous.measurable, Measure.map_zero _⟩

/-- Total mass `4 π R = 2 L` of the product of `volume` on `AddCircle (2 π R)` with Lebesgue
measure `Measure.comap Subtype.val volume` on `Ioo (-1) 1`. -/
theorem measure_univ_circleBilliardPhaseSpace (R : ℝ) [hL : Fact (0 < 2 * Real.pi * R)] :
    ((volume : Measure (AddCircle (2 * Real.pi * R))).prod
        (Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume)) univ =
      ENNReal.ofReal (4 * Real.pi * R) := by
  have hIoo : (Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume) univ =
      ENNReal.ofReal 2 := by
    rw [← Measure.Subtype.volume_def,
      Measure.Subtype.volume_univ isOpen_Ioo.measurableSet.nullMeasurableSet, Real.volume_Ioo]
    norm_num
  have : IsFiniteMeasure (Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume) :=
    ⟨by rw [hIoo]; exact ENNReal.ofReal_lt_top⟩
  have hR_nonneg : 0 ≤ 2 * Real.pi * R := hL.out.le
  rw [← univ_prod_univ, Measure.prod_prod, AddCircle.measure_univ, hIoo,
    ← ENNReal.ofReal_mul hR_nonneg]
  congr 1
  ring

/-- The `n`-th forward iterate of `circleBilliardQuotient R` rotates the first coordinate by
`n • ↑(2 R arccos v)` and fixes `v`. -/
@[simp]
theorem iterate_circleBilliardQuotient (R : ℝ) (n : ℕ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    ((circleBilliardQuotient R)^[n]) p =
      (p.1 + n • (↑(2 * R * Real.arccos p.2.1) : AddCircle (2 * Real.pi * R)), p.2) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [succ_nsmul', add_assoc]

/-- The `n`-th backward iterate of `circleBilliardQuotient R` subtracts `n • ↑(2 R arccos v)` from
the first coordinate and fixes `v`. -/
@[simp]
theorem iterate_circleBilliardQuotient_symm (R : ℝ) (n : ℕ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    (((circleBilliardQuotient R).symm)^[n]) p =
      (p.1 - n • (↑(2 * R * Real.arccos p.2.1) : AddCircle (2 * Real.pi * R)), p.2) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    refine Prod.ext ?_ rfl
    simp only [circleBilliardQuotient_symm_apply, succ_nsmul', sub_eq_add_neg, neg_add_rev]
    abel

/-- **Rational-rotation periodicity criterion.** For `R ≠ 0`, a quotient collision state
`p = (q, v)` has period `n` under `circleBilliardQuotient R` if and only if `n * arccos v` is an
integer multiple of `π`. -/
theorem isPeriodicPt_circleBilliardQuotient_iff {R : ℝ} (hR : R ≠ 0) (n : ℕ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    IsPeriodicPt (circleBilliardQuotient R) n p ↔
      ∃ k : ℤ, (n : ℝ) * Real.arccos p.2.1 = k * Real.pi := by
  rw [IsPeriodicPt, IsFixedPt, iterate_circleBilliardQuotient, Prod.ext_iff]
  simp only [and_true, add_eq_left, ← AddCircle.coe_nsmul, nsmul_eq_mul,
    AddCircle.coe_eq_zero_iff, zsmul_eq_mul]
  refine exists_congr fun k ↦ ⟨fun h ↦ ?_, fun h ↦ by linear_combination -2 * R * h⟩
  have hmul : (2 * R) * ((n : ℝ) * Real.arccos p.2.1 - k * Real.pi) = 0 := by linarith
  linarith [(mul_eq_zero.1 hmul).resolve_left (mul_ne_zero two_ne_zero hR)]

/-- A state `p = (q, v)` lies on a periodic orbit of `circleBilliardQuotient R` (`R ≠ 0`) if and
only if `arccos v` is a rational multiple of `π`. -/
theorem exists_pos_isPeriodicPt_circleBilliardQuotient_iff {R : ℝ} (hR : R ≠ 0)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    (∃ n > 0, IsPeriodicPt (circleBilliardQuotient R) n p) ↔
      ∃ r : ℚ, Real.arccos p.2.1 = r * Real.pi := by
  constructor
  · rintro ⟨n, hn, hper⟩
    obtain ⟨k, hk⟩ := (isPeriodicPt_circleBilliardQuotient_iff hR n p).1 hper
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine ⟨(k : ℚ) / (n : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hn']
    linarith
  · rintro ⟨r, hr⟩
    refine ⟨r.den, r.pos, (isPeriodicPt_circleBilliardQuotient_iff hR r.den p).2 ⟨r.num, ?_⟩⟩
    have hden : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 r.pos.ne'
    have hrat : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den r).symm
    rw [hr, hrat]
    field_simp

/-- **Exact least period under coprime rotation number.** If `n * arccos v = k * π` with `n > 0`
and `k` coprime to `n`, then the least period of `(q, v)` under `circleBilliardQuotient R` (`R ≠ 0`)
is `n`. -/
theorem minimalPeriod_circleBilliardQuotient {R : ℝ} (hR : R ≠ 0) {n : ℕ} (hn : 0 < n) {k : ℤ}
    {p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1}
    (hk : (n : ℝ) * Real.arccos p.2.1 = k * Real.pi) (hcop : IsCoprime k (n : ℤ)) :
    minimalPeriod (circleBilliardQuotient R) p = n := by
  have hper_n : IsPeriodicPt (circleBilliardQuotient R) n p :=
    (isPeriodicPt_circleBilliardQuotient_iff hR n p).2 ⟨k, hk⟩
  refine le_antisymm (hper_n.minimalPeriod_le hn) ?_
  set m := minimalPeriod (circleBilliardQuotient R) p
  have hm : 0 < m := hper_n.minimalPeriod_pos hn
  have hper_m : IsPeriodicPt (circleBilliardQuotient R) m p := isPeriodicPt_minimalPeriod _ _
  obtain ⟨l, hl⟩ := (isPeriodicPt_circleBilliardQuotient_iff hR m p).1 hper_m
  have hreal : ((m : ℤ) * k : ℝ) * Real.pi = ((n : ℤ) * l : ℝ) * Real.pi := by
    calc
      ((m : ℤ) * k : ℝ) * Real.pi = (m : ℝ) * ((n : ℝ) * Real.arccos p.2.1) := by
        push_cast; linear_combination (m : ℝ) * hk.symm
      _ = (n : ℝ) * ((m : ℝ) * Real.arccos p.2.1) := by ring
      _ = ((n : ℤ) * l : ℝ) * Real.pi := by
        push_cast; linear_combination (n : ℝ) * hl
  have hint : (m : ℤ) * k = (n : ℤ) * l := by
    exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero hreal
  have hdvd : (n : ℤ) ∣ (m : ℤ) :=
    hcop.symm.dvd_of_dvd_mul_right ⟨l, hint⟩
  exact Nat.le_of_dvd hm (Int.ofNat_dvd.1 hdvd)

/-- **Irrational-rotation density.** For `R ≠ 0`, the two-sided angular orbit
`z ↦ q + z • ↑(2 R arccos v)` is dense in `AddCircle (2 π R)` if and only if `arccos v / π` is
irrational. -/
theorem denseRange_zsmul_circleBilliardQuotient_iff {R : ℝ} (hR : R ≠ 0)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    DenseRange
        (fun z : ℤ ↦ p.1 + z • (↑(2 * R * Real.arccos p.2.1) : AddCircle (2 * Real.pi * R))) ↔
      Irrational (Real.arccos p.2.1 / Real.pi) := by
  let e := Homeomorph.addLeft p.1
  have hiff : DenseRange
      (fun z : ℤ ↦ e (z • (↑(2 * R * Real.arccos p.2.1) : AddCircle (2 * Real.pi * R)))) ↔
      DenseRange (fun z : ℤ ↦ z • (↑(2 * R * Real.arccos p.2.1) : AddCircle (2 * Real.pi * R))) :=
    ⟨fun h ↦ by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
        e.symm.surjective.denseRange.comp h e.symm.continuous,
     fun h ↦ e.surjective.denseRange.comp h e.continuous⟩
  have hdiv : (2 * R * Real.arccos p.2.1) / (2 * Real.pi * R) = Real.arccos p.2.1 / Real.pi := by
    field_simp
  exact hiff.trans (AddCircle.denseRange_zsmul_coe_iff.trans (by rw [hdiv]))

/-! ### Explicit perimeter maximizers and reflection-law checks on the circle (`N = 2, 3, 4`) -/

/-- The diameter `2`-gon on a circle of radius `R` starting at arclength parameter `s₀`. -/
def circleDiameter (R s₀ : ℝ) : ZMod 2 → ℝ := ![s₀, s₀ + Real.pi * R]

theorem circleDiameter_def (R s₀ : ℝ) :
    circleDiameter R s₀ = ![s₀, s₀ + Real.pi * R] :=
  (rfl)

/-- A diameter billiard state (`v = 0`) on `circleBilliardQuotient R` (`R ≠ 0`) has least period
`2`. -/
theorem minimalPeriod_circleBilliardQuotient_zero {R : ℝ} (hR : R ≠ 0)
    (q : AddCircle (2 * Real.pi * R)) {hv : (0 : ℝ) ∈ Ioo (-1) 1} :
    minimalPeriod (circleBilliardQuotient R) (q, ⟨0, hv⟩) = 2 := by
  refine minimalPeriod_circleBilliardQuotient hR (by decide) (k := 1) ?_ isCoprime_one_left
  simp only [Real.arccos_zero]
  push_cast
  ring

/-- The doubled-diameter `4`-gon on a circle of radius `R`, traversing the diameter from `s₀` to
`s₀ + π R` twice. -/
def circleDoubledDiameter (R s₀ : ℝ) : ZMod 4 → ℝ :=
  ![s₀, s₀ + Real.pi * R, s₀, s₀ + Real.pi * R]

theorem circleDoubledDiameter_def (R s₀ : ℝ) :
    circleDoubledDiameter R s₀ = ![s₀, s₀ + Real.pi * R, s₀, s₀ + Real.pi * R] :=
  (rfl)

/-- The regular inscribed square on a circle of radius `R` starting at arclength parameter `s₀`,
with quarter-circle step `π R / 2`. -/
def circleInscribedSquare (R s₀ : ℝ) (k : ZMod 4) : ℝ :=
  s₀ + (k.val : ℝ) * (Real.pi * R / 2)

theorem circleInscribedSquare_apply (R s₀ : ℝ) (k : ZMod 4) :
    circleInscribedSquare R s₀ k = s₀ + (k.val : ℝ) * (Real.pi * R / 2) :=
  (rfl)

/-- Although not a global perimeter maximizer, the inscribed square corresponds to a quotient
billiard state `(q, √2 / 2)` of genuine least period `4` (`R ≠ 0`). -/
theorem minimalPeriod_circleBilliardQuotient_sqrt_two_div_two {R : ℝ} (hR : R ≠ 0)
    (q : AddCircle (2 * Real.pi * R)) {hv : √2 / 2 ∈ Ioo (-1 : ℝ) 1} :
    minimalPeriod (circleBilliardQuotient R) (q, ⟨√2 / 2, hv⟩) = 4 := by
  have harc : Real.arccos (√2 / 2) = Real.pi / 4 :=
    Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_four.symm
  refine minimalPeriod_circleBilliardQuotient hR (by decide) (k := 1) ?_ isCoprime_one_left
  simp only [harc]
  push_cast
  ring

/-- The positively oriented inscribed equilateral triangle on a circle of radius `R` starting at
arclength parameter `s₀`, with one-third-turn step `2 π R / 3`. -/
def circleEquilateralTriangle (R s₀ : ℝ) (k : ZMod 3) : ℝ :=
  s₀ + (k.val : ℝ) * (2 * Real.pi * R / 3)

theorem circleEquilateralTriangle_apply (R s₀ : ℝ) (k : ZMod 3) :
    circleEquilateralTriangle R s₀ k = s₀ + (k.val : ℝ) * (2 * Real.pi * R / 3) :=
  (rfl)

/-- An equilateral-triangle billiard state (`v = 1 / 2`) on `circleBilliardQuotient R` (`R ≠ 0`)
has least period `3`. -/
theorem minimalPeriod_circleBilliardQuotient_half {R : ℝ} (hR : R ≠ 0)
    (q : AddCircle (2 * Real.pi * R)) {hv : (1 / 2 : ℝ) ∈ Ioo (-1) 1} :
    minimalPeriod (circleBilliardQuotient R) (q, ⟨1 / 2, hv⟩) = 3 := by
  have harc : Real.arccos (1 / 2) = Real.pi / 3 :=
    Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_three.symm
  refine minimalPeriod_circleBilliardQuotient hR (by decide) (k := 1) ?_ isCoprime_one_left
  simp only [harc]
  push_cast
  ring

/-- The right-angled inscribed triangle on a circle of radius `R` with vertices at central angles
`0`, `π / 2`, and `π` (arclength parameters `0`, `π R / 2`, `π R`). -/
def circleRightTriangle (R : ℝ) : ZMod 3 → ℝ :=
  ![0, Real.pi * R / 2, Real.pi * R]

theorem circleRightTriangle_def (R : ℝ) :
    circleRightTriangle R = ![0, Real.pi * R / 2, Real.pi * R] :=
  (rfl)

end TauCeti

namespace Orientation

open TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

private theorem circleCurve_mem_sphere_norm_smul (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s : ℝ) :
    o.circleCurve c e R s ∈ Metric.sphere c ‖R • e‖ := by
  rw [Metric.mem_sphere, dist_eq_norm, circleCurve_eq_add_smul_rotation, add_sub_cancel_left,
    norm_smul, LinearIsometryEquiv.norm_map, ← norm_smul]

/-! #### `N = 2`: diameters and double normals -/

private theorem inscribedPerimeter_circleDiameter_eq (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDiameter R s₀) = 4 * ‖R • e‖ := by
  refine (inscribedPerimeter_zmod_two_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)).2 ?_
  simpa [circleDiameter] using o.circleCurve_add_pi_mul_sub_center c e R s₀

/-- A diameter `2`-gon on `o.circleCurve c e R` (`R ≥ 0`) has inscribed perimeter `4 R`. -/
@[simp]
theorem inscribedPerimeter_circleDiameter (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDiameter R s₀) = 4 * R := by
  rw [o.inscribedPerimeter_circleDiameter_eq, norm_smul, he, mul_one, Real.norm_of_nonneg hR]

/-- A `2`-gon maximizes the inscribed perimeter on `o.circleCurve c e R` if and only if its two
vertices are antipodal across `c` (a diameter). -/
theorem isMaxOn_inscribedPerimeter_circleCurve_zmod_two_iff (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R : ℝ) (s : ZMod 2 → ℝ) :
    IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s ↔
      o.circleCurve c e R (s 1) - c = -(o.circleCurve c e R (s 0) - c) := by
  rw [← inscribedPerimeter_zmod_two_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)]
  constructor
  · intro hs
    refine le_antisymm
      (inscribedPerimeter_zmod_two_le_of_mem_sphere
        fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _) ?_
    simpa [o.inscribedPerimeter_circleDiameter_eq] using
      isMaxOn_iff.1 hs (circleDiameter R 0) (mem_univ _)
  · intro hs
    refine isMaxOn_iff.2 fun r _ ↦ ?_
    rw [hs]
    exact inscribedPerimeter_zmod_two_le_of_mem_sphere
      fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _

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

/-! #### `N = 4`: the doubled diameter maximizes perimeter, not the inscribed square -/

private theorem inscribedPerimeter_circleDoubledDiameter_eq (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDoubledDiameter R s₀) = 8 * ‖R • e‖ := by
  refine (inscribedPerimeter_zmod_four_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)).2 ?_
  have hant := o.circleCurve_add_pi_mul_sub_center c e R s₀
  have h0 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((0 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 0) - c) := hant
  have h1 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((1 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 1) - c) := by
    have hv2 : circleDoubledDiameter R s₀ ((1 : ZMod 4) + 1) = s₀ := rfl
    have hv1 : circleDoubledDiameter R s₀ 1 = s₀ + Real.pi * R := rfl
    rw [hv2, hv1, hant, neg_neg]
  have h2 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((2 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 2) - c) := hant
  have h3 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((3 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 3) - c) := by
    have hv0 : circleDoubledDiameter R s₀ ((3 : ZMod 4) + 1) = s₀ := rfl
    have hv3 : circleDoubledDiameter R s₀ 3 = s₀ + Real.pi * R := rfl
    rw [hv0, hv3, hant, neg_neg]
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- For `‖e‖ = 1` and `R ≥ 0`, the doubled diameter has inscribed perimeter `8 R`. -/
@[simp]
theorem inscribedPerimeter_circleDoubledDiameter (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDoubledDiameter R s₀) = 8 * R := by
  rw [o.inscribedPerimeter_circleDoubledDiameter_eq, norm_smul, he, mul_one,
    Real.norm_of_nonneg hR]

/-- **For `N = 4`, perimeter maximizers on the circle are doubled diameters.** A `4`-gon maximizes
`inscribedPerimeter` on `o.circleCurve c e R` if and only if consecutive vertices are antipodal
across `c`. -/
theorem isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff (o : Orientation ℝ E (Fin 2))
    (c e : E) (R : ℝ) (s : ZMod 4 → ℝ) :
    IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s ↔
      ∀ k, o.circleCurve c e R (s (k + 1)) - c = -(o.circleCurve c e R (s k) - c) := by
  rw [← inscribedPerimeter_zmod_four_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)]
  constructor
  · intro hs
    refine le_antisymm
      (inscribedPerimeter_zmod_four_le_of_mem_sphere
        fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _) ?_
    simpa [o.inscribedPerimeter_circleDoubledDiameter_eq] using
      isMaxOn_iff.1 hs (circleDoubledDiameter R 0) (mem_univ _)
  · intro hs
    refine isMaxOn_iff.2 fun r _ ↦ ?_
    rw [hs]
    exact inscribedPerimeter_zmod_four_le_of_mem_sphere
      fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _

/-- Every `N = 4` perimeter maximizer on `o.circleCurve c e R` repeats its vertices with period
`2`: `χ(s_(k+2)) = χ(s_k)`. -/
theorem circleCurve_add_two_of_isMaxOn_zmod_four (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R : ℝ) {s : ZMod 4 → ℝ}
    (hs : IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s) (k : ZMod 4) :
    o.circleCurve c e R (s (k + 2)) = o.circleCurve c e R (s k) := by
  have h24 : (2 : ℝ) * (4 : ℕ) * ‖R • e‖ = 8 * ‖R • e‖ := by push_cast; ring
  have heq : inscribedPerimeter (o.circleCurve c e R) s = 2 * (4 : ℕ) * ‖R • e‖ := by
    rw [h24, inscribedPerimeter_zmod_four_eq_iff_of_mem_sphere
      (fun j ↦ o.circleCurve_mem_sphere_norm_smul c e R _)]
    exact (o.isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff c e R s).1 hs
  exact apply_add_two_eq_of_inscribedPerimeter_eq_two_mul
    (fun j ↦ o.circleCurve_mem_sphere_norm_smul c e R _) heq k

private theorem circleCurve_circleInscribedSquare_succ (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) (k : ZMod 4) :
    o.circleCurve c e R (circleInscribedSquare R s₀ (k + 1)) =
      o.circleCurve c e R (circleInscribedSquare R s₀ k + Real.pi * R / 2) := by
  have hstep : 2 * Real.pi * R / (4 : ℕ) = Real.pi * R / 2 := by push_cast; ring
  simpa only [circleInscribedSquare_apply, hstep] using
    (o.periodic_circleCurve c e R).apply_add_val_add_one_mul_div s₀ k

/-- For `‖e‖ = 1` and `R ≥ 0`, each side of `circleInscribedSquare R s₀` has length `√2 R`, so the
inscribed square has perimeter `4 √2 R`. -/
@[simp]
theorem inscribedPerimeter_circleInscribedSquare (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleInscribedSquare R s₀) = 4 * √2 * R := by
  rcases hR.eq_or_lt with rfl | hR
  · simp [circleCurve, inscribedPerimeter_def]
  · have hv : √2 / 2 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by nlinarith [Real.sqrt_nonneg 2],
        by nlinarith [Real.sq_sqrt zero_le_two, Real.sqrt_nonneg 2]⟩
    have harc : Real.arccos (√2 / 2) = Real.pi / 4 :=
      Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_four.symm
    have hstep (t : ℝ) : ‖o.circleCurve c e R (t + Real.pi * R / 2) - o.circleCurve c e R t‖ =
        √2 * R := by
      have hparam : t + Real.pi * R / 2 =
          (o.circleBilliardTable c e R he hR).nextParam t (√2 / 2) := by
        rw [o.circleBilliardTable_nextParam c e he hR hv, harc]
        ring
      have hlen := o.circleBilliardTable_norm_nextParam_sub c e he hR (s := t) hv
      rw [← hparam] at hlen
      have hsq : √(1 - (√2 / 2) ^ 2) = √2 / 2 := by
        have h1 : 1 - (√2 / 2) ^ 2 = (√2 / 2) ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num)]
          norm_num
        rw [h1, Real.sqrt_sq (by positivity)]
      rw [hlen, hsq]
      ring
    rw [inscribedPerimeter_def]
    have hterms : ∀ k : ZMod 4,
        ‖o.circleCurve c e R (circleInscribedSquare R s₀ (k + 1)) -
            o.circleCurve c e R (circleInscribedSquare R s₀ k)‖ = √2 * R := fun k ↦ by
      rw [o.circleCurve_circleInscribedSquare_succ, hstep]
    simp only [hterms, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    push_cast
    ring

/-- **The inscribed square does not maximize perimeter for `N = 4`.** Whenever `e ≠ 0` and `R ≠ 0`,
consecutive vertices of `circleInscribedSquare R s₀` differ by a quarter turn rather than being
antipodal. -/
theorem not_isMaxOn_circleInscribedSquare (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} {R : ℝ}
    (he : e ≠ 0) (hR : R ≠ 0) (s₀ : ℝ) :
    ¬ IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ (circleInscribedSquare R s₀) := by
  intro hmax
  have hant := (o.isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff c e R _).1 hmax 0
  have hv0 : circleInscribedSquare R s₀ 0 = s₀ := by simp [circleInscribedSquare]
  have hv1 : circleInscribedSquare R s₀ (0 + 1) = s₀ + Real.pi * R / 2 := by
    have h1 : (0 + 1 : ZMod 4).val = 1 := rfl
    rw [circleInscribedSquare_apply, h1, Nat.cast_one, one_mul]
  have hdiv : (s₀ + Real.pi * R / 2) / R = Real.pi / 2 + s₀ / R := by field_simp; ring
  set u₀ := o.rotation (s₀ / R : ℝ) e
  have hu₁ : o.rotation ((s₀ + Real.pi * R / 2) / R : ℝ) e = o.rightAngleRotation u₀ := by
    rw [hdiv, Real.Angle.coe_add, ← o.rotation_rotation, o.rotation_apply, Real.Angle.cos_coe,
      Real.Angle.sin_coe, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]
  rw [hv1, hv0, circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation,
    add_sub_cancel_left, add_sub_cancel_left, ← smul_neg, smul_right_inj hR, hu₁] at hant
  have hin : ⟪u₀, o.rightAngleRotation u₀⟫ = 0 := by
    rw [real_inner_comm, o.inner_rightAngleRotation_self]
  rw [hant, inner_neg_right, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map,
    neg_eq_zero, sq_eq_zero_iff, norm_eq_zero] at hin
  exact he hin

/-! #### `N = 3`: the equilateral triangle versus the `0, π / 2, π` inscribed triangle -/

private theorem circleCurve_circleEquilateralTriangle_succ (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) (k : ZMod 3) :
    o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) =
      o.circleCurve c e R (circleEquilateralTriangle R s₀ k + 2 * Real.pi * R / 3) := by
  simpa [circleEquilateralTriangle_apply] using
    (o.periodic_circleCurve c e R).apply_add_val_add_one_mul_div s₀ k

private theorem circleCurve_circleEquilateralTriangle_pred (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) (k : ZMod 3) :
    o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1)) =
      o.circleCurve c e R (circleEquilateralTriangle R s₀ k - 2 * Real.pi * R / 3) := by
  simpa [circleEquilateralTriangle_apply] using
    (o.periodic_circleCurve c e R).apply_add_val_sub_one_mul_div s₀ k

/-- Stepping by `2 π R / 3` along `o.circleCurve c e R` (`R > 0`) traces the chord of `nextParam`
at tangential component `v = 1 / 2`, of length `√3 R` and direction `outgoingDir t (1 / 2)`. -/
private theorem circleCurve_step_third_eq (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) (t : ℝ) :
    o.circleCurve c e R (t + 2 * Real.pi * R / 3) - o.circleCurve c e R t =
      (√3 * R) • (o.circleBilliardTable c e R he hR).outgoingDir t (1 / 2) := by
  have hv : (1 / 2 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have harc : Real.arccos (1 / 2) = Real.pi / 3 :=
    Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_three.symm
  have hparam : t + 2 * Real.pi * R / 3 =
      (o.circleBilliardTable c e R he hR).nextParam t (1 / 2) := by
    rw [o.circleBilliardTable_nextParam c e he hR hv, harc]
    ring
  have hlen : ‖o.circleCurve c e R (t + 2 * Real.pi * R / 3) - o.circleCurve c e R t‖ =
      √3 * R := by
    have hc := o.circleBilliardTable_norm_nextParam_sub c e he hR (s := t) hv
    rw [← hparam] at hc
    have hsqrt : √(1 - (1 / 2 : ℝ) ^ 2) = √3 / 2 := by
      have h34 : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 2 ^ 2 := by norm_num
      rw [h34, Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [hc, hsqrt]
    ring
  have hsub := (o.circleBilliardTable c e R he hR).sub_eq_norm_smul_outgoingDir (s := t) hv
  simpa only [coe_circleBilliardTable, ← hparam, hlen] using hsub

/-- Every side of `circleEquilateralTriangle R s₀` (`R ≥ 0`) has length `√3 R`. -/
theorem norm_sub_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) (k : ZMod 3) :
    ‖o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) -
        o.circleCurve c e R (circleEquilateralTriangle R s₀ k)‖ = √3 * R := by
  rcases hR.eq_or_lt with rfl | hRpos
  · simp [circleCurve]
  · rw [o.circleCurve_circleEquilateralTriangle_succ, o.circleCurve_step_third_eq c e he hRpos,
      norm_smul, (o.circleBilliardTable c e R he hRpos).norm_outgoingDir (by norm_num),
      mul_one, Real.norm_of_nonneg (by positivity)]

/-- `circleEquilateralTriangle R s₀` (`R ≥ 0`) has inscribed perimeter `3 √3 R`. -/
@[simp]
theorem inscribedPerimeter_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleEquilateralTriangle R s₀) = 3 * √3 * R :=
  (inscribedPerimeter_zmod_three_eq_iff_norm_sub_eq
    fun _ ↦ o.circleCurve_mem_sphere c e he hR _).2
    (o.norm_sub_circleEquilateralTriangle c e he hR s₀)

/-- **For `N = 3`, perimeter maximizers on the circle are equilateral triangles.** A `3`-gon
maximizes `inscribedPerimeter` on `o.circleCurve c e R` (`R ≥ 0`) if and only if every side has
length `√3 R`. -/
theorem isMaxOn_inscribedPerimeter_circleCurve_zmod_three_iff (o : Orientation ℝ E (Fin 2))
    (c e : E) {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s : ZMod 3 → ℝ) :
    IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s ↔
      ∀ k, ‖o.circleCurve c e R (s (k + 1)) - o.circleCurve c e R (s k)‖ = √3 * R := by
  rw [← inscribedPerimeter_zmod_three_eq_iff_norm_sub_eq
    (fun k ↦ o.circleCurve_mem_sphere c e he hR _)]
  constructor
  · intro hs
    refine le_antisymm
      (inscribedPerimeter_zmod_three_le_of_mem_sphere
        fun k ↦ o.circleCurve_mem_sphere c e he hR _) ?_
    simpa [o.inscribedPerimeter_circleEquilateralTriangle c e he hR 0] using
      isMaxOn_iff.1 hs (circleEquilateralTriangle R 0) (mem_univ _)
  · intro hs
    refine isMaxOn_iff.2 fun r _ ↦ ?_
    rw [hs]
    exact inscribedPerimeter_zmod_three_le_of_mem_sphere
      fun k ↦ o.circleCurve_mem_sphere c e he hR _

/-- **Outgoing side of the reflection law on the equilateral triangle.** At every vertex `k` of
`circleEquilateralTriangle R s₀` (`R > 0`), the unit outgoing chord has inner product `1 / 2` with
the unit tangent `χ'(s_k)`. -/
theorem inner_outgoing_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) (s₀ : ℝ) (k : ZMod 3) :
    ⟪‖o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ k)‖⁻¹ •
        (o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ k)),
      deriv (o.circleCurve c e R) (circleEquilateralTriangle R s₀ k)⟫ = 1 / 2 := by
  have hpos : √3 * R ≠ 0 := by positivity
  rw [o.norm_sub_circleEquilateralTriangle c e he hR.le s₀ k,
    o.circleCurve_circleEquilateralTriangle_succ, o.circleCurve_step_third_eq c e he hR,
    inv_smul_smul₀ hpos, real_inner_comm]
  exact (o.circleBilliardTable c e R he hR).inner_deriv_outgoingDir _ (1 / 2)

/-- **Incoming side of the reflection law on the equilateral triangle.** At every vertex `k` of
`circleEquilateralTriangle R s₀` (`R > 0`), the unit incoming chord also has inner product `1 / 2`
with the unit tangent `χ'(s_k)`. -/
theorem inner_incoming_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) (s₀ : ℝ) (k : ZMod 3) :
    ⟪‖o.circleCurve c e R (circleEquilateralTriangle R s₀ k) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1))‖⁻¹ •
        (o.circleCurve c e R (circleEquilateralTriangle R s₀ k) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1))),
      deriv (o.circleCurve c e R) (circleEquilateralTriangle R s₀ k)⟫ = 1 / 2 := by
  set t := circleEquilateralTriangle R s₀ k - 2 * Real.pi * R / 3
  have ht : t + 2 * Real.pi * R / 3 = circleEquilateralTriangle R s₀ k := sub_add_cancel _ _
  have hv : (1 / 2 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have harc : Real.arccos (1 / 2) = Real.pi / 3 :=
    Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_three.symm
  have hparam : circleEquilateralTriangle R s₀ k =
      (o.circleBilliardTable c e R he hR).nextParam t (1 / 2) := by
    rw [o.circleBilliardTable_nextParam c e he hR hv, harc, ← ht]
    ring
  have hstep := o.circleCurve_step_third_eq c e he hR t
  rw [ht] at hstep
  have hnorm : ‖o.circleCurve c e R (circleEquilateralTriangle R s₀ k) -
      o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1))‖ = √3 * R := by
    simpa only [sub_add_cancel] using o.norm_sub_circleEquilateralTriangle c e he hR.le s₀ (k - 1)
  have hpos : √3 * R ≠ 0 := by positivity
  rw [hnorm, o.circleCurve_circleEquilateralTriangle_pred, hstep, inv_smul_smul₀ hpos, hparam,
    ← o.coe_circleBilliardTable c e R he hR,
    ← StrictConvexBilliardTable.nextTangential_def]
  exact o.circleBilliardTable_nextTangential c e he hR hv

private theorem circleCurve_circleRightTriangle_one_sub_zero (o : Orientation ℝ E (Fin 2))
    (c e : E) (R : ℝ) :
    o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
        o.circleCurve c e R (circleRightTriangle R 0) =
      R • (o.rightAngleRotation e - e) := by
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hs1 : circleRightTriangle R (0 + 1) = Real.pi * R / 2 := rfl
  rw [hs1, hs0, o.circleCurve_pi_mul_div_two, o.circleCurve_zero]
  module

/-- Consecutive vertices of `circleRightTriangle R` (`e ≠ 0`, `R ≠ 0`) are distinct. -/
theorem apply_add_one_ne_circleRightTriangle (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} {R : ℝ}
    (he : e ≠ 0) (hR : R ≠ 0) (k : ZMod 3) :
    o.circleCurve c e R (circleRightTriangle R (k + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R k) := by
  have hne10 : o.rightAngleRotation e ≠ e := fun h ↦ he <| by
    simpa [h] using o.inner_rightAngleRotation_self e
  have hne21 : c - R • e ≠ c + R • o.rightAngleRotation e := fun h ↦
    he <| inner_self_eq_zero.1 <| by
      have h' : -e = o.rightAngleRotation e :=
        smul_right_injective E hR (by simpa [sub_eq_add_neg, ← smul_neg] using h)
      have hin := o.inner_rightAngleRotation_self e
      rw [← h', inner_neg_left, neg_eq_zero] at hin
      exact hin
  have hne02 : c + R • e ≠ c - R • e := fun h ↦ by
    have h2R : (2 * R) • e = 0 := by
      calc
        (2 * R) • e = (c + R • e) - (c - R • e) := by module
        _ = 0 := sub_eq_zero.2 h
    exact mul_ne_zero two_ne_zero hR ((smul_eq_zero.1 h2R).resolve_right he)
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hs1 : circleRightTriangle R 1 = Real.pi * R / 2 := rfl
  have hs2 : circleRightTriangle R 2 = Real.pi * R := rfl
  have h01 : (0 : ZMod 3) + 1 = 1 := rfl
  have h12 : (1 : ZMod 3) + 1 = 2 := rfl
  have h20 : (2 : ZMod 3) + 1 = 0 := rfl
  have hk0 : o.circleCurve c e R (circleRightTriangle R ((0 : ZMod 3) + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 0) := by
    rw [h01, hs1, hs0, o.circleCurve_pi_mul_div_two, o.circleCurve_zero, ne_eq, add_right_inj,
      smul_right_inj hR]
    exact hne10
  have hk1 : o.circleCurve c e R (circleRightTriangle R ((1 : ZMod 3) + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 1) := by
    rw [h12, hs2, hs1, o.circleCurve_pi_mul, o.circleCurve_pi_mul_div_two]
    exact hne21
  have hk2 : o.circleCurve c e R (circleRightTriangle R ((2 : ZMod 3) + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 2) := by
    rw [h20, hs0, hs2, o.circleCurve_zero, o.circleCurve_pi_mul]
    exact hne02
  fin_cases k
  · exact hk0
  · exact hk1
  · exact hk2

/-- **Incoming inner product at angle `0` of the `0, π / 2, π` triangle.** At vertex `0` of
`circleRightTriangle R`, the incoming unit chord from angle `π` to angle `0` has inner product `0`
with the tangent `χ'(0)`. -/
theorem inner_incoming_circleRightTriangle_zero (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) :
    ⟪‖o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ = 0 := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [circleCurve]
  · have hs0 : circleRightTriangle R 0 = 0 := rfl
    have hs2 : circleRightTriangle R (0 - 1) = Real.pi * R := rfl
    have hdiff : o.circleCurve c e R 0 - o.circleCurve c e R (Real.pi * R) = (2 * R) • e := by
      rw [o.circleCurve_zero, o.circleCurve_pi_mul]
      module
    rw [hs0, hs2, hdiff, o.deriv_circleCurve_zero c e hR, smul_smul, real_inner_smul_left,
      o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero, mul_zero]

/-- **Outgoing inner product at angle `0` of the `0, π / 2, π` triangle.** At vertex `0` of
`circleRightTriangle R` (`R > 0`), the outgoing unit chord from angle `0` to angle `π / 2` has
inner product `1 / √2` with the unit tangent `χ'(0)`. -/
theorem inner_outgoing_circleRightTriangle_zero (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) :
    ⟪‖o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ = 1 / √2 := by
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hnorm_orth : ‖o.rightAngleRotation e - e‖ = √2 := by
    have h := norm_sub_eq_sqrt_iff_real_inner_eq_zero.mpr (o.inner_rightAngleRotation_self e)
    rw [LinearIsometryEquiv.norm_map, he] at h
    norm_num at h
    exact h
  have hnorm : ‖R • (o.rightAngleRotation e - e)‖ = R * √2 := by
    rw [norm_smul, hnorm_orth, Real.norm_of_nonneg hR.le]
  have hJe2 : ⟪o.rightAngleRotation e, o.rightAngleRotation e⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, he, one_pow]
  rw [o.circleCurve_circleRightTriangle_one_sub_zero, hs0, o.deriv_circleCurve_zero c e hR.ne',
    hnorm, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hR.ne', mul_one,
    real_inner_smul_left, inner_sub_left, hJe2, o.inner_rightAngleRotation_right,
    o.areaForm_apply_self]
  ring

/-- **Failure of the reflection law at angle `0` for the `0, π / 2, π` triangle.** Whenever `e ≠ 0`
and `R ≠ 0`, the incoming and outgoing unit-chord inner products at vertex `0` differ. -/
theorem incoming_ne_outgoing_circleRightTriangle_zero (o : Orientation ℝ E (Fin 2)) (c : E) {e : E}
    {R : ℝ} (he : e ≠ 0) (hR : R ≠ 0) :
    ⟪‖o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ ≠
    ⟪‖o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ := by
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hne : R • (o.rightAngleRotation e - e) ≠ 0 := by
    rw [← o.circleCurve_circleRightTriangle_one_sub_zero c e R]
    exact sub_ne_zero.2 (o.apply_add_one_ne_circleRightTriangle c he hR 0)
  have hJe2 : ⟪o.rightAngleRotation e, o.rightAngleRotation e⟫ = ‖e‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  rw [o.inner_incoming_circleRightTriangle_zero c e R,
    o.circleCurve_circleRightTriangle_one_sub_zero, hs0, o.deriv_circleCurve_zero c e hR,
    smul_smul, real_inner_smul_left, inner_sub_left, hJe2, o.inner_rightAngleRotation_right,
    o.areaForm_apply_self, neg_zero, sub_zero]
  exact (mul_ne_zero (mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hne)) hR)
    (pow_ne_zero 2 (norm_ne_zero_iff.2 he))).symm

/-- The `0, π / 2, π` inscribed triangle is not a local extremum of `inscribedPerimeter` on
`o.circleCurve c e R` (`e ≠ 0`, `R ≠ 0`). -/
theorem not_isLocalExtr_circleRightTriangle (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} {R : ℝ}
    (he : e ≠ 0) (hR : R ≠ 0) :
    ¬ IsLocalExtr (inscribedPerimeter (o.circleCurve c e R)) (circleRightTriangle R) := by
  intro hloc
  have hd : DifferentiableAt ℝ (o.circleCurve c e R) (circleRightTriangle R 0) :=
    (o.hasDerivAt_circleCurve c e hR _).differentiableAt
  have h20 : (0 : ZMod 3) - 1 = 2 := rfl
  have h21 : (2 : ZMod 3) + 1 = 0 := rfl
  have hne1 : o.circleCurve c e R (circleRightTriangle R 0) ≠
      o.circleCurve c e R (circleRightTriangle R (0 - 1)) := by
    rw [h20, ← h21]
    exact o.apply_add_one_ne_circleRightTriangle c he hR 2
  have hne2 : o.circleCurve c e R (circleRightTriangle R (0 + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 0) :=
    o.apply_add_one_ne_circleRightTriangle c he hR 0
  exact o.incoming_ne_outgoing_circleRightTriangle_zero c he hR
    (inner_eq_inner_of_isLocalExtr_inscribedPerimeter hloc hd hne1 hne2)

end Orientation
