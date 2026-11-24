/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Pushing a shell of the closed unit ball onto the unit sphere

In a real seminormed space and for a radius `0 < r ≤ 1`, the rescaled radial retraction
`r⁻¹ • TauCeti.radialRetraction r` maps the closed unit ball into itself and sends every point
of the shell `r ≤ ‖y‖ ≤ 1` to the unit sphere along its ray. The straight-line homotopy
`TauCeti.radialPush r` from the identity to it stays inside the closed unit ball, never decreases
norms there, and fixes the unit sphere at all times.

Points of positive norm at most `r` end at `r⁻¹ • y`. A vector of seminorm zero instead ends at
zero, and at time `t` its image is `(1 - (t : ℝ)) • y`.

In a normed space this is the deformation which shows that the inclusion of the pair (closed ball,
unit sphere) into the pair (closed ball, shell) is a homotopy equivalence of pairs, and similarly,
cell by cell, that the skeleta of a CW complex form good pairs.

## Main declarations

* `TauCeti.radialPush`: the straight-line homotopy from the identity to
  `r⁻¹ • TauCeti.radialRetraction r`.
* `TauCeti.radialPush_eq_smul`: it rescales each vector along its ray, by the factor
  `TauCeti.radialPushScale` depending only on the time and the norm.
* `TauCeti.radialPushScale_def`, `TauCeti.radialPushScale_zero`, `TauCeti.radialPushScale_one`
  and `TauCeti.radialPushScale_one_right`: its formula, its values at times zero and one, and its
  value at norm one.
* `TauCeti.radialPushScale_nonneg`, `TauCeti.radialPushScale_pos` and `TauCeti.radialPushScale_le`:
  bounds on this factor, and `TauCeti.continuousAt_radialPushScale`: its continuity off norm zero.
* `TauCeti.norm_radialPush`: its norm is the linear interpolation of the endpoint norms.
* `TauCeti.norm_le_norm_radialPush` and `TauCeti.norm_radialPush_le_one`: on the closed unit
  ball it does not decrease norms and stays in the ball.
* `TauCeti.radialPush_of_le_norm`: outside the ball of radius `r` it scales by the interpolation
  from `1` to `‖y‖⁻¹`, and `TauCeti.radialPush_one_of_le_norm`: it ends there at the radial
  projection to the unit sphere.
* `TauCeti.inv_norm_smul_radialPush`: for `r > 0` it moves every vector along its ray.
* `TauCeti.radialPush_of_norm_eq_one`: it fixes the unit sphere.
* `TauCeti.norm_radialPush_one`: at the end it sends the shell `r ≤ ‖y‖` to the unit sphere.
* `TauCeti.radialPush_nonneg`, `TauCeti.radialPush_le_one`, `TauCeti.le_radialPush` and
  `TauCeti.radialPush_one_eq_one`: the same facts on the real line, without norms, and
  `TauCeti.radialPush_eq_radialPushScale_mul`: there it multiplies by the rescaling factor.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, the discussion of good pairs before Proposition 2.22.
-/

public section

open unitInterval

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} {y : E}

/-- The straight-line homotopy from the identity to the rescaled radial retraction
`r⁻¹ • TauCeti.radialRetraction r`, at time `t`. For `0 < r ≤ 1` it moves a positive-norm
point `y` of the closed unit ball along its ray, from `y` towards `r⁻¹ • y` if `‖y‖ ≤ r` and
towards `‖y‖⁻¹ • y` otherwise. If `‖y‖ = 0`, its value is `(1 - (t : ℝ)) • y`. -/
noncomputable def radialPush (r : ℝ) (t : I) (y : E) : E :=
  (1 - (t : ℝ)) • y + (t : ℝ) • r⁻¹ • radialRetraction r y

@[simp]
theorem radialPush_zero (r : ℝ) (y : E) : radialPush r 0 y = y := by
  simp [radialPush]

@[simp]
theorem radialPush_one (r : ℝ) (y : E) : radialPush r 1 y = r⁻¹ • radialRetraction r y := by
  simp [radialPush]

/-- The factor by which `TauCeti.radialPush r` at time `t` rescales a vector of norm `a`. -/
noncomputable def radialPushScale (r : ℝ) (t : I) (a : ℝ) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) * (r⁻¹ * min 1 (r / a))

/-- The defining formula of the rescaling factor of `TauCeti.radialPush`. -/
theorem radialPushScale_def (r : ℝ) (t : I) (a : ℝ) :
    radialPushScale r t a = 1 - (t : ℝ) + (t : ℝ) * (r⁻¹ * min 1 (r / a)) :=
  (rfl)

/-- At time zero the radial push does not rescale. -/
@[simp]
theorem radialPushScale_zero (r a : ℝ) : radialPushScale r 0 a = 1 := by
  simp [radialPushScale]

/-- At time one the radial push rescales by the factor of `r⁻¹ • TauCeti.radialRetraction r`. -/
@[simp]
theorem radialPushScale_one (r a : ℝ) : radialPushScale r 1 a = r⁻¹ * min 1 (r / a) := by
  simp [radialPushScale]

/-- The radial push rescales `y` along its ray, by a factor depending only on `t` and `‖y‖`. -/
theorem radialPush_eq_smul (r : ℝ) (t : I) (y : E) :
    radialPush r t y = radialPushScale r t ‖y‖ • y := by
  rw [radialPushScale, radialPush, radialRetraction_def, smul_smul, smul_smul, ← mul_assoc,
    ← add_smul]

/-- The rescaling factor of `TauCeti.radialPush` is nonnegative, for every radius. -/
theorem radialPushScale_nonneg (r : ℝ) (t : I) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ radialPushScale r t a := by
  have hk : 0 ≤ r⁻¹ * min 1 (r / a) := by
    rcases le_or_gt 0 r with hr | hr
    · exact mul_nonneg (inv_nonneg.2 hr) (le_min zero_le_one (div_nonneg hr ha))
    · exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 hr.le)
        ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg hr.le ha))
  rw [radialPushScale]
  nlinarith [t.property.1, t.property.2, mul_nonneg t.property.1 hk]

/-- For `r > 0` the rescaling factor of `TauCeti.radialPush` is positive on positive norms. -/
theorem radialPushScale_pos (hr : 0 < r) (t : I) {a : ℝ} (ha : 0 < a) :
    0 < radialPushScale r t a := by
  have hk : 0 < r⁻¹ * min 1 (r / a) := by positivity
  rw [radialPushScale]
  rcases t.property.1.eq_or_lt with h | h
  · simp [← h]
  · nlinarith [mul_pos h hk, t.property.2]

/-- For `r > 0` the rescaling factor of `TauCeti.radialPush` is at most `1 + r⁻¹`. -/
theorem radialPushScale_le (hr : 0 < r) (t : I) (a : ℝ) : radialPushScale r t a ≤ 1 + r⁻¹ := by
  have hm : r⁻¹ * min 1 (r / a) ≤ r⁻¹ :=
    mul_le_of_le_one_right (inv_nonneg.2 hr.le) (min_le_left _ _)
  rw [radialPushScale]
  nlinarith [t.property.1, t.property.2, inv_nonneg.2 hr.le]

/-- The rescaling factor of `TauCeti.radialPush` is continuous in the time and the norm, away from
norm zero. -/
theorem continuousAt_radialPushScale (r : ℝ) {p : I × ℝ} (hp : p.2 ≠ 0) :
    ContinuousAt (fun q : I × ℝ ↦ radialPushScale r q.1 q.2) p := by
  have ht : ContinuousAt (fun q : I × ℝ ↦ (q.1 : ℝ)) p := by fun_prop
  exact (continuousAt_const.sub ht).add (ht.mul (continuousAt_const.mul
    (continuousAt_const.min (continuousAt_const.div continuousAt_snd hp))))

/-- For `0 < r ≤ 1` the radial push does not rescale vectors of norm one: the factor is `1` when
its norm argument is `1`. -/
theorem radialPushScale_one_right (hr : 0 < r) (hr1 : r ≤ 1) (t : I) :
    radialPushScale r t 1 = 1 := by
  simp [radialPushScale, min_eq_right hr1, hr.ne']

/-- On a vector of seminorm zero, the radial push contracts linearly to zero. -/
@[simp]
theorem radialPush_of_norm_eq_zero (hy : ‖y‖ = 0) (t : I) :
    radialPush r t y = (1 - (t : ℝ)) • y := by
  simp [radialPush, hy]

/-- On a vector of positive norm at most `r`, the radial push scales by the linear
interpolation from `1` to `r⁻¹`. -/
@[simp]
theorem radialPush_of_norm_pos_of_norm_le (hy0 : 0 < ‖y‖) (hyr : ‖y‖ ≤ r) (t : I) :
    radialPush r t y = (1 - (t : ℝ) + (t : ℝ) * r⁻¹) • y := by
  simp [radialPush, hy0, hyr, smul_smul, ← add_smul]

/-- On a vector of norm at least `r > 0`, the radial push scales by the linear interpolation
from `1` to `‖y‖⁻¹`. -/
theorem radialPush_of_le_norm (hr : 0 < r) (hy : r ≤ ‖y‖) (t : I) :
    radialPush r t y = (1 - (t : ℝ) + (t : ℝ) * ‖y‖⁻¹) • y := by
  rw [radialPush, radialRetraction_of_le_norm hy, smul_smul, smul_smul, ← add_smul]
  congr 1
  field_simp

/-- At the end, the radial push sends a vector of norm at least `r > 0` to its radial projection
on the unit sphere. -/
theorem radialPush_one_of_le_norm (hr : 0 < r) (hy : r ≤ ‖y‖) : radialPush r 1 y = ‖y‖⁻¹ • y := by
  simp [radialPush_of_le_norm hr hy]

/-- For `r > 0` the radial push moves every vector along its ray: its radial projection does not
change. -/
theorem inv_norm_smul_radialPush (hr : 0 < r) (t : I) :
    ‖radialPush r t y‖⁻¹ • radialPush r t y = ‖y‖⁻¹ • y := by
  rcases (norm_nonneg y).eq_or_lt' with hy | hy
  · simp [norm_smul, hy]
  have hc := radialPushScale_pos hr t hy
  rw [radialPush_eq_smul, norm_smul, Real.norm_of_nonneg hc.le, smul_smul, mul_inv,
    mul_right_comm, inv_mul_cancel₀ hc.ne', one_mul]

theorem continuous_radialPush (hr : 0 ≤ r) : Continuous fun p : I × E ↦ radialPush r p.1 p.2 :=
  ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul
    continuous_snd).add <| (continuous_subtypeVal.comp continuous_fst).smul <|
      ((lipschitzWith_radialRetraction (E := E) hr).continuous.comp continuous_snd).const_smul _

/-- The norm along `TauCeti.radialPush` is the linear interpolation between the initial
norm and the norm of the rescaled radial retraction. -/
@[simp]
theorem norm_radialPush (hr : 0 ≤ r) (t : I) :
    ‖radialPush r t y‖ = (1 - (t : ℝ)) * ‖y‖ + (t : ℝ) * (r⁻¹ * min ‖y‖ r) := by
  have ht := t.property.1
  rw [radialPush, SameRay.norm_add]
  · rw [norm_smul_of_nonneg (sub_nonneg.mpr t.property.2), norm_smul_of_nonneg t.property.1,
      norm_smul_of_nonneg (inv_nonneg.mpr hr), norm_radialRetraction hr]
  · rw [radialRetraction_def, smul_smul, smul_smul]
    exact sameRay_smul_smul_of_mul_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (by positivity))

/-- On the closed unit ball, `TauCeti.radialPush` does not decrease norms. -/
theorem norm_le_norm_radialPush (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ ≤ 1) :
    ‖y‖ ≤ ‖radialPush r t y‖ := by
  have h : ‖y‖ ≤ r⁻¹ * min ‖y‖ r := by
    rw [inv_mul_eq_div, le_div_iff₀ hr, le_min_iff]
    constructor <;> nlinarith [norm_nonneg y]
  rw [norm_radialPush hr.le]
  nlinarith [t.property.1]

/-- For every radius, `TauCeti.radialPush` maps the closed unit ball into itself. -/
theorem norm_radialPush_le_one (t : I) (hy : ‖y‖ ≤ 1) : ‖radialPush r t y‖ ≤ 1 := by
  rcases le_or_gt 0 r with hr | hr
  · have h : r⁻¹ * min ‖y‖ r ≤ 1 := by
      rcases hr.eq_or_lt with rfl | hr
      · simp
      · rw [inv_mul_le_iff₀ hr, mul_one]
        exact min_le_right _ _
    rw [norm_radialPush hr]
    nlinarith [t.property.1, t.property.2, norm_nonneg y]
  · rcases eq_or_ne ‖y‖ 0 with hy0 | hy0
    · rw [radialPush_of_norm_eq_zero hy0, norm_smul_of_nonneg (sub_nonneg.mpr t.property.2), hy0]
      simp
    · have hy0' : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) hy0.symm
      have hpush : r⁻¹ • radialRetraction r y = ‖y‖⁻¹ • y := by
        rw [radialRetraction_of_le_norm (hr.le.trans (norm_nonneg y)), smul_smul]
        congr 1
        have := hr.ne
        field_simp
      rw [radialPush, hpush]
      calc ‖(1 - (t : ℝ)) • y + (t : ℝ) • ‖y‖⁻¹ • y‖
          ≤ ‖(1 - (t : ℝ)) • y‖ + ‖(t : ℝ) • ‖y‖⁻¹ • y‖ := norm_add_le _ _
        _ = (1 - (t : ℝ)) * ‖y‖ + (t : ℝ) := by
          rw [norm_smul_of_nonneg (sub_nonneg.mpr t.property.2), norm_smul_of_nonneg t.property.1,
            norm_smul_of_nonneg (inv_nonneg.mpr hy0'.le), inv_mul_cancel₀ hy0, mul_one]
        _ ≤ 1 := by nlinarith [t.property.1, t.property.2]

/-- `TauCeti.radialPush` fixes the unit sphere. -/
theorem radialPush_of_norm_eq_one (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ = 1) :
    radialPush r t y = y := by
  simp [radialPush, radialRetraction_of_le_norm (hr1.trans_eq hy.symm), hy, hr.ne',
    ← add_smul]

/-- At the end, `TauCeti.radialPush r` sends the shell `r ≤ ‖y‖` to the unit sphere. -/
theorem norm_radialPush_one (hr : 0 < r) (hy : r ≤ ‖y‖) : ‖radialPush r 1 y‖ = 1 := by
  rw [norm_radialPush hr.le]
  simp [min_eq_right hy, hr.ne']

/-! ### The radial push on the real line -/

section Real

variable {x : ℝ}

/-- On the real line, `TauCeti.radialPush` keeps nonnegative numbers nonnegative. -/
theorem radialPush_nonneg (t : I) (hx : 0 ≤ x) : 0 ≤ radialPush r t x := by
  rw [radialPush_eq_smul, smul_eq_mul]
  exact mul_nonneg (radialPushScale_nonneg r t (norm_nonneg x)) hx

/-- On the real line, `TauCeti.radialPush` keeps numbers at most `1` at most `1`. -/
theorem radialPush_le_one (t : I) (hx : x ≤ 1) : radialPush r t x ≤ 1 := by
  rcases le_total x 0 with hx0 | hx0
  · rw [radialPush_eq_smul, smul_eq_mul]
    nlinarith [radialPushScale_nonneg r t (norm_nonneg x)]
  · exact (Real.le_norm_self _).trans
      (norm_radialPush_le_one t (by rwa [Real.norm_of_nonneg hx0]))

/-- On `[0, 1]`, `TauCeti.radialPush` does not decrease real numbers. -/
theorem le_radialPush (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ radialPush r t x := by
  have h := norm_le_norm_radialPush hr hr1 t (y := x) (by rwa [Real.norm_of_nonneg hx])
  rwa [Real.norm_of_nonneg hx, Real.norm_of_nonneg (radialPush_nonneg t hx)] at h

/-- On nonnegative real numbers, `TauCeti.radialPush` multiplies by its rescaling factor. -/
theorem radialPush_eq_radialPushScale_mul (t : I) (hx : 0 ≤ x) :
    radialPush r t x = radialPushScale r t x * x := by
  rw [radialPush_eq_smul, smul_eq_mul, Real.norm_of_nonneg hx]

/-- At the end, `TauCeti.radialPush r` sends every real number at least `r > 0` to `1`. -/
theorem radialPush_one_eq_one (hr : 0 < r) (hx : r ≤ x) : radialPush r 1 x = 1 := by
  have hx0 : 0 < x := hr.trans_le hx
  have hnx : ‖x‖ = x := Real.norm_of_nonneg hx0.le
  rw [radialPush_one_of_le_norm hr (by rwa [hnx]), hnx, smul_eq_mul, inv_mul_cancel₀ hx0.ne']

end Real

end TauCeti
