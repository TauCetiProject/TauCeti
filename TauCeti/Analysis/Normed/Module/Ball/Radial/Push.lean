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
* `TauCeti.norm_radialPush`: its norm is the linear interpolation of the endpoint norms.
* `TauCeti.norm_le_norm_radialPush` and `TauCeti.norm_radialPush_le_one`: on the closed unit
  ball it does not decrease norms and stays in the ball.
* `TauCeti.radialPush_of_norm_eq_one`: it fixes the unit sphere.
* `TauCeti.norm_radialPush_one`: at the end it sends the shell `r ≤ ‖y‖` to the unit sphere.

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

theorem continuous_radialPush (hr : 0 ≤ r) : Continuous fun p : I × E ↦ radialPush r p.1 p.2 :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    continuous_snd).add <| (continuous_subtype_val.comp continuous_fst).smul <|
      ((lipschitzWith_radialRetraction (E := E) hr).continuous.comp continuous_snd).const_smul _

/-- The norm along `TauCeti.radialPush` is the linear interpolation between the initial
norm and the norm of the rescaled radial retraction. -/
@[simp]
theorem norm_radialPush (hr : 0 ≤ r) (t : I) :
    ‖radialPush r t y‖ = (1 - (t : ℝ)) * ‖y‖ + (t : ℝ) * (r⁻¹ * min ‖y‖ r) := by
  have ht := t.2.1
  rw [radialPush, SameRay.norm_add]
  · rw [norm_smul_of_nonneg (sub_nonneg.mpr t.2.2), norm_smul_of_nonneg t.2.1,
      norm_smul_of_nonneg (inv_nonneg.mpr hr), norm_radialRetraction hr]
  · rw [radialRetraction_def, smul_smul, smul_smul]
    exact sameRay_smul_smul_of_mul_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (by positivity))

/-- On the closed unit ball, `TauCeti.radialPush` does not decrease norms. -/
theorem norm_le_norm_radialPush (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ ≤ 1) :
    ‖y‖ ≤ ‖radialPush r t y‖ := by
  have h : ‖y‖ ≤ r⁻¹ * min ‖y‖ r := by
    rw [inv_mul_eq_div, le_div_iff₀ hr, le_min_iff]
    constructor <;> nlinarith [norm_nonneg y]
  rw [norm_radialPush hr.le]
  nlinarith [t.2.1]

/-- For every nonnegative radius, `TauCeti.radialPush` maps the closed unit ball into itself. -/
theorem norm_radialPush_le_one (hr : 0 ≤ r) (t : I) (hy : ‖y‖ ≤ 1) :
    ‖radialPush r t y‖ ≤ 1 := by
  have h : r⁻¹ * min ‖y‖ r ≤ 1 := by
    rcases hr.eq_or_lt with rfl | hr
    · simp
    · rw [inv_mul_le_iff₀ hr, mul_one]
      exact min_le_right _ _
  rw [norm_radialPush hr]
  nlinarith [t.2.1, t.2.2, norm_nonneg y]

/-- `TauCeti.radialPush` fixes the unit sphere. -/
theorem radialPush_of_norm_eq_one (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ = 1) :
    radialPush r t y = y := by
  simp [radialPush, radialRetraction_of_le_norm (hr1.trans_eq hy.symm), hy, hr.ne',
    ← add_smul]

/-- At the end, `TauCeti.radialPush r` sends the shell `r ≤ ‖y‖` to the unit sphere. -/
theorem norm_radialPush_one (hr : 0 < r) (hy : r ≤ ‖y‖) : ‖radialPush r 1 y‖ = 1 := by
  rw [norm_radialPush hr.le]
  simp [min_eq_right hy, hr.ne']

end TauCeti
