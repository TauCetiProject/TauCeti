/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Pushing a shell of the closed unit ball onto the unit sphere

In a real normed space and for a radius `0 < r ≤ 1`, the rescaled radial retraction
`r⁻¹ • TauCeti.radialRetraction r` maps the closed unit ball onto itself: it expands the closed
ball of radius `r` linearly onto the closed unit ball and sends every point of the shell
`r ≤ ‖y‖ ≤ 1` to the unit sphere along its ray.  The straight-line homotopy
`TauCeti.radialPush r` from the identity to it stays inside the closed unit ball, never decreases
norms there, and fixes the unit sphere at all times.

This is the deformation which shows that the inclusion of the pair (closed ball, unit sphere) into
the pair (closed ball, shell) is a homotopy equivalence of pairs, and similarly, cell by cell, that
the skeleta of a CW complex form good pairs.

## Main declarations

* `TauCeti.radialPush`: the straight-line homotopy from the identity to
  `r⁻¹ • TauCeti.radialRetraction r`.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} {y : E}

/-- The straight-line homotopy from the identity to the rescaled radial retraction
`r⁻¹ • TauCeti.radialRetraction r`, at time `t`.  For `0 < r ≤ 1` it moves a point `y` of the
closed unit ball along its ray, from `y` towards `r⁻¹ • y` if `‖y‖ ≤ r` and towards `‖y‖⁻¹ • y`
otherwise. -/
noncomputable def radialPush (r : ℝ) (t : I) (y : E) : E :=
  (1 - (t : ℝ)) • y + (t : ℝ) • r⁻¹ • radialRetraction r y

@[simp]
theorem radialPush_zero (r : ℝ) (y : E) : radialPush r 0 y = y := by
  simp [radialPush]

@[simp]
theorem radialPush_one (r : ℝ) (y : E) : radialPush r 1 y = r⁻¹ • radialRetraction r y := by
  simp [radialPush]

theorem continuous_radialPush (hr : 0 ≤ r) : Continuous fun p : I × E ↦ radialPush r p.1 p.2 :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    continuous_snd).add <| (continuous_subtype_val.comp continuous_fst).smul <|
      ((lipschitzWith_radialRetraction (E := E) hr).continuous.comp continuous_snd).const_smul _

/-- The scalar by which `TauCeti.radialPush r t` multiplies `y`. -/
private noncomputable def radialFactor (r : ℝ) (t : I) (y : E) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * (max ‖y‖ r)⁻¹

omit [NormedSpace ℝ E] in
private lemma max_norm_pos (hr : 0 < r) (y : E) : 0 < max ‖y‖ r :=
  hr.trans_le (le_max_right _ _)

private lemma radialPush_eq_radialFactor_smul (hr : 0 < r) (t : I) (y : E) :
    radialPush r t y = radialFactor r t y • y := by
  have hret : r⁻¹ • radialRetraction r y = (max ‖y‖ r)⁻¹ • y := by
    rcases le_total ‖y‖ r with h | h
    · rw [radialRetraction_of_norm_le h, max_eq_right h]
    · rw [radialRetraction_of_le_norm h, max_eq_left h, smul_smul, div_eq_mul_inv,
        inv_mul_cancel_left₀ hr.ne']
  rw [radialPush, hret, smul_smul, ← add_smul]
  rfl

omit [NormedSpace ℝ E] in
private lemma one_le_radialFactor (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ ≤ 1) :
    1 ≤ radialFactor r t y := by
  have h : 1 ≤ (max ‖y‖ r)⁻¹ := (one_le_inv₀ (max_norm_pos hr y)).2 (max_le hy hr1)
  have ht := t.2.1
  unfold radialFactor
  nlinarith

private lemma norm_radialPush (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ ≤ 1) :
    ‖radialPush r t y‖ = radialFactor r t y * ‖y‖ := by
  rw [radialPush_eq_radialFactor_smul hr, norm_smul,
    Real.norm_of_nonneg (by linarith [one_le_radialFactor hr hr1 t hy])]

/-- On the closed unit ball, `TauCeti.radialPush` does not decrease norms. -/
theorem norm_le_norm_radialPush (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ ≤ 1) :
    ‖y‖ ≤ ‖radialPush r t y‖ := by
  rw [norm_radialPush hr hr1 t hy]
  exact le_mul_of_one_le_left (norm_nonneg y) (one_le_radialFactor hr hr1 t hy)

/-- `TauCeti.radialPush` maps the closed unit ball into itself. -/
theorem norm_radialPush_le_one (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ ≤ 1) :
    ‖radialPush r t y‖ ≤ 1 := by
  rw [norm_radialPush hr hr1 t hy, radialFactor, add_mul, mul_assoc]
  have h : (max ‖y‖ r)⁻¹ * ‖y‖ ≤ 1 := by
    rw [inv_mul_le_iff₀ (max_norm_pos hr y), mul_one]
    exact le_max_left _ _
  have ht := t.2.1
  have ht' := t.2.2
  nlinarith [norm_nonneg y]

/-- `TauCeti.radialPush` fixes the unit sphere. -/
theorem radialPush_of_norm_eq_one (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (hy : ‖y‖ = 1) :
    radialPush r t y = y := by
  rw [radialPush_eq_radialFactor_smul hr]
  have h : max ‖y‖ r = 1 := by rw [hy, max_eq_left hr1]
  simp [radialFactor, h]

/-- At the end, `TauCeti.radialPush r` sends the shell `r ≤ ‖y‖` to the unit sphere. -/
theorem norm_radialPush_one (hr : 0 < r) (hy : r ≤ ‖y‖) : ‖radialPush r 1 y‖ = 1 := by
  rw [radialPush_one, norm_smul, norm_radialRetraction hr.le, min_eq_right hy, norm_inv,
    Real.norm_of_nonneg hr.le, inv_mul_cancel₀ hr.ne']

end TauCeti
