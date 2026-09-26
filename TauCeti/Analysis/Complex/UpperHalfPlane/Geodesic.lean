/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation

/-!
# Geodesic lines in the upper half-plane, transported from the imaginary axis

Mathlib's `UpperHalfPlane.isometry_vertical_line` already exhibits the imaginary axis, in its
upward unit-speed parametrisation `t ↦ mk ⟨0, exp t⟩ _`, as a geodesic line, and Tau Ceti's
`IsIsometricSMul PSL(2, ℝ) ℍ` (`ProperAction.lean`) already gives the isometric action of the
group Fuchsian groups are subgroups of. The first part of this file composes the two: the
`PSL(2, ℝ)`-translate of the imaginary axis by any `g` is again a geodesic line, and every one of
these is unit-speed (`isometry_geodesicLine`), hence injective (`geodesicLine_injective`) and at
explicit distance `|s - t|` between its parameters (`dist_geodesicLine`).

This is the transport step behind the classical description of hyperbolic geodesics in `ℍ` as
vertical lines and semicircles centred on the real axis: as a *set*, the image of the map
`geodesicLine g` is the `g`-translate of the imaginary axis, which is a vertical line when the
representing matrix's lower-left entry `g 1 0` or lower-right entry `g 1 1` is `0` (equivalently,
`g` sends one of the imaginary axis's two boundary points, `0` and the point at infinity, to the
point at infinity) and a semicircle centred on the real axis otherwise. That case split is not
proved here.

The second part is two-point transitivity: any two points `z`, `w` lie on a common geodesic line,
with `z` at parameter `0` and `w` at parameter `dist z w`
(`exists_geodesicLine_zero_eq_and_dist_eq`). Transitivity of the action puts `z` at `I`; a
rotation about `I` (`Rotation.lean`) then moves `w` onto the imaginary axis, which is the geodesic
line of the identity (`mem_range_geodesicLine_one_iff`), and if `w` lands below `I` the rotation
by `π/2` reverses the axis (`geodesicLine_rotation_pi_div_two`).

## Main declarations

* `TauCeti.UpperHalfPlane.geodesicLine g` — the imaginary axis in its upward unit-speed
  parametrisation, moved by `g`: the map `t ↦ g • UpperHalfPlane.mk ⟨0, exp t⟩ _`.
  `geodesicLine_one_apply` and `geodesicLine_zero` give its value at `g = 1` and at `t = 0`.
* `TauCeti.UpperHalfPlane.isometry_geodesicLine` — `geodesicLine g` is an isometric embedding
  of `ℝ`, hence injective (`geodesicLine_injective`).
* `TauCeti.UpperHalfPlane.dist_geodesicLine` — the distance between two of its points is
  `|s - t|`.
* `TauCeti.UpperHalfPlane.smul_geodesicLine` — further translating a geodesic line by `h` gives
  the geodesic line of `h * g`, pointwise; `TauCeti.UpperHalfPlane.smul_range_geodesicLine` is
  the same fact at the level of the line as a set, so these lines are permuted, not merely
  mapped into each other, by the `PSL(2, ℝ)`-action.
* `TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq` — a geodesic line through any prescribed
  point of `ℍ`.
* `TauCeti.UpperHalfPlane.mem_range_geodesicLine_one_iff` — the geodesic line of the identity
  is the imaginary axis (`exists_geodesicLine_one_eq_iff` is its simp-normal form);
  `geodesicLine_rotation_pi_div_two` reverses its parametrisation.
* `TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq_and_dist_eq` — two-point transitivity:
  a geodesic line with `z` at parameter `0` and `w` at parameter `dist z w`, for any `z`, `w`;
  `exists_mem_range_geodesicLine_and_mem_range` is the same at the level of the line as a set.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-- The geodesic line obtained by moving the (upward, unit-speed) imaginary axis by `g`. -/
def geodesicLine (g : PSL(2, ℝ)) (t : ℝ) : ℍ :=
  g • UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)

theorem geodesicLine_def (g : PSL(2, ℝ)) (t : ℝ) :
    geodesicLine g t = g • UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t) := by
  rfl

/-- The geodesic line of the identity is the upward unit-speed imaginary axis. -/
theorem geodesicLine_one_apply (t : ℝ) :
    geodesicLine (1 : PSL(2, ℝ)) t = UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t) := by
  simp [geodesicLine_def]

theorem isometry_geodesicLine (g : PSL(2, ℝ)) : Isometry (geodesicLine g) :=
  (isometry_smul ℍ g).comp (UpperHalfPlane.isometry_vertical_line 0)

theorem geodesicLine_injective (g : PSL(2, ℝ)) : Function.Injective (geodesicLine g) :=
  (isometry_geodesicLine g).injective

@[simp]
theorem dist_geodesicLine (g : PSL(2, ℝ)) (s t : ℝ) :
    dist (geodesicLine g s) (geodesicLine g t) = |s - t| := by
  rw [(isometry_geodesicLine g).dist_eq, Real.dist_eq]

theorem geodesicLine_zero (g : PSL(2, ℝ)) : geodesicLine g 0 = g • UpperHalfPlane.I := by
  rw [geodesicLine_def]
  congr 1
  simp [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_I, Complex.ext_iff]

/-- Translating a geodesic line by `h` gives the geodesic line of `h * g`, pointwise. -/
@[simp]
theorem smul_geodesicLine (h g : PSL(2, ℝ)) (t : ℝ) :
    h • geodesicLine g t = geodesicLine (h * g) t := by
  simp [geodesicLine_def, mul_smul]

/-- The same fact as `smul_geodesicLine`, at the level of the line as a set: the `PSL(2, ℝ)`-action
permutes these lines rather than merely mapping into their union. -/
@[simp]
theorem smul_range_geodesicLine (h g : PSL(2, ℝ)) :
    h • Set.range (geodesicLine g) = Set.range (geodesicLine (h * g)) := by
  rw [Set.smul_set_range]
  simp [smul_geodesicLine]

/-- A geodesic line through any prescribed point, at its own parameter `0`. -/
theorem exists_geodesicLine_zero_eq (z : ℍ) : ∃ g : PSL(2, ℝ), geodesicLine g 0 = z := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) UpperHalfPlane.I z
  exact ⟨g, by rw [geodesicLine_zero, hg]⟩

/-- The rotation by `π/2` reverses the parametrised imaginary axis. -/
@[simp]
theorem geodesicLine_rotation_pi_div_two (t : ℝ) :
    geodesicLine (↑(rotation (Real.pi / 2)) : PSL(2, ℝ)) t = geodesicLine 1 (-t) := by
  ext
  rw [geodesicLine_def, geodesicLine_one_apply, UpperHalfPlane.pslMk_smul, rotation_pi_div_two_smul,
    UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Complex.ext_iff]
  simp [Real.exp_neg, Real.exp_ne_zero]

/-- The geodesic line of the identity is the imaginary axis. The simp-normal form is
`exists_geodesicLine_one_eq_iff`, since `simp` unfolds `Set.range` membership. -/
theorem mem_range_geodesicLine_one_iff {u : ℍ} : u ∈ Set.range (geodesicLine 1) ↔ u.re = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp [geodesicLine_one_apply]
  · intro hu
    refine ⟨Real.log u.im, ?_⟩
    ext
    rw [geodesicLine_one_apply, UpperHalfPlane.coe_mk, Complex.ext_iff]
    simp [coe_re, coe_im, hu, Real.exp_log u.im_pos]

/-- `mem_range_geodesicLine_one_iff` in simp-normal form: a point is on the geodesic line of the
identity exactly when it is on the imaginary axis. -/
@[simp]
theorem exists_geodesicLine_one_eq_iff {u : ℍ} : (∃ t, geodesicLine 1 t = u) ↔ u.re = 0 :=
  mem_range_geodesicLine_one_iff

/-- Any two points `z`, `w` lie on a common geodesic line, `z` at parameter `0` and `w` at a
nonnegative parameter; the parameter is identified as `dist z w` in
`exists_geodesicLine_zero_eq_and_dist_eq`. -/
private theorem exists_nonneg_geodesicLine_zero_eq_and_apply_eq (z w : ℍ) :
    ∃ g : PSL(2, ℝ), ∃ t : ℝ, 0 ≤ t ∧ geodesicLine g 0 = z ∧ geodesicLine g t = w := by
  obtain ⟨h, hz⟩ := MulAction.exists_smul_eq PSL(2, ℝ) z UpperHalfPlane.I
  obtain ⟨θ, -, hθ⟩ := exists_rotation_smul_re_eq_zero (h • w)
  -- `k` moves `z` to `I` and `w` onto the imaginary axis, at some parameter `t`
  set k : PSL(2, ℝ) := (↑(rotation θ) : PSL(2, ℝ)) * h with hk
  have hkz : k • z = UpperHalfPlane.I := by
    rw [hk, mul_smul, hz, UpperHalfPlane.pslMk_smul, rotation_smul_I]
  have hkw : (k • w).re = 0 := by
    rw [hk, mul_smul, UpperHalfPlane.pslMk_smul]
    exact hθ
  obtain ⟨t, ht⟩ := mem_range_geodesicLine_one_iff.2 hkw
  rcases le_or_gt 0 t with ht0 | ht0
  · refine ⟨k⁻¹, t, ht0, ?_, ?_⟩
    · rw [geodesicLine_zero, ← hkz, inv_smul_smul]
    · rw [← mul_one k⁻¹, ← smul_geodesicLine, ht, inv_smul_smul]
  -- if `w` landed below `I`, reverse the axis by the rotation by `π/2` first
  · refine ⟨k⁻¹ * ↑(rotation (Real.pi / 2)), -t, by linarith, ?_, ?_⟩
    · rw [geodesicLine_zero, mul_smul, UpperHalfPlane.pslMk_smul, rotation_smul_I, ← hkz,
        inv_smul_smul]
    · rw [← smul_geodesicLine, geodesicLine_rotation_pi_div_two, neg_neg, ht, inv_smul_smul]

/-- **Two-point transitivity on parametrised geodesic lines.** Any two points `z`, `w` lie on a
common geodesic line, with `z` at parameter `0` and `w` at parameter `dist z w`. -/
theorem exists_geodesicLine_zero_eq_and_dist_eq (z w : ℍ) :
    ∃ g : PSL(2, ℝ), geodesicLine g 0 = z ∧ geodesicLine g (dist z w) = w := by
  obtain ⟨g, t, ht, hz, hw⟩ := exists_nonneg_geodesicLine_zero_eq_and_apply_eq z w
  refine ⟨g, hz, ?_⟩
  rw [← hz, ← hw, dist_geodesicLine, zero_sub, abs_neg, abs_of_nonneg ht]

/-- Any two points lie on a common geodesic line. -/
theorem exists_mem_range_geodesicLine_and_mem_range (z w : ℍ) :
    ∃ g : PSL(2, ℝ), z ∈ Set.range (geodesicLine g) ∧ w ∈ Set.range (geodesicLine g) := by
  obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  exact ⟨g, ⟨0, hz⟩, ⟨dist z w, hw⟩⟩

end TauCeti.UpperHalfPlane
