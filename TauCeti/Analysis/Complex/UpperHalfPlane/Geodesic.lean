/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation

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
line of the identity (`range_geodesicLine_one`), and if `w` lands below `I` the involution `pslS`
reverses the axis (`geodesicLine_mul_pslS`).

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
* `TauCeti.UpperHalfPlane.range_geodesicLine_one` and `TauCeti.UpperHalfPlane.range_geodesicLine`
  — every geodesic line, as a set, is a `g`-translate of the imaginary axis `{z | z.re = 0}`.
* `TauCeti.UpperHalfPlane.mem_range_geodesicLine_iff` — membership test for a geodesic line,
  without unfolding the smul-image.
* `TauCeti.UpperHalfPlane.geodesicLine_mul_pslS` — multiplying the representative by `pslS`
  reverses the parametrisation of a geodesic line; `range_geodesicLine_mul_pslS` is the same fact
  at the level of the line as a set, which is unchanged.
* `TauCeti.UpperHalfPlane.geodesicLine_mul_dilation` — multiplying the representative by the
  dilation `Matrix.SpecialLinearGroup.dilation s` shifts the parameter by `s`;
  `range_geodesicLine_mul_dilation` is the same fact at the level of the line as a set, which is
  unchanged. `geodesicLine_one_eq_dilation_smul_I` is the underlying description of the imaginary
  axis as the orbit of `I` under the dilations.
* `TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq_and_dist_eq` — two-point transitivity:
  a geodesic line with `z` at parameter `0` and `w` at parameter `dist z w`, for any `z`, `w`;
  `exists_mem_range_geodesicLine_and_mem_range` is the same at the level of the line as a set.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-! ### Geodesic lines as translates of the imaginary axis -/

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

/-- The geodesic line of the identity, as a set, is the imaginary axis `{z | z.re = 0}`. -/
theorem range_geodesicLine_one :
    Set.range (geodesicLine (1 : PSL(2, ℝ))) = {z : ℍ | z.re = 0} := by
  ext z
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    simp [geodesicLine_one_apply]
  · intro hz
    refine ⟨Real.log z.im, UpperHalfPlane.ext_re_im ?_ ?_⟩
    · simp [geodesicLine_one_apply, hz]
    · simp [geodesicLine_one_apply, Real.exp_log z.im_pos]

/-- Every geodesic line, as a set, is a `g`-translate of the imaginary axis. -/
theorem range_geodesicLine (g : PSL(2, ℝ)) :
    Set.range (geodesicLine g) = g • {z : ℍ | z.re = 0} := by
  rw [← range_geodesicLine_one, smul_range_geodesicLine, mul_one]

-- Not `@[simp]`: at default priority it never fires, since `Set.mem_range` rewrites the same
-- term first; at `@[simp high]` it regresses the self-membership goal
-- `geodesicLine g t ∈ Set.range (geodesicLine g)` into the harder
-- `(g⁻¹ • geodesicLine g t).re = 0`. Use it via `rw`.
/-- A point `z` lies on the geodesic line of `g` iff `g⁻¹ • z` lies on the imaginary axis. -/
theorem mem_range_geodesicLine_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ Set.range (geodesicLine g) ↔ (g⁻¹ • z : ℍ).re = 0 := by
  rw [range_geodesicLine, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq]

/-- Multiplying the representative by `pslS` reverses the parametrisation of a geodesic line:
`z ↦ -1/z` runs the upward imaginary axis downward. -/
@[simp]
theorem geodesicLine_mul_pslS (g : PSL(2, ℝ)) (t : ℝ) :
    geodesicLine (g * pslS) t = geodesicLine g (-t) := by
  have h : geodesicLine pslS t = geodesicLine 1 (-t) := by
    ext
    rw [geodesicLine_def, geodesicLine_one_apply, pslS_smul, modular_S_smul, coe_mk, coe_mk]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [Complex.ext_iff]
    simp [Real.exp_neg, Real.exp_ne_zero]
  rw [← smul_geodesicLine, h, smul_geodesicLine, mul_one]

/-- The geodesic lines of `g` and `g * pslS` have the same image: `z ↦ -1/z` fixes the
imaginary axis setwise, reversing its direction. (The two half-planes it bounds are swapped
instead.) -/
@[simp]
theorem range_geodesicLine_mul_pslS (g : PSL(2, ℝ)) :
    Set.range (geodesicLine (g * pslS)) = Set.range (geodesicLine g) := by
  have h : geodesicLine (g * pslS) = geodesicLine g ∘ Neg.neg := funext (geodesicLine_mul_pslS g)
  rw [h, neg_surjective.range_comp]

/-! ### Dilations along a geodesic line -/

open Matrix.SpecialLinearGroup (dilation)

/-- The imaginary axis is the orbit of `I` under the dilations. -/
theorem geodesicLine_one_eq_dilation_smul_I (t : ℝ) :
    geodesicLine 1 t = dilation t • UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_injective
  rw [geodesicLine_one_apply, coe_dilation_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
  simp [Complex.ext_iff, Complex.exp_ofReal_re]

/-- Right multiplication by a dilation shifts the parameter of a geodesic line. -/
@[simp]
theorem geodesicLine_mul_dilation (g : PSL(2, ℝ)) (s t : ℝ) :
    geodesicLine (g * ↑(dilation s)) t = geodesicLine g (s + t) := by
  rw [← smul_geodesicLine]
  conv_rhs => rw [← mul_one g, ← smul_geodesicLine]
  congr 1
  rw [geodesicLine_def, UpperHalfPlane.pslMk_smul, ← geodesicLine_one_apply,
    geodesicLine_one_eq_dilation_smul_I, geodesicLine_one_eq_dilation_smul_I, ← mul_smul,
    ← Matrix.SpecialLinearGroup.dilation_add]

/-- Shifting the parameter does not change a geodesic line as a set. -/
@[simp]
theorem range_geodesicLine_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    Set.range (geodesicLine (g * ↑(dilation s))) = Set.range (geodesicLine g) := by
  have h : geodesicLine (g * ↑(dilation s)) = geodesicLine g ∘ (s + ·) :=
    funext (geodesicLine_mul_dilation g s)
  rw [h, (add_left_surjective s).range_comp]

/-! ### Two-point transitivity -/

/-- Any two points `z`, `w` lie on a common geodesic line, `z` at parameter `0` and `w` at a
nonnegative parameter; the parameter is identified as `dist z w` in
`exists_geodesicLine_zero_eq_and_dist_eq`. -/
private theorem exists_nonneg_geodesicLine_zero_eq_and_apply_eq (z w : ℍ) :
    ∃ g : PSL(2, ℝ), ∃ t : ℝ, 0 ≤ t ∧ geodesicLine g 0 = z ∧ geodesicLine g t = w := by
  obtain ⟨h, hz⟩ := MulAction.exists_smul_eq PSL(2, ℝ) z UpperHalfPlane.I
  obtain ⟨θ, -, hθ⟩ := exists_rotation_smul_re_eq_zero (h • w)
  -- `k` moves `z` to `I` and `w` onto the imaginary axis, at some parameter `t`
  set k : PSL(2, ℝ) := (↑(Matrix.SpecialLinearGroup.rotation θ) : PSL(2, ℝ)) * h with hk
  have hkz : k • z = UpperHalfPlane.I := by
    rw [hk, mul_smul, hz, UpperHalfPlane.pslMk_smul, rotation_smul_I]
  have hkw : (k • w).re = 0 := by
    rw [hk, mul_smul, UpperHalfPlane.pslMk_smul]
    exact hθ
  obtain ⟨t, ht⟩ : k • w ∈ Set.range (geodesicLine 1) := by
    rw [range_geodesicLine_one]
    exact hkw
  rcases le_or_gt 0 t with ht0 | ht0
  · refine ⟨k⁻¹, t, ht0, ?_, ?_⟩
    · rw [geodesicLine_zero, ← hkz, inv_smul_smul]
    · rw [← mul_one k⁻¹, ← smul_geodesicLine, ht, inv_smul_smul]
  -- if `w` landed below `I`, reverse the axis by `pslS` first
  · refine ⟨k⁻¹ * pslS, -t, by linarith, ?_, ?_⟩
    · rw [geodesicLine_mul_pslS, neg_zero, geodesicLine_zero, ← hkz, inv_smul_smul]
    · rw [geodesicLine_mul_pslS, neg_neg, ← mul_one k⁻¹, ← smul_geodesicLine, ht, inv_smul_smul]

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
