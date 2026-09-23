/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# Geodesic lines in the upper half-plane, transported from the imaginary axis

Mathlib's `UpperHalfPlane.isometry_vertical_line` already exhibits the imaginary axis, in its
upward unit-speed parametrisation `t ↦ mk ⟨0, exp t⟩ _`, as a geodesic line, and Tau Ceti's
`IsIsometricSMul PSL(2, ℝ) ℍ` (`ProperAction.lean`) already gives the isometric action of the
group Fuchsian groups are subgroups of. This file only composes the two: the `PSL(2, ℝ)`-translate
of the imaginary axis by any `g` is again a geodesic line, and every one of these is unit-speed
(`isometry_geodesicLine`), hence injective (`geodesicLine_injective`) and at explicit distance
`|s - t|` between its parameters (`dist_geodesicLine`).

This is the transport step behind the classical description of hyperbolic geodesics in `ℍ` as
vertical lines and semicircles centred on the real axis: as a *set*, the image of the map
`geodesicLine g` is the `g`-translate of the imaginary axis, which is a vertical line when the
representing matrix's lower-left entry `g 1 0` or lower-right entry `g 1 1` is `0` (equivalently,
`g` sends one of the imaginary axis's two boundary points, `0` and the point at infinity, to the
point at infinity) and a semicircle centred on the real axis otherwise. That case split is not
proved here.

What is proved is two-point transitivity: any two points `z`, `w` lie on a common geodesic line,
with `z` at parameter `0` and `w` at parameter `dist z w`
(`exists_geodesicLine_zero_eq_and_dist_eq`). The one new ingredient is the rotations
`rotation θ = !![cos θ, sin θ; -sin θ, cos θ]` in the stabiliser of `I`: rotating a point from
`θ = 0` to `θ = π/2` (where the rotation acts as `w ↦ -1/w`) reverses the sign of its real part,
so by the intermediate value theorem some rotation brings it onto the imaginary axis
(`exists_rotation_smul_re_eq_zero`). No explicit formula for the rotation angle, and no
description of the stabiliser of `I` as the full rotation group, is needed or given.

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
* `TauCeti.UpperHalfPlane.rotation θ` — the rotation `!![cos θ, sin θ; -sin θ, cos θ]` in
  `SL(2, ℝ)`; it fixes `I` (`rotation_smul_I`), and `rotation (π/2)` reverses the parametrised
  imaginary axis (`rotation_pi_div_two_smul_geodesicLine_one`).
* `TauCeti.UpperHalfPlane.exists_rotation_smul_re_eq_zero` — some rotation about `I` moves any
  point onto the imaginary axis.
* `TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq_and_dist_eq` — two-point transitivity:
  a geodesic line with `z` at parameter `0` and `w` at parameter `dist z w`, for any `z`, `w`;
  `exists_mem_range_geodesicLine_and_mem` is the same at the level of the line as a set.
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

/-- Every geodesic line is the translate of the one of the identity. -/
theorem geodesicLine_eq_smul (g : PSL(2, ℝ)) (t : ℝ) :
    geodesicLine g t = g • geodesicLine 1 t := by
  rw [smul_geodesicLine, mul_one]

/-! ### Rotations about `I`, and a geodesic line through two prescribed points

The stabiliser of `I` contains the rotations `rotation θ = !![cos θ, sin θ; -sin θ, cos θ]`.
Rotating a point `w` continuously from `θ = 0` to `θ = π/2` (where the rotation acts as
`w ↦ -1/w`) changes the sign of its real part, so some rotation brings `w` onto the imaginary
axis (`exists_rotation_smul_re_eq_zero`, an intermediate-value argument). Combined with
transitivity this is two-point transitivity on parametrised geodesic lines: for any `z`, `w`
there is a geodesic line with `z` at parameter `0` and `w` at parameter `dist z w`
(`exists_geodesicLine_zero_eq_and_dist_eq`). -/

/-- The rotation `!![cos θ, sin θ; -sin θ, cos θ]`, an element of `SL(2, ℝ)` fixing `I`. -/
def rotation (θ : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ], by
    rw [Matrix.det_fin_two_of]
    linear_combination Real.cos_sq_add_sin_sq θ⟩

theorem rotation_denom_ne_zero (θ : ℝ) (z : ℍ) :
    -(Real.sin θ : ℂ) * z + Real.cos θ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.mul_re, coe_im, coe_re, Complex.zero_im,
    Complex.zero_re] at him hre
  have hsin : Real.sin θ = 0 := by
    have := z.im_pos
    nlinarith
  rw [hsin] at hre
  have := Real.cos_sq_add_sin_sq θ
  rw [hsin] at this
  nlinarith

theorem coe_rotation_smul (θ : ℝ) (z : ℍ) :
    ((rotation θ • z : ℍ) : ℂ) =
      ((Real.cos θ : ℂ) * z + Real.sin θ) / (-(Real.sin θ : ℂ) * z + Real.cos θ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [rotation]

/-- The rotations fix `I`. -/
@[simp]
theorem rotation_smul_I (θ : ℝ) : rotation θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  ext
  have hne := rotation_denom_ne_zero θ UpperHalfPlane.I
  rw [UpperHalfPlane.coe_I] at hne
  rw [coe_rotation_smul, UpperHalfPlane.coe_I, div_eq_iff hne]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The rotation by `π/2` reverses the parametrised imaginary axis: it is `z ↦ -1/z`. -/
theorem rotation_pi_div_two_smul_geodesicLine_one (t : ℝ) :
    (↑(rotation (Real.pi / 2)) : PSL(2, ℝ)) • geodesicLine 1 t = geodesicLine 1 (-t) := by
  rw [UpperHalfPlane.pslMk_smul]
  ext
  rw [coe_rotation_smul, geodesicLine_one_apply, geodesicLine_one_apply, UpperHalfPlane.coe_mk,
    UpperHalfPlane.coe_mk, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.exp_neg]
  rw [Complex.ext_iff]
  constructor
  · simp [Complex.normSq_apply]
  · simp [Complex.normSq_apply]
    field_simp

/-- Some rotation about `I` moves any point onto the imaginary axis. -/
theorem exists_rotation_smul_re_eq_zero (w : ℍ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), (rotation θ • w).re = 0 := by
  have hcont : Continuous fun θ => (rotation θ • w).re := by
    have : (fun θ => (rotation θ • w).re) = fun θ => (((Real.cos θ : ℂ) * w + Real.sin θ) /
        (-(Real.sin θ : ℂ) * w + Real.cos θ)).re := by
      funext θ
      rw [← coe_re, coe_rotation_smul]
    rw [this]
    refine Complex.continuous_re.comp (Continuous.div (by fun_prop) (by fun_prop) ?_)
    exact fun θ => rotation_denom_ne_zero θ w
  have h0 : (rotation 0 • w).re = w.re := by
    rw [← coe_re, coe_rotation_smul]
    simp
  have hpi : (rotation (Real.pi / 2) • w).re = -(w.re / Complex.normSq w) := by
    rw [← coe_re, coe_rotation_smul, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp [Complex.inv_re, coe_re]
  have hpos : 0 < Complex.normSq w := Complex.normSq_pos.2 (ne_zero w)
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rcases le_or_gt 0 w.re with hre | hre
  · have hpi' : (rotation (Real.pi / 2) • w).re ≤ 0 := by
      rw [hpi]
      exact neg_nonpos.2 (div_nonneg hre hpos.le)
    obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc' hab hcont.continuousOn ⟨hpi', h0 ▸ hre⟩
    exact ⟨θ, hθ, hθ0⟩
  · have hpi' : 0 ≤ (rotation (Real.pi / 2) • w).re := by
      rw [hpi]
      exact neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hre.le hpos.le)
    obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨h0 ▸ hre.le, hpi'⟩
    exact ⟨θ, hθ, hθ0⟩

/-- A point of the imaginary axis lies on the geodesic line of the identity. -/
theorem exists_geodesicLine_one_eq {u : ℍ} (hu : u.re = 0) : ∃ t : ℝ, geodesicLine 1 t = u := by
  refine ⟨Real.log u.im, ?_⟩
  ext
  rw [geodesicLine_one_apply, UpperHalfPlane.coe_mk, Complex.ext_iff]
  simp [coe_re, coe_im, hu, Real.exp_log u.im_pos]

/-- **Two-point transitivity on parametrised geodesic lines.** Any two points `z`, `w` lie on a
common geodesic line, with `z` at parameter `0` and `w` at parameter `dist z w`. -/
theorem exists_geodesicLine_zero_eq_and_dist_eq (z w : ℍ) :
    ∃ g : PSL(2, ℝ), geodesicLine g 0 = z ∧ geodesicLine g (dist z w) = w := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq PSL(2, ℝ) z UpperHalfPlane.I
  obtain ⟨θ, -, hθ⟩ := exists_rotation_smul_re_eq_zero (g₀ • w)
  set h : PSL(2, ℝ) := (↑(rotation θ) : PSL(2, ℝ)) * g₀ with hh
  have hz : h • z = UpperHalfPlane.I := by
    rw [hh, mul_smul, hg₀, UpperHalfPlane.pslMk_smul, rotation_smul_I]
  obtain ⟨t, ht⟩ := exists_geodesicLine_one_eq (u := h • w) (by
    rw [hh, mul_smul, UpperHalfPlane.pslMk_smul]; exact hθ)
  -- `z` and `w` are `h⁻¹ • I` and `h⁻¹ • geodesicLine 1 t`; if `t < 0`, reverse the axis first.
  have key : ∀ g : PSL(2, ℝ), ∀ s : ℝ, 0 ≤ s → g • geodesicLine 1 0 = UpperHalfPlane.I →
      g • geodesicLine 1 s = h • w → ∃ g' : PSL(2, ℝ), geodesicLine g' 0 = z ∧
        geodesicLine g' (dist z w) = w := by
    intro g s hs h0 hsw
    refine ⟨h⁻¹ * g, ?_, ?_⟩
    · rw [geodesicLine_eq_smul, mul_smul, h0, ← hz, inv_smul_smul]
    · have hd : dist z w = s := by
        rw [← inv_smul_smul h z, ← inv_smul_smul h w, dist_smul, hz, ← hsw, ← h0,
          dist_smul, geodesicLine_one_apply, geodesicLine_one_apply,
          ← geodesicLine_one_apply, ← geodesicLine_one_apply, dist_geodesicLine, zero_sub,
          abs_neg, abs_of_nonneg hs]
      rw [hd, geodesicLine_eq_smul, mul_smul, hsw, inv_smul_smul]
  rcases le_or_gt 0 t with ht0 | ht0
  · exact key 1 t ht0 (by rw [one_smul, geodesicLine_zero, one_smul]) (by rw [one_smul, ht])
  · refine key (↑(rotation (Real.pi / 2)) : PSL(2, ℝ)) (-t) (by linarith) ?_ ?_
    · rw [rotation_pi_div_two_smul_geodesicLine_one, neg_zero, geodesicLine_zero, one_smul]
    · rw [rotation_pi_div_two_smul_geodesicLine_one, neg_neg, ht]

/-- Any two points lie on a common geodesic line. -/
theorem exists_mem_range_geodesicLine_and_mem (z w : ℍ) :
    ∃ g : PSL(2, ℝ), z ∈ Set.range (geodesicLine g) ∧ w ∈ Set.range (geodesicLine g) := by
  obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  exact ⟨g, ⟨0, hz⟩, ⟨dist z w, hw⟩⟩

end TauCeti.UpperHalfPlane
