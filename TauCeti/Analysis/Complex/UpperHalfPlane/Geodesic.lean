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
proved here. A geodesic line through one prescribed point is (`exists_geodesicLine_zero_eq`);
one through two prescribed points is not.

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

/-- Membership test for a geodesic line, without unfolding the smul-image. -/
@[simp]
theorem mem_range_geodesicLine_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ Set.range (geodesicLine g) ↔ (g⁻¹ • z : ℍ).re = 0 := by
  rw [range_geodesicLine, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq]

end TauCeti.UpperHalfPlane
