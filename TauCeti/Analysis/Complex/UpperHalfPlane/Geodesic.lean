/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Geodesic lines in the upper half-plane, transported from the imaginary axis

Mathlib's `UpperHalfPlane.isometry_vertical_line` already exhibits the imaginary axis, in its
upward unit-speed parametrisation `t ↦ mk ⟨0, exp t⟩ _`, as a geodesic line, and
`IsIsometricSMul SL(2, ℝ) ℍ` already gives the isometric action. This file only composes the
two: the `SL(2, ℝ)`-translate of the imaginary axis by any `g` is again a geodesic line, and
every one of these is unit-speed (`isometry_geodesicLine`), hence injective
(`geodesicLine_injective`) and at explicit distance `|s - t|` between its parameters
(`dist_geodesicLine`).

This is the transport step behind the classical description of hyperbolic geodesics in `ℍ` as
vertical lines and semicircles centred on the real axis: as a *set*, the image of
`geodesicLine g` is the `g`-translate of the imaginary axis, which is a vertical line when `g`
fixes the point at infinity and a semicircle otherwise. That case split, and the existence of a
`geodesicLine` through two prescribed points, are not proved here.

## Main declarations

* `TauCeti.geodesicLine g` — the image of the (upward, unit-speed) imaginary axis under `g`.
* `TauCeti.isometry_geodesicLine` — `geodesicLine g` is an isometric embedding of `ℝ`.
* `TauCeti.dist_geodesicLine` — the distance between two of its points is `|s - t|`.
* `TauCeti.smul_geodesicLine` — further translating a geodesic line by `h` gives the geodesic
  line of `h * g`, so these lines are permuted, not merely mapped into each other, by the
  `SL(2, ℝ)`-action.
-/

public section

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti

/-- The geodesic line obtained by moving the (upward, unit-speed) imaginary axis by `g`. -/
def geodesicLine (g : SL(2, ℝ)) (t : ℝ) : ℍ :=
  g • UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)

theorem geodesicLine_one (t : ℝ) :
    geodesicLine 1 t = UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t) := by
  simp [geodesicLine]

theorem isometry_geodesicLine (g : SL(2, ℝ)) : Isometry (geodesicLine g) :=
  (isometry_smul ℍ g).comp (UpperHalfPlane.isometry_vertical_line 0)

theorem geodesicLine_injective (g : SL(2, ℝ)) : Function.Injective (geodesicLine g) :=
  (isometry_geodesicLine g).injective

theorem dist_geodesicLine (g : SL(2, ℝ)) (s t : ℝ) :
    dist (geodesicLine g s) (geodesicLine g t) = |s - t| := by
  rw [(isometry_geodesicLine g).dist_eq, Real.dist_eq]

theorem geodesicLine_zero (g : SL(2, ℝ)) : geodesicLine g 0 = g • UpperHalfPlane.I := by
  unfold geodesicLine
  congr 1
  simp [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_I, Complex.ext_iff]

/-- Translating a geodesic line by `h` gives the geodesic line of `h * g`: the
`SL(2, ℝ)`-action permutes these lines rather than merely mapping into their union. -/
theorem smul_geodesicLine (h g : SL(2, ℝ)) (t : ℝ) :
    h • geodesicLine g t = geodesicLine (h * g) t := by
  simp [geodesicLine, mul_smul]

end TauCeti
