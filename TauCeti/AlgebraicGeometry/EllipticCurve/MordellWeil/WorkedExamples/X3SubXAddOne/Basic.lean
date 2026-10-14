/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The integral equation `y² = x³ - x + 1`

This file defines the integral Weierstrass equation, computes its discriminant `-368`, and
establishes ellipticity over `ℚ`. Over `ℚ` the equation is in the normal form
`y² = x³ + a₂x² + a₄x + a₆` of explicit `2`-descent, and every rational solution is a nonsingular
point. It is the common starting point for calculations of its rational torsion and
Mordell–Weil rank.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-- The integral short equation `y² = x³ - x + 1`. -/
abbrev curveX3SubXAddOne : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 1⟩

/-- The discriminant of `y² = x³ - x + 1` is `-368 = -16 * 23`. -/
theorem Δ_curveX3SubXAddOne : curveX3SubXAddOne.Δ = -368 := by
  norm_num [curveX3SubXAddOne, Δ, b₂, b₄, b₆, b₈]

/-- `y² = x³ - x + 1` is an elliptic curve over `ℚ`. -/
instance : (curveX3SubXAddOne.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curveX3SubXAddOne]
  norm_num

/-- Over `ℚ`, `y² = x³ - x + 1` is in the normal form `y² = x³ + a₂x² + a₄x + a₆`. -/
instance : (curveX3SubXAddOne.baseChange ℚ).IsCharNeTwoNF :=
  ⟨by simp, by simp⟩

/-- Every rational solution of `y² = x³ - x + 1` is a nonsingular point. -/
theorem nonsingular_curveX3SubXAddOne {x y : ℚ} (h : y ^ 2 = x ^ 3 - x + 1) :
    (curveX3SubXAddOne.baseChange ℚ).toAffine.Nonsingular x y :=
  Affine.equation_iff_nonsingular.mp (by rw [Affine.equation_iff]; simpa [sub_eq_add_neg] using h)

end TauCeti.WorkedExamples
