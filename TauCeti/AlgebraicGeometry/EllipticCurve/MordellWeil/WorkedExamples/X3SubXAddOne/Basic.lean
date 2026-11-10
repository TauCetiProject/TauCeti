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

This file defines the integral Weierstrass equation and computes its discriminant `-368`. It shows
that the equation is in short normal form `a₁ = a₂ = a₃ = 0` over every commutative ring, and that
it is elliptic over every commutative `ℚ`-algebra. It is the common starting point for calculations
of its rational torsion and Mordell–Weil rank.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-- The integral short equation `y² = x³ - x + 1`. -/
abbrev curveX3SubXAddOne : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 1⟩

/-- The discriminant of `y² = x³ - x + 1` is `-368 = -16 * 23`. -/
@[simp]
theorem Δ_curveX3SubXAddOne : curveX3SubXAddOne.Δ = -368 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- `y² = x³ - x + 1` is an elliptic curve over every commutative `ℚ`-algebra, in particular over
`ℚ` and over every field of characteristic zero. -/
instance instIsEllipticBaseChangeCurveX3SubXAddOne {R : Type*} [CommRing R] [Algebra ℚ R] :
    (curveX3SubXAddOne.baseChange R).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curveX3SubXAddOne, map_neg,
    map_ofNat, IsUnit.neg_iff, ← map_ofNat (algebraMap ℚ R)]
  exact (IsUnit.mk0 (368 : ℚ) (by norm_num)).map _

/-- Over every commutative ring, `y² = x³ - x + 1` is in the short normal form `a₁ = a₂ = a₃ = 0`.
In particular it is in the normal form `a₁ = a₃ = 0` of characteristic `≠ 2`, the form in which
explicit `2`-descent is set up. -/
instance instIsShortNFBaseChangeCurveX3SubXAddOne {R : Type*} [CommRing R] :
    (curveX3SubXAddOne.baseChange R).IsShortNF :=
  ⟨by simp, by simp, by simp⟩

end TauCeti.WorkedExamples
