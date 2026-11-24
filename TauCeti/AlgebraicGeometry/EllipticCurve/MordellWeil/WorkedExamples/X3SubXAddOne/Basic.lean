/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The integral equation `y² = x³ - x + 1`

This file defines the integral Weierstrass equation, spells out the affine equation of its points
over an arbitrary commutative ring, and computes its discriminant `-368`. It shows that the
integral equation is in short normal form `a₁ = a₂ = a₃ = 0`, so that every reduction and base
change of it is too, and that it is elliptic over every commutative `ℚ`-algebra. It is the common
starting point for calculations of its rational torsion and Mordell–Weil rank.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-- The integral short equation `y² = x³ - x + 1`. -/
abbrev curveX3SubXAddOne : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 1⟩

/-- Over any commutative ring, the affine points of `curveX3SubXAddOne` are the solutions of
`y² = x³ - x + 1`. -/
theorem equation_curveX3SubXAddOne_iff {R : Type*} [CommRing R] (x y : R) :
    (curveX3SubXAddOne.baseChange R).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x + 1 := by
  rw [Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_zero,
    map_one, map_neg]
  grind

/-- `y² = x³ - x + 1` is in the short normal form `a₁ = a₂ = a₃ = 0`. Through the transport
instances `WeierstrassCurve.isShortNF_map` and `WeierstrassCurve.isShortNF_baseChange`, so is every
reduction and base change of it, and through Mathlib's `WeierstrassCurve.isCharNeTwoNF_of_isShortNF`
each of these is in the normal form `a₁ = a₃ = 0` of characteristic `≠ 2`, the form in which
explicit `2`-descent is set up. -/
instance instIsShortNFCurveX3SubXAddOne : curveX3SubXAddOne.IsShortNF :=
  ⟨rfl, rfl, rfl⟩

/-- The discriminant of `y² = x³ - x + 1` is `-368 = -16 * 23`. -/
theorem Δ_curveX3SubXAddOne : curveX3SubXAddOne.Δ = -368 := by
  simp

/-- `y² = x³ - x + 1` is an elliptic curve over every commutative `ℚ`-algebra, in particular over
`ℚ` and over every field of characteristic zero. -/
instance instIsEllipticBaseChangeCurveX3SubXAddOne {R : Type*} [CommRing R] [Algebra ℚ R] :
    (curveX3SubXAddOne.baseChange R).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curveX3SubXAddOne]
  -- `-368` is a unit in `ℚ`, hence its image is a unit in every `ℚ`-algebra.
  simpa [map_ofNat] using (IsUnit.mk0 (-368 : ℚ) (by norm_num)).map (algebraMap ℚ R)

end TauCeti.WorkedExamples
