/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral

/-!
# The two hypotheses of the integral-point adapter

An integral point of a Weierstrass equation over `ℤ` is an affine rational point whose two
coordinates are integers; `WeierstrassCurve.integralPoints` records the set for an equation over
`ℤ`, with negation stability (`WeierstrassCurve.neg_mem_integralPoints`), invariance under changes
of variables over `ℤ` (`WeierstrassCurve.bijOn_pointEquivVariableChange_integralPoints`) and a
bounded search that exhausts it. Two hypotheses are load-bearing, and this file supplies the
witnesses showing that neither can be dropped. Since both witnesses live on models that are not
integral over `ℤ`, where `integralPoints` is not available, they are stated for the coordinate
property itself, `WeierstrassCurve.Affine.Point.HasIntegralCoordinates`.

* **The equation must be integral over `ℤ`.** Negation is `-(x, y) = (x, -y - a₁x - a₃)`, so a
  rational coefficient `a₃` can destroy integrality of the ordinate. On `y² + ½y = x³` the point
  `(0, 0)` has integral coordinates, while `-(0, 0) = (0, -½)` does not
  (`WeierstrassCurve.exists_not_hasIntegralCoordinates_neg`): on that model the points with
  integral coordinates are not stable under `P ↦ -P`.
* **A change of variables needs `u = ±1`.** Over `ℤ` the unit group is `{±1}`, so every change of
  variables over `ℤ` is a bijection on integral points. Over `ℚ` the identification of rational
  points still exists for `u = 2`, but the integral points are not preserved: on `y² = x³ + 3` the
  point `(1, 2)` is integral, while the point identified with it by `(x, y) ↦ (4x, 8y)` is
  `(1/4, 1/4)`, which is not. This is
  `WeierstrassCurve.exists_variableChange_not_surjective_on_integralCoordinates`.

No finiteness statement is made: Siegel's theorem is not a target of this development, and
`integralPoints` carries no `Finite` instance.

## Main definitions

* `WeierstrassCurve.Affine.Point.HasIntegralCoordinates`: a point of a Weierstrass curve over `ℚ`
  is affine and both of its coordinates are integers.

## Main results

* `WeierstrassCurve.Affine.Point.some_hasIntegralCoordinates` and
  `WeierstrassCurve.Affine.Point.zero_not_hasIntegralCoordinates`: the coordinates of an affine
  point, and the exclusion of the point at infinity.
* `WeierstrassCurve.halfYCurvePointZero_hasIntegralCoordinates`,
  `WeierstrassCurve.neg_halfYCurvePointZero` and
  `WeierstrassCurve.not_hasIntegralCoordinates_neg_halfYCurvePointZero`: on `y² + ½y = x³` the
  point `(0, 0)` is integral and its negative `(0, -½)` is not.
* `WeierstrassCurve.exists_not_hasIntegralCoordinates_neg`: negation stability therefore needs the
  equation to be integral over `ℤ`.
* `WeierstrassCurve.exists_variableChange_not_surjective_on_integralCoordinates`: a change of
  variables over `ℚ` with `u = 2` is not surjective on integral points, so the change of variables
  statement needs `u = ±1`.

This is the integral-point item of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 8.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and III.2.
-/

public section

namespace WeierstrassCurve.Affine

/-- A point of a Weierstrass curve over `ℚ` **has integral coordinates** when it is affine and both
of its coordinates are integers. The equation is not required to be integral: this is the notion
that stays meaningful on a rational model, where it need not be stable under negation
(`WeierstrassCurve.exists_not_hasIntegralCoordinates_neg`). -/
def Point.HasIntegralCoordinates {W : WeierstrassCurve ℚ} (P : W.toAffine.Point) : Prop :=
  ∃ (x y : ℤ) (h : W.toAffine.Nonsingular (x : ℚ) (y : ℚ)), P = .some (x : ℚ) (y : ℚ) h

namespace Point

variable {W : WeierstrassCurve ℚ}

/-- The coordinates of an affine point with integral coordinates are integers, and conversely. -/
theorem some_hasIntegralCoordinates {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    (.some x y h : W.toAffine.Point).HasIntegralCoordinates ↔
      ∃ x₀ y₀ : ℤ, x = (x₀ : ℚ) ∧ y = (y₀ : ℚ) := by
  constructor
  · rintro ⟨x₀, y₀, _, hP⟩
    rw [Affine.Point.some.injEq] at hP
    exact ⟨x₀, y₀, hP.1, hP.2⟩
  · rintro ⟨x₀, y₀, rfl, rfl⟩
    exact ⟨x₀, y₀, h, rfl⟩

/-- The point at infinity is not an affine point, so it has no coordinates to be integral. -/
theorem zero_not_hasIntegralCoordinates : ¬ (0 : W.toAffine.Point).HasIntegralCoordinates := by
  rintro ⟨x, y, h, hP⟩
  exact Point.some_ne_zero h hP.symm

end Point

end WeierstrassCurve.Affine

namespace WeierstrassCurve

/-! ### An integral equation is needed for negation stability -/

/-- The curve `y² + ½y = x³` over `ℚ`. Its coefficient `a₃ = ½` is not an integer, and that is
what breaks stability of integral coordinates under negation. -/
def halfYCurve : WeierstrassCurve ℚ := ⟨0, 0, 1 / 2, 0, 0⟩

/-- The point `(0, 0)` of `y² + ½y = x³` is nonsingular: the partial derivative in `y` is
`2y + ½`, which is `½` there. -/
theorem halfYCurve_nonsingular_zero : halfYCurve.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  norm_num [halfYCurve]

/-- The point `(0, 0)` of `y² + ½y = x³`. -/
def halfYCurvePointZero : halfYCurve.toAffine.Point :=
  .some 0 0 halfYCurve_nonsingular_zero

/-- The point `(0, 0)` has integral coordinates. -/
theorem halfYCurvePointZero_hasIntegralCoordinates :
    halfYCurvePointZero.HasIntegralCoordinates :=
  ⟨0, 0, halfYCurve_nonsingular_zero, rfl⟩

/-- **The negative of `(0, 0)` on `y² + ½y = x³` is `(0, -½)`**: negation is
`-(x, y) = (x, -y - a₁x - a₃)`, and here `a₁ = 0` and `a₃ = ½`. -/
theorem neg_halfYCurvePointZero :
    ∃ h : halfYCurve.toAffine.Nonsingular 0 (-(1 / 2)),
      -halfYCurvePointZero = .some 0 (-(1 / 2)) h := by
  have hneg : halfYCurve.toAffine.negY 0 0 = -(1 / 2) := by
    simp [Affine.negY, halfYCurve]
  refine ⟨hneg ▸ (halfYCurve.toAffine.nonsingular_neg 0 0).mpr halfYCurve_nonsingular_zero, ?_⟩
  rw [halfYCurvePointZero, Affine.Point.neg_some, Affine.Point.some.injEq]
  exact ⟨rfl, hneg⟩

/-- **On `y² + ½y = x³` the negative of the integral point `(0, 0)` is not integral**: its
ordinate is `-½`. -/
theorem not_hasIntegralCoordinates_neg_halfYCurvePointZero :
    ¬ (-halfYCurvePointZero).HasIntegralCoordinates := by
  obtain ⟨_, hneg⟩ := neg_halfYCurvePointZero
  rw [hneg, Affine.Point.some_hasIntegralCoordinates]
  rintro ⟨_, y, _, hy⟩
  have h : (2 : ℚ) * (y : ℚ) = -1 := by
    rw [← hy]
    norm_num
  have h' : (2 : ℤ) * y = -1 := by
    exact_mod_cast h
  omega

/-- **Integrality of the equation is needed for negation stability**: there is a Weierstrass curve
over `ℚ` with a point whose two coordinates are integers and whose negative does not have integral
coordinates. On an equation over `ℤ` this cannot happen (`neg_mem_integralPoints`). -/
theorem exists_not_hasIntegralCoordinates_neg :
    ∃ (W : WeierstrassCurve ℚ) (P : W.toAffine.Point),
      P.HasIntegralCoordinates ∧ ¬ (-P).HasIntegralCoordinates :=
  ⟨halfYCurve, halfYCurvePointZero, halfYCurvePointZero_hasIntegralCoordinates,
    not_hasIntegralCoordinates_neg_halfYCurvePointZero⟩

/-! ### A change of variables needs `u = ±1` -/

/-- The curve `y² = x³ + 3` over `ℚ`. -/
private def curveAddThree : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 3⟩

/-- The point `(1, 2)` of `y² = x³ + 3` is nonsingular. -/
private theorem curveAddThree_nonsingular : curveAddThree.toAffine.Nonsingular 1 2 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff]
  refine ⟨?_, Or.inr ?_⟩
  · norm_num [curveAddThree]
  · norm_num [curveAddThree]

/-- The change of variables `(x, y) ↦ (4x, 8y)` of `y² = x³ + 3`, that is `u = 2` with
`r = s = t = 0`. -/
private def twoChange : VariableChange ℚ := ⟨Units.mk0 2 (by norm_num), 0, 0, 0⟩

/-- **A change of variables needs `u = ±1`.** A change over `ℚ` with `u = 2` identifies the rational
points of `C • W` with those of `W`, but it does not map the integral points of `C • W` onto those
of `W`: on `y² = x³ + 3` the integral point `(1, 2)` is the image of `(1/4, 1/4)`, whose coordinates
are not integers. Over `ℤ` the unit group is `{±1}`, and there the identification is a bijection on
integral points (`bijOn_pointEquivVariableChange_integralPoints`). -/
theorem exists_variableChange_not_surjective_on_integralCoordinates :
    ∃ (W : WeierstrassCurve ℚ) (C : VariableChange ℚ) (P : W.toAffine.Point),
      (C.u : ℚ) = 2 ∧ P.HasIntegralCoordinates ∧
        ∀ Q : (C • W).toAffine.Point,
          Q.HasIntegralCoordinates → Affine.Point.equivVariableChange W C Q ≠ P := by
  refine ⟨curveAddThree, twoChange, .some 1 2 curveAddThree_nonsingular, rfl,
    ⟨1, 2, curveAddThree_nonsingular, rfl⟩, ?_⟩
  rintro Q ⟨x, y, _, rfl⟩ hP
  -- The identification sends `(x, y)` to `(4x, 8y)`, so the abscissa `1` of the image forces
  -- `4x = 1` in `ℤ`.
  rw [Affine.Point.equivVariableChange_some, Affine.Point.some.injEq] at hP
  simp only [twoChange, Units.val_mk0] at hP
  norm_num at hP
  have h4 : (4 : ℤ) * x = 1 := by
    have h : ((4 : ℤ) * x : ℚ) = 1 := by
      push_cast
      linarith [hP.1]
    exact_mod_cast h
  omega

end WeierstrassCurve

end
