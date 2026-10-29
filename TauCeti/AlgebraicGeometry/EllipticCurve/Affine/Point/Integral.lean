/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.Data.Int.Quadratic
import Mathlib.Data.Int.Interval

/-!
# Integral points of an integral Weierstrass equation

An integral point is an affine rational point whose two coordinates come from `ℤ`. The equation
is kept over `ℤ`, so negation preserves integral points even when the model is not short. A finite
search over a box of integer coordinates gives a certificate for every point in that box. No
finiteness assertion is made for the set of all integral points.

The same coordinate property is also defined on its own, as
`WeierstrassCurve.Affine.Point.HasIntegralCoordinates`: a point of an arbitrary
`WeierstrassCurve ℚ` has integral coordinates when it is affine and both of its coordinates are
integers. On an integral model this agrees with membership in `integralPoints`
(`hasIntegralCoordinates_iff_mem_integralPoints`). It is the predicate the two counterexamples
below are stated for, since `integralPoints` is only defined on models integral over `ℤ`: the
first model is not integral over `ℤ`, and the second's source curve `C • W` is not either.

The set depends on the integral equation, rather than only on its rational isomorphism class. A
change of variables `C` over `ℤ`, so with `u = ±1` and `r, s, t ∈ ℤ`, identifies the rational points
of `C • W` and of `W` by `(x, y) ↦ (u²x + r, u³y + u²sx + t)`
(`WeierstrassCurve.pointEquivVariableChange` with `L = ℚ`), and this identification restricts to a
bijection between their integral points
(`WeierstrassCurve.bijOn_pointEquivVariableChange_integralPoints`).
The restriction to changes of variables over `ℤ` matters: the scaling `(x, y) ↦ (u²x, u³y)` with
`|u| > 1` identifies the rational points too, but not the integral ones, since a point `(X, Y)` of
`W` corresponds to `(X / u², Y / u³)`.

Both restrictions are load-bearing. On `y² + ½y = x³` the point `(0, 0)` has integral coordinates
while its negative `(0, -½)` does not (`exists_not_hasIntegralCoordinates_neg`), so stability under
negation is not guaranteed on an arbitrary rational model. On `y² = x³ + 3` the change of variables
`(x, y) ↦ (4x, 8y)`, that is `u = 2` with `r = s = t = 0`, sends the point `(1/4, 1/4)` of the
transformed curve `C • W : y² = x³ + 3/64` to the integral point `(1, 2)`. The identification is a
bijection on rational points, so `(1/4, 1/4)` is the only preimage of `(1, 2)`, and it is not
integral; hence the change of variables does not map the integral points of `C • W` onto those of
`W` (`exists_not_surjOn_equivVariableChange_hasIntegralCoordinates`).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and III.2.
-/

public section

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℤ) [(W.baseChange ℚ).IsElliptic]

-- The affine curve of the rational base change is the coefficientwise map of the integral curve.
omit [(W.baseChange ℚ).IsElliptic] in
private theorem integral_toAffine_baseChange :
    (W.baseChange ℚ).toAffine = W.toAffine.map (Int.castRingHom ℚ) := by
  rfl

omit [(W.baseChange ℚ).IsElliptic] in
/-- The rational base change satisfies the Weierstrass equation at integer-cast coordinates
exactly when the integral model does. Not to be confused with
`WeierstrassCurve.Affine.equation_baseChange_iff`, which expands the coefficients of a base
change. -/
theorem equation_baseChange_iff_intCast {x y : ℤ} :
    (W.baseChange ℚ).toAffine.Equation (x : ℚ) (y : ℚ) ↔ W.toAffine.Equation x y := by
  rw [W.integral_toAffine_baseChange]
  simpa only [Int.coe_castRingHom] using
    Affine.map_equation W.toAffine (f := Int.castRingHom ℚ) Int.cast_injective x y

/-- An integral solution of the affine Weierstrass equation determines a rational point. -/
def pointOfIntegralSolution (x y : ℤ) (h : W.toAffine.Equation x y) :
    (W.baseChange ℚ).toAffine.Point :=
  .mk (W.equation_baseChange_iff_intCast.mpr h)

-- Not a `simp` lemma: it would rewrite the left-hand sides of `pointOfIntegralSolution_mem` and
-- the `pointEquiv` lemmas, which are themselves in `simp` normal form.
/-- The point built from an integral solution is the affine point with those coordinates. -/
theorem pointOfIntegralSolution_eq_some (x y : ℤ) (h : W.toAffine.Equation x y) :
    W.pointOfIntegralSolution x y h =
      .some (x : ℚ) (y : ℚ)
        (Affine.equation_iff_nonsingular.mp (W.equation_baseChange_iff_intCast.mpr h)) := by
  simp only [pointOfIntegralSolution, Affine.Point.mk]

/-- The affine coordinates of the rational point constructed from an integral solution. -/
@[simp]
theorem pointEquiv_pointOfIntegralSolution (x y : ℤ) (h : W.toAffine.Equation x y) :
    (W.baseChange ℚ).toAffine.pointEquiv (W.pointOfIntegralSolution x y h) =
      .some ⟨⟨(x : ℚ), (y : ℚ)⟩, by
        exact W.equation_baseChange_iff_intCast.mpr h⟩ := by
  simp only [pointOfIntegralSolution, Affine.pointEquiv_some]
  congr 1

/-- The affine rational points with both coordinates integral. The point at infinity is excluded. -/
def integralPoints : Set (W.baseChange ℚ).toAffine.Point :=
  {P | ∃ x y : ℤ, ∃ h : W.toAffine.Equation x y, P = W.pointOfIntegralSolution x y h}

/-- A rational affine point is integral exactly when it comes from an integer solution of the
Weierstrass equation. -/
theorem mem_integralPoints_iff (P : (W.baseChange ℚ).toAffine.Point) :
    P ∈ W.integralPoints ↔
      ∃ x y : ℤ, ∃ h : W.toAffine.Equation x y, P = W.pointOfIntegralSolution x y h :=
  Iff.rfl

/-- Every integral solution gives an integral point. -/
@[simp]
theorem pointOfIntegralSolution_mem (x y : ℤ) (h : W.toAffine.Equation x y) :
    W.pointOfIntegralSolution x y h ∈ W.integralPoints :=
  ⟨x, y, h, rfl⟩

/-- The point at infinity, denoted by `0`, is not an affine integral point. -/
@[simp]
theorem zero_not_mem_integralPoints :
    (0 : (W.baseChange ℚ).toAffine.Point) ∉ W.integralPoints := by
  rintro ⟨x, y, h, heq⟩
  simp [pointOfIntegralSolution, Affine.Point.mk] at heq

/-- Integral points are stable under the group inverse because
`-(x,y) = (x,-y-a₁x-a₃)` has integral coordinates. -/
theorem neg_mem_integralPoints {P : (W.baseChange ℚ).toAffine.Point}
    (hP : P ∈ W.integralPoints) : -P ∈ W.integralPoints := by
  obtain ⟨x, y, h, rfl⟩ := hP
  let y' : ℤ := -y - W.a₁ * x - W.a₃
  have h' : W.toAffine.Equation x y' := by
    -- The chosen integer is exactly the Weierstrass negation formula.
    change W.toAffine.Equation x (W.toAffine.negY x y)
    exact (W.toAffine.equation_neg _ _).2 h
  refine ⟨x, y', h', ?_⟩
  simp only [pointOfIntegralSolution, Affine.Point.mk, Affine.Point.neg_some]
  congr 1
  rw [W.integral_toAffine_baseChange]
  exact W.toAffine.map_negY (Int.castRingHom ℚ) x y

/-- Negation preserves and reflects integrality of affine points. -/
@[simp]
theorem neg_mem_integralPoints_iff {P : (W.baseChange ℚ).toAffine.Point} :
    -P ∈ W.integralPoints ↔ P ∈ W.integralPoints := by
  constructor
  · intro hP
    have h := W.neg_mem_integralPoints hP
    simpa only [neg_neg] using h
  · exact W.neg_mem_integralPoints

/-- A bound for the `yCoord` of an integral point with a fixed `xCoord`. -/
def integralYCoordBound (x : ℤ) : ℕ :=
  (|W.a₁ * x + W.a₃| +
    |x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆| + 1).toNat

omit [(W.baseChange ℚ).IsElliptic] in
/-- The quadratic Weierstrass equation bounds the absolute `yCoord` by its linear and constant
coefficients. This makes a search bounded only in `xCoord` finite. -/
theorem abs_yCoord_le_integralYCoordBound {x y : ℤ}
    (h : W.toAffine.Equation x y) : |y| ≤ W.integralYCoordBound x := by
  let b : ℤ := W.a₁ * x + W.a₃
  let c : ℤ := x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  have heq : y ^ 2 + b * y = c := by
    have := (W.toAffine.equation_iff x y).mp h
    dsimp [b, c]
    nlinarith
  have hbound := TauCeti.abs_le_of_quadratic_eq heq
  -- Unfold the natural bound as its nonnegative integer cast.
  change |y| ≤ ((|b| + |c| + 1).toNat : ℤ)
  rw [Int.toNat_of_nonneg (by positivity)]
  exact hbound

/-- Integer coordinate pairs with `|x| ≤ B` that solve the Weierstrass equation. This is a
computable finite search: the ordinate bound makes each inner interval finite. -/
def boundedIntegralSolutions (B : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(B : ℤ)) B).biUnion fun x =>
    (Finset.Icc (-(W.integralYCoordBound x : ℤ)) (W.integralYCoordBound x)).image
      fun y => (x, y)).filter
    (fun p => p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 =
      p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆)

omit [(W.baseChange ℚ).IsElliptic] in
/-- The search contains exactly the integral solutions with bounded abscissa. -/
@[simp]
theorem mem_boundedIntegralSolutions_iff (B : ℕ) (p : ℤ × ℤ) :
    p ∈ W.boundedIntegralSolutions B ↔
      W.toAffine.Equation p.1 p.2 ∧ -(B : ℤ) ≤ p.1 ∧ p.1 ≤ B := by
  simp only [boundedIntegralSolutions, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨x, hx, y, _, hp⟩, heq⟩
    have hxy : p = (x, y) := hp.symm
    rcases hxy with rfl
    exact ⟨(W.toAffine.equation_iff _ _).2 heq, hx.1, hx.2⟩
  · rintro ⟨heq, hx₁, hx₂⟩
    have hy := W.abs_yCoord_le_integralYCoordBound heq
    have hy' : -(W.integralYCoordBound p.1 : ℤ) ≤ p.2 ∧
        p.2 ≤ W.integralYCoordBound p.1 := abs_le.mp hy
    exact ⟨⟨p.1, ⟨hx₁, hx₂⟩, p.2, hy', rfl⟩,
      (W.toAffine.equation_iff _ _).1 heq⟩

/-- The finite set of rational integral points with `|x| ≤ B`, obtained by evaluating the
bounded integer-coordinate search. -/
def boundedIntegralPoints (B : ℕ) : Finset (W.baseChange ℚ).toAffine.Point :=
  (W.boundedIntegralSolutions B).attach.image fun p =>
    W.pointOfIntegralSolution p.1.1 p.1.2 ((W.mem_boundedIntegralSolutions_iff B p.1).mp p.2).1

/-- Membership in the finite search result is exactly integrality and the abscissa bound. -/
@[simp]
theorem mem_boundedIntegralPoints_iff (B : ℕ) (P : (W.baseChange ℚ).toAffine.Point) :
    P ∈ W.boundedIntegralPoints B ↔
      ∃ x y : ℤ, ∃ h : W.toAffine.Equation x y,
        P = W.pointOfIntegralSolution x y h ∧ -(B : ℤ) ≤ x ∧ x ≤ B := by
  simp only [boundedIntegralPoints, Finset.mem_image, Finset.mem_attach]
  constructor
  · rintro ⟨p, -, heq⟩
    rcases p with ⟨⟨x, y⟩, hp⟩
    obtain ⟨heq', hx₁, hx₂⟩ := (W.mem_boundedIntegralSolutions_iff B (x, y)).mp hp
    exact ⟨x, y, heq', heq.symm, hx₁, hx₂⟩
  · rintro ⟨x, y, h, heq, hx₁, hx₂⟩
    have hp : (x, y) ∈ W.boundedIntegralSolutions B :=
      (W.mem_boundedIntegralSolutions_iff B _).2 ⟨h, hx₁, hx₂⟩
    exact ⟨⟨(x, y), hp⟩, trivial, heq.symm⟩

/-- Every point returned by the bounded search is integral. -/
theorem boundedIntegralPoints_subset_integralPoints (B : ℕ) :
    ↑(W.boundedIntegralPoints B) ⊆ W.integralPoints := by
  intro P hP
  obtain ⟨x, y, h, hEq, -, -⟩ := (W.mem_boundedIntegralPoints_iff B P).mp hP
  exact ⟨x, y, h, hEq⟩

/-- The bounded searches exhaust the integral points. A claimed complete list below an abscissa
bound can therefore be checked by comparing it with `boundedIntegralPoints`. -/
theorem mem_integralPoints_iff_exists_mem_boundedIntegralPoints
    (P : (W.baseChange ℚ).toAffine.Point) :
    P ∈ W.integralPoints ↔ ∃ B : ℕ, P ∈ W.boundedIntegralPoints B := by
  constructor
  · rintro ⟨x, y, h, rfl⟩
    refine ⟨x.natAbs, (W.mem_boundedIntegralPoints_iff _ _).2 ?_⟩
    exact ⟨x, y, h, rfl, by omega, by omega⟩
  · rintro ⟨B, hB⟩
    exact W.boundedIntegralPoints_subset_integralPoints B hB

/-! ### Changes of variables over `ℤ` -/

section VariableChange

variable (C : VariableChange ℤ)

/-- The identification `pointEquivVariableChange` sends the rational point of an integral solution
`(x, y)` of `C • W` to that of the integral solution `(u²x + r, u³y + u²sx + t)` of `W`. -/
@[simp]
theorem pointEquivVariableChange_pointOfIntegralSolution (x y : ℤ)
    (h : (C • W).toAffine.Equation x y) :
    W.pointEquivVariableChange ℚ C ((C • W).pointOfIntegralSolution x y h) =
      W.pointOfIntegralSolution ((C.u : ℤ) ^ 2 * x + C.r)
        ((C.u : ℤ) ^ 3 * y + (C.u : ℤ) ^ 2 * C.s * x + C.t)
        ((Affine.variableChange_equation W C x y).mpr h) := by
  simp only [pointOfIntegralSolution, Affine.Point.mk, pointEquivVariableChange_some]
  congr 1 <;> simp [VariableChange.baseChange]

/-- The inverse of `pointEquivVariableChange` sends the rational point of an integral solution
`(x, y)` of `W` to that of the integral solution of `C • W` given by the coordinates of `C⁻¹`. -/
@[simp]
theorem pointEquivVariableChange_symm_pointOfIntegralSolution (x y : ℤ)
    (h : W.toAffine.Equation x y) :
    (W.pointEquivVariableChange ℚ C).symm (W.pointOfIntegralSolution x y h) =
      (C • W).pointOfIntegralSolution (((C⁻¹).u : ℤ) ^ 2 * x + (C⁻¹).r)
        (((C⁻¹).u : ℤ) ^ 3 * y + ((C⁻¹).u : ℤ) ^ 2 * (C⁻¹).s * x + (C⁻¹).t)
        ((Affine.variableChange_equation (C • W) C⁻¹ x y).mpr
          ((inv_smul_smul C W).symm ▸ h)) := by
  simp only [pointOfIntegralSolution, Affine.Point.mk, pointEquivVariableChange_symm_some]
  congr 1 <;> simp [VariableChange.baseChange, ← VariableChange.map_inv]

/-- **A change of variables over `ℤ` preserves and reflects integrality**: a rational point of
`C • W` is integral exactly when its image under `pointEquivVariableChange` is an integral point
of `W`. -/
@[simp]
theorem pointEquivVariableChange_mem_integralPoints_iff
    (P : ((C • W).baseChange ℚ).toAffine.Point) :
    W.pointEquivVariableChange ℚ C P ∈ W.integralPoints ↔ P ∈ (C • W).integralPoints := by
  constructor
  · rintro ⟨x, y, h, hP⟩
    rw [← (W.pointEquivVariableChange ℚ C).symm_apply_apply P, hP,
      pointEquivVariableChange_symm_pointOfIntegralSolution]
    exact pointOfIntegralSolution_mem _ _ _ _
  · rintro ⟨x, y, h, rfl⟩
    rw [pointEquivVariableChange_pointOfIntegralSolution]
    exact pointOfIntegralSolution_mem _ _ _ _

/-- **A change of variables over `ℤ` is a bijection on integral points**: the identification
`pointEquivVariableChange` of the rational points of `C • W` and of `W` maps the integral points
of `C • W` bijectively onto those of `W`. -/
theorem bijOn_pointEquivVariableChange_integralPoints :
    Set.BijOn (W.pointEquivVariableChange ℚ C) (C • W).integralPoints W.integralPoints :=
  (W.pointEquivVariableChange ℚ C).toEquiv.bijOn
    (W.pointEquivVariableChange_mem_integralPoints_iff C)

end VariableChange

end WeierstrassCurve

namespace WeierstrassCurve.Affine

/-- A point of a Weierstrass curve over `ℚ` **has integral coordinates** when it is affine and
both of its coordinates are integers. The equation is not required to be integral: this is the
notion that stays meaningful on a rational model, where it need not be stable under negation
(`exists_not_hasIntegralCoordinates_neg`). -/
def Point.HasIntegralCoordinates {W : WeierstrassCurve ℚ} (P : W.toAffine.Point) : Prop :=
  ∃ (x y : ℤ) (h : W.toAffine.Nonsingular (x : ℚ) (y : ℚ)), P = .some (x : ℚ) (y : ℚ) h

namespace Point

variable {W : WeierstrassCurve ℚ}

/-- An affine point over `ℚ` has integral coordinates exactly when it is the point with
integer-cast coordinates. This is the general form of `hasIntegralCoordinates_some`, and the form
to use when building or destructuring such a point. -/
theorem hasIntegralCoordinates_iff (P : W.toAffine.Point) :
    P.HasIntegralCoordinates ↔
      ∃ (x y : ℤ) (h : W.toAffine.Nonsingular (x : ℚ) (y : ℚ)),
        P = .some (x : ℚ) (y : ℚ) h :=
  Iff.rfl

/-- The coordinates of an affine point with integral coordinates are integers, and conversely. -/
@[simp]
theorem hasIntegralCoordinates_some {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    (.some x y h : W.toAffine.Point).HasIntegralCoordinates ↔
      ∃ x₀ y₀ : ℤ, x = (x₀ : ℚ) ∧ y = (y₀ : ℚ) := by
  constructor
  · rintro ⟨x₀, y₀, _, hP⟩
    rw [Affine.Point.some.injEq] at hP
    exact ⟨x₀, y₀, hP.1, hP.2⟩
  · rintro ⟨x₀, y₀, rfl, rfl⟩
    exact ⟨x₀, y₀, h, rfl⟩

/-- The point at infinity is not an affine point, so it has no coordinates to be integral. -/
@[simp]
theorem not_hasIntegralCoordinates_zero : ¬ (0 : W.toAffine.Point).HasIntegralCoordinates := by
  rintro ⟨x, y, h, hP⟩
  exact Point.some_ne_zero h hP.symm

end Point

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℤ) [(W.baseChange ℚ).IsElliptic]

/-- On an integral model the coordinate predicate is exactly membership in `integralPoints`. -/
@[simp]
theorem hasIntegralCoordinates_iff_mem_integralPoints
    (P : (W.baseChange ℚ).toAffine.Point) :
    P.HasIntegralCoordinates ↔ P ∈ W.integralPoints := by
  rw [mem_integralPoints_iff]
  constructor
  · rintro ⟨x, y, hP, rfl⟩
    have hEq : (W.baseChange ℚ).toAffine.Equation (x : ℚ) (y : ℚ) :=
      Affine.equation_iff_nonsingular.mpr hP
    refine ⟨x, y, W.equation_baseChange_iff_intCast.mp hEq, ?_⟩
    rw [W.pointOfIntegralSolution_eq_some, Affine.Point.some.injEq]
    exact ⟨rfl, rfl⟩
  · rintro ⟨x, y, h, rfl⟩
    refine ⟨x, y, Affine.equation_iff_nonsingular.mp (W.equation_baseChange_iff_intCast.mpr h), ?_⟩
    rw [W.pointOfIntegralSolution_eq_some, Affine.Point.some.injEq]
    exact ⟨rfl, rfl⟩

/-- An affine point of an integral model is an integral point exactly when both its coordinates are
integer casts, the same normal form as `hasIntegralCoordinates_some`. -/
@[simp]
theorem some_mem_integralPoints_iff {x y : ℚ}
    (h : (W.baseChange ℚ).toAffine.Nonsingular x y) :
    (.some x y h : (W.baseChange ℚ).toAffine.Point) ∈ W.integralPoints ↔
      ∃ x₀ y₀ : ℤ, x = (x₀ : ℚ) ∧ y = (y₀ : ℚ) := by
  rw [← hasIntegralCoordinates_iff_mem_integralPoints, Affine.Point.hasIntegralCoordinates_some]

end WeierstrassCurve

namespace TauCeti

/-! ### An integral equation is needed for negation stability -/

/-- The curve `y² + ½y = x³` over `ℚ`. Its coefficient `a₃ = ½` is not an integer, and that
is what breaks stability of integral coordinates under negation. -/
private def halfYCurve : WeierstrassCurve ℚ := ⟨0, 0, 1 / 2, 0, 0⟩

/-- The point `(0, 0)` of `y² + ½y = x³` is nonsingular: the partial derivative in `y` is
`2y + ½`, which is `½` there. -/
private theorem halfYCurve_nonsingular_zero : halfYCurve.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  norm_num [halfYCurve]

/-- The point `(0, 0)` of `y² + ½y = x³`. -/
private def halfYCurvePointZero : halfYCurve.toAffine.Point :=
  .some 0 0 halfYCurve_nonsingular_zero

/-- The point `(0, 0)` has integral coordinates. -/
private theorem hasIntegralCoordinates_halfYCurvePointZero :
    halfYCurvePointZero.HasIntegralCoordinates := by
  rw [halfYCurvePointZero]
  exact (WeierstrassCurve.Affine.Point.hasIntegralCoordinates_some _).mpr
    ⟨0, 0, by norm_num, by norm_num⟩

/-- **The negative of `(0, 0)` on `y² + ½y = x³` is `(0, -½)`**: negation is
`-(x, y) = (x, -y - a₁x - a₃)`, and here `a₁ = 0` and `a₃ = ½`. -/
private theorem neg_halfYCurvePointZero :
    ∃ h : halfYCurve.toAffine.Nonsingular 0 (-(1 / 2)),
      -halfYCurvePointZero = .some 0 (-(1 / 2)) h := by
  have hneg : halfYCurve.toAffine.negY 0 0 = -(1 / 2) := by
    simp [WeierstrassCurve.Affine.negY, halfYCurve]
  refine ⟨hneg ▸ (halfYCurve.toAffine.nonsingular_neg 0 0).mpr halfYCurve_nonsingular_zero,
    ?_⟩
  rw [halfYCurvePointZero, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, hneg⟩

/-- **On `y² + ½y = x³` the negative of the integral point `(0, 0)` is not integral**: its
ordinate is `-½`. -/
private theorem not_hasIntegralCoordinates_neg_halfYCurvePointZero :
    ¬ (-halfYCurvePointZero).HasIntegralCoordinates := by
  obtain ⟨_, hneg⟩ := neg_halfYCurvePointZero
  rw [hneg, WeierstrassCurve.Affine.Point.hasIntegralCoordinates_some]
  rintro ⟨_, y, _, hy⟩
  have h : (2 : ℚ) * (y : ℚ) = -1 := by
    rw [← hy]
    norm_num
  have h' : (2 : ℤ) * y = -1 := by
    exact_mod_cast h
  omega

/-- **Stability under negation fails on a general rational model**: there is a Weierstrass curve
over `ℚ` with a point whose two coordinates are integers and whose negative does not have integral
coordinates. On an equation over `ℤ` this cannot happen (`neg_mem_integralPoints`). -/
theorem exists_not_hasIntegralCoordinates_neg :
    ∃ (W : WeierstrassCurve ℚ) (P : W.toAffine.Point),
      P.HasIntegralCoordinates ∧ ¬ (-P).HasIntegralCoordinates :=
  ⟨halfYCurve, halfYCurvePointZero, hasIntegralCoordinates_halfYCurvePointZero,
    not_hasIntegralCoordinates_neg_halfYCurvePointZero⟩

/-! ### A change of variables with `u = 2` is not onto integral points -/

/-- The curve `y² = x³ + 3` over `ℚ`. -/
private def curveAddThree : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 3⟩

/-- The point `(1, 2)` of `y² = x³ + 3` is nonsingular. -/
private theorem curveAddThree_nonsingular : curveAddThree.toAffine.Nonsingular 1 2 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  refine ⟨?_, Or.inr ?_⟩
  · norm_num [curveAddThree]
  · norm_num [curveAddThree]

/-- The change of variables with `u = 2` and `r = s = t = 0`, which acts on a point of `C • W` as
`(x, y) ↦ (4x, 8y)`. -/
private def twoChange : WeierstrassCurve.VariableChange ℚ := ⟨Units.mk0 2 (by norm_num), 0, 0, 0⟩

/-- **A change of variables with `u = 2` is not onto integral points.** The hypothesis `u = ±1`
cannot be dropped: over `ℚ` the change with `u = 2` and `r = s = t = 0` is integral apart from the
unit, and it identifies the rational points of `C • W` with those of `W`, but it does not map the
integral points of `C • W` onto those of `W`. On `y² = x³ + 3` the integral point `(1, 2)` is the
image of `(1/4, 1/4)` of `C • W : y² = x³ + 3/64`, whose coordinates are not integers, and by
bijectivity on rational points that is its only preimage. Over `ℤ` the unit group is `{±1}`, and
there the identification is a bijection on integral points
(`bijOn_pointEquivVariableChange_integralPoints`). -/
theorem exists_not_surjOn_equivVariableChange_hasIntegralCoordinates :
    ∃ (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) (P : W.toAffine.Point),
      (C.u : ℚ) = 2 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ P.HasIntegralCoordinates ∧
        ∀ Q : (C • W).toAffine.Point,
          Q.HasIntegralCoordinates →
            WeierstrassCurve.Affine.Point.equivVariableChange W C Q ≠ P := by
  refine ⟨curveAddThree, twoChange, .some 1 2 curveAddThree_nonsingular, by simp [twoChange],
    rfl, rfl, rfl,
    (WeierstrassCurve.Affine.Point.hasIntegralCoordinates_some _).mpr
      ⟨1, 2, by norm_num, by norm_num⟩, ?_⟩
  rintro Q ⟨x, y, _, rfl⟩ hEq
  -- The identification sends `(x, y)` to `(4x, 8y)`, so the abscissa `1` of the image forces
  -- `4x = 1` in `ℤ`.
  rw [WeierstrassCurve.Affine.Point.equivVariableChange_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hEq
  obtain ⟨hx, -⟩ := hEq
  have h4 : (4 : ℤ) * x = 1 := by
    norm_num [twoChange] at hx
    exact_mod_cast hx
  omega

end TauCeti

end
