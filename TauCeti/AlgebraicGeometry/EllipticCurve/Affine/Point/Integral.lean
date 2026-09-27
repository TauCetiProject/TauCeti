/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.Data.Int.Quadratic
import Mathlib.Data.Int.Interval

/-!
# Integral points of an integral Weierstrass equation

An integral point is an affine rational point whose two coordinates come from `ℤ`. The equation
is kept over `ℤ`, so negation preserves integral points even when the model is not short. A finite
search over a box of integer coordinates gives a certificate for every point in that box. No
finiteness assertion is made for the set of all integral points.

The set depends on the integral equation, rather than only on its rational isomorphism class.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.
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
private theorem integral_equation_baseChange (x y : ℤ) (h : W.toAffine.Equation x y) :
    (W.baseChange ℚ).toAffine.Equation (x : ℚ) (y : ℚ) := by
  rw [W.integral_toAffine_baseChange]
  exact h.map (Int.castRingHom ℚ)

/-- An integral solution of the affine Weierstrass equation determines a rational point. -/
def pointOfIntegralSolution (x y : ℤ) (h : W.toAffine.Equation x y) :
    (W.baseChange ℚ).toAffine.Point :=
  .mk (W.integral_equation_baseChange x y h)

/-- The affine coordinates of the rational point constructed from an integral solution. -/
@[simp]
theorem pointEquiv_pointOfIntegralSolution (x y : ℤ) (h : W.toAffine.Equation x y) :
    (W.baseChange ℚ).toAffine.pointEquiv (W.pointOfIntegralSolution x y h) =
      .some ⟨⟨(x : ℚ), (y : ℚ)⟩, by
        exact W.integral_equation_baseChange x y h⟩ := by
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
  · rintro ⟨⟨x, hx, y, hy, hp⟩, heq⟩
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

end WeierstrassCurve

end
