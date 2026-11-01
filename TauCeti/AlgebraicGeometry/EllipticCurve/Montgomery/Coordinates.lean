/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Pair

/-!
# The coordinate pair and the projective `x`-coordinate of a Montgomery point

A native point of the monic Montgomery model `TauCeti.Montgomery.model A B`, the Weierstrass
curve `y'² = x'³ + A B x'² + B² x'`, comes from the point `(x, y) = (x' / B, y' / B²)` of the
Montgomery curve `B y² = x³ + A x² + x`. Montgomery's `x`-only arithmetic tracks the Montgomery
coordinate `x = x' / B` as a raw pair, so the **coordinate pair** of a native point is `(1, 0)`
at infinity and `(x', B)` at an affine point `(x', y')`. It is Mathlib's
`WeierstrassCurve.Affine.Point.xRep`, which represents the Weierstrass coordinate `x'`, with its
second entry scaled by `B`.

For `B ≠ 0` the coordinate pair is never `(0, 0)`; its second field vanishes exactly at infinity
and its first field exactly at the distinguished point of order two `(0, 0)`. It is invariant
under negation. Over a field, the coordinate pair defines the **projective `x`-coordinate**, a
point of `ℙ K (Fin 2 → K)`, and two native points have the same projective `x`-coordinate, or
equivalently coordinate pairs with vanishing cross difference, exactly when they are equal or
negatives of each other. This is what makes `x`-only arithmetic well defined on the native
point group up to sign.

The projective `x`-coordinate need not be surjective: when `model A B` is elliptic (`2 ≠ 0`,
`B ≠ 0` and `A² ≠ 4`, so every solution is nonsingular), `(r : 1)` comes from a `K`-rational
point exactly when `(r³ + A r² + r) / B` is a square in `K`.

## Main definitions

* `TauCeti.Montgomery.coordinates A B P`: the coordinate pair of a native point `P` of
  `model A B`.
* `TauCeti.Montgomery.projectiveX A hB P`: the projective `x`-coordinate of `P` over a field,
  for `hB : B ≠ 0`.

## Main results

* `TauCeti.Montgomery.coordinates_ne_zero`: for `B ≠ 0` the coordinate pair is nonzero.
* `TauCeti.Montgomery.coordinates_z_eq_zero_iff` and
  `TauCeti.Montgomery.coordinates_x_eq_zero_iff`: its fields vanish exactly at infinity and at
  the distinguished point of order two, respectively.
* `TauCeti.Montgomery.coordinates_neg`: the coordinate pair of `-P` is that of `P`.
* `TauCeti.Montgomery.cross_coordinates_eq_zero_iff`: over a domain, the coordinate pairs of `P`
  and `Q` have vanishing cross difference exactly when `P = Q` or `P = -Q`.
* `TauCeti.Montgomery.projectiveX_eq_projectiveX_iff`: the fibres of the projective
  `x`-coordinate are the sets `{P, -P}`.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve
open scoped LinearAlgebra.Projectivization

section CommRing

variable {R : Type*} [CommRing R]

/-- The **coordinate pair** of a native point of the monic Montgomery model `model A B`: `(1, 0)`
at infinity and `(x', B)` at the affine point `(x', y')`, which stands for the Montgomery
coordinate `x = x' / B`. It is Mathlib's `xRep` with its second entry scaled by `B`. -/
noncomputable def coordinates (A B : R) (P : (model A B).toAffine.Point) : Pair R :=
  ⟨P.xRep 0, B * P.xRep 1⟩

variable (A B : R)

/-- The coordinate pair of the point at infinity is `(1, 0)`. -/
@[simp]
theorem coordinates_zero : coordinates A B 0 = ⟨1, 0⟩ := by
  simp [coordinates]

/-- The coordinate pair of the affine point `(x', y')` is `(x', B)`. -/
@[simp]
theorem coordinates_some {x y : R} (h : (model A B).toAffine.Nonsingular x y) :
    coordinates A B (.some x y h) = ⟨x, B⟩ := by
  simp [coordinates]

/-- The coordinate pair is invariant under negation. -/
@[simp]
theorem coordinates_neg (P : (model A B).toAffine.Point) :
    coordinates A B (-P) = coordinates A B P := by
  simp [coordinates]

variable {A B}

/-- For `B ≠ 0`, the coordinate pair of a native point is nonzero. -/
@[simp]
theorem coordinates_ne_zero (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    coordinates A B P ≠ 0 := by
  have : Nontrivial R := nontrivial_of_ne B 0 hB
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def, Pair.eq_zero_iff]
  · simp [Pair.eq_zero_iff, hB]

/-- For `B ≠ 0`, the second field of the coordinate pair vanishes exactly at infinity. -/
@[simp]
theorem coordinates_z_eq_zero_iff (hB : B ≠ 0) {P : (model A B).toAffine.Point} :
    (coordinates A B P).z = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  · simp [hB, Affine.Point.some_ne_zero]

end CommRing

section Domain

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {A B : R}

/-- For `B ≠ 0`, the first field of the coordinate pair vanishes exactly at the distinguished
point of order two `(0, 0)`. -/
@[simp]
theorem coordinates_x_eq_zero_iff (hB : B ≠ 0) {P : (model A B).toAffine.Point} :
    (coordinates A B P).x = 0 ↔ P = twoTorsionPoint A hB := by
  have : Nontrivial R := nontrivial_of_ne B 0 hB
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, coordinates_zero, one_ne_zero, false_iff]
    exact (twoTorsionPoint_ne_zero A hB).symm
  · rw [coordinates_some, some_eq_twoTorsionPoint_iff hB]

/-- **The coordinate pairs of two native points have vanishing cross difference exactly when the
points are equal or negatives of each other**, for `B ≠ 0` over a domain. This includes the case
where one of them is the point at infinity. -/
theorem cross_coordinates_eq_zero_iff (hB : B ≠ 0) {P Q : (model A B).toAffine.Point} :
    (coordinates A B P).cross (coordinates A B Q) = 0 ↔ P = Q ∨ P = -Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · simp [← Affine.Point.zero_def]
  · simp [← Affine.Point.zero_def, Pair.cross_def, hB, (Affine.Point.some_ne_zero _).symm]
  · simp [← Affine.Point.zero_def, Pair.cross_def, hB, Affine.Point.some_ne_zero]
  · rw [coordinates_some, coordinates_some, Pair.cross_def, ← sub_mul, mul_eq_zero, sub_eq_zero,
      or_iff_left hB]
    refine ⟨fun hx ↦ ?_, by rintro (h | h) <;> simp_all [Affine.Point.neg_some]⟩
    subst hx
    have e₁ := (Affine.equation_iff ..).mp h₁.1
    have e₂ := (Affine.equation_iff ..).mp h₂.1
    simp_rw [Affine.Point.neg_some, Affine.Point.some.injEq, true_and, ← sub_eq_zero (a := y₁),
      ← mul_eq_zero, Affine.negY]
    linear_combination e₁ - e₂

end Domain

section Field

variable {K : Type*} [Field K] {A B : K}

/-- The **projective `x`-coordinate** of a native point of `model A B` over a field, for
`B ≠ 0`: the point of the projective line `ℙ K (Fin 2 → K)` defined by its coordinate pair. It is
`(1 : 0)` at infinity and `(x' : B)` at the affine point `(x', y')`. -/
noncomputable def projectiveX (A : K) (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    ℙ K (Fin 2 → K) :=
  (coordinates A B P).toProj (coordinates_ne_zero hB P)

theorem projectiveX_def (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    projectiveX A hB P = (coordinates A B P).toProj (coordinates_ne_zero hB P) := (rfl)

/-- **The fibres of the projective `x`-coordinate.** Two native points have the same projective
`x`-coordinate exactly when they are equal or negatives of each other. -/
theorem projectiveX_eq_projectiveX_iff (hB : B ≠ 0) {P Q : (model A B).toAffine.Point} :
    projectiveX A hB P = projectiveX A hB Q ↔ P = Q ∨ P = -Q := by
  rw [projectiveX_def, projectiveX_def, Pair.toProj_eq_toProj_iff,
    cross_coordinates_eq_zero_iff hB]

/-- The projective `x`-coordinate is invariant under negation. -/
@[simp]
theorem projectiveX_neg (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    projectiveX A hB (-P) = projectiveX A hB P :=
  (projectiveX_eq_projectiveX_iff hB).mpr (.inr rfl)

end Field

end TauCeti.Montgomery
