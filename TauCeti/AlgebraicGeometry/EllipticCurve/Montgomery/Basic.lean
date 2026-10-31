/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The monic model of a Montgomery curve

A **Montgomery curve** is the plane cubic `B y² = x³ + A x² + x`. Its leading coefficient `B` is
in general not a square, so it is not itself a Weierstrass equation. The substitution
`x' = B x`, `y' = B² y` multiplies the equation by `B³` and turns it into the monic Weierstrass
equation

  `y'² = x'³ + A B x'² + B² x'`,

with coefficients `(a₁, a₂, a₃, a₄, a₆) = (0, A B, 0, B², 0)`. This is
`TauCeti.Montgomery.model A B`. Over a field, the native points of a Montgomery curve are the
points of Mathlib's group `(Montgomery.model A B).toAffine.Point`; no second group law is
introduced, and the `x`-only arithmetic of Montgomery's elliptic-curve method (doubling and
differential addition on projective `x`-coordinates) computes `x`-coordinates of points of this
group.

The discriminant of the model is `16 B⁶ (A² - 4)` over every commutative ring, so over a field the
model is elliptic exactly when `2`, `B` and `A² - 4` are nonzero. When `B ≠ 0`, the affine point
`(0, 0)` lies on the model and is nonsingular, since the cubic `x'³ + A B x'² + B² x'` has
derivative `B²` at `x' = 0`. Over a field it has order `2`: this is the distinguished `2`-torsion
point `T₀` of the Montgomery curve.
No square root of `B` is needed to compare the two equations: when `B ≠ 0` (over a ring without
zero divisors), `(x, y)` lies on `B y² = x³ + A x² + x` exactly when `(B x, B² y)` lies on the
model, and the substitution preserves and reflects nonsingularity.

## Main definitions

* `TauCeti.Montgomery.model A B`: the Weierstrass curve `y'² = x'³ + A B x'² + B² x'`.
* `TauCeti.Montgomery.twoTorsionPoint`: for `B ≠ 0`, the native point `T₀ = (0, 0)` of the model.

## Main results

* `TauCeti.Montgomery.model_Δ`: the discriminant of the model is `16 B⁶ (A² - 4)`.
* `TauCeti.Montgomery.isElliptic_model_iff` and `TauCeti.Montgomery.isElliptic_model_iff_ne_zero`:
  the model is elliptic exactly when `2`, `B` and `A² - 4` are units, respectively, over a field,
  nonzero.
* `TauCeti.Montgomery.map_model`: base change of the model along a ring homomorphism.
* `TauCeti.Montgomery.model_eq_model_iff` and
  `TauCeti.Montgomery.model_eq_model_iff_of_ne_zero`: two models are equal exactly when their
  coefficients `A B` and `B²` agree; over a domain with `B ≠ 0`, exactly when
  `(A', B') = ±(A, B)`.
* `TauCeti.Montgomery.addOrderOf_twoTorsionPoint`: over a field, `T₀` has order `2` in the native
  group.
* `TauCeti.Montgomery.equation_model_iff` and `TauCeti.Montgomery.nonsingular_model_iff`: the
  substitution `(x, y) ↦ (B x, B² y)` carries the Montgomery equation and its nonsingular points
  to those of the model, and back.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*, Math.
  Comp. 48 (1987), 243–264, §10.3.1, equation (10.3.1.1).
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R]

/-- The **monic model of the Montgomery curve** `B y² = x³ + A x² + x`: the Weierstrass curve
`y'² = x'³ + A B x'² + B² x'`, reached from the Montgomery equation by `x' = B x`, `y' = B² y`.
Its coefficients are `(a₁, a₂, a₃, a₄, a₆) = (0, A B, 0, B², 0)`. -/
def model (A B : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := A * B
  a₃ := 0
  a₄ := B ^ 2
  a₆ := 0

variable (A B : R)

@[simp] theorem model_a₁ : (model A B).a₁ = 0 := (rfl)
@[simp] theorem model_a₂ : (model A B).a₂ = A * B := (rfl)
@[simp] theorem model_a₃ : (model A B).a₃ = 0 := (rfl)
@[simp] theorem model_a₄ : (model A B).a₄ = B ^ 2 := (rfl)
@[simp] theorem model_a₆ : (model A B).a₆ = 0 := (rfl)

@[simp]
theorem model_b₂ : (model A B).b₂ = 4 * (A * B) := by
  simp [b₂]

@[simp]
theorem model_b₄ : (model A B).b₄ = 2 * B ^ 2 := by
  simp [b₄]

@[simp]
theorem model_b₆ : (model A B).b₆ = 0 := by
  simp [b₆]

@[simp]
theorem model_b₈ : (model A B).b₈ = -B ^ 4 := by
  simp [b₈]
  ring

/-- The discriminant of the monic Montgomery model is `16 B⁶ (A² - 4)`. -/
@[simp]
theorem model_Δ : (model A B).Δ = 16 * B ^ 6 * (A ^ 2 - 4) := by
  simp [Δ]
  ring

/-- The image of the monic Montgomery model under a ring homomorphism is the model of the
images of its coefficients. -/
@[simp]
theorem map_model {S : Type*} [CommRing S] (f : R →+* S) :
    (model A B).map f = model (f A) (f B) := by
  ext <;> simp

/-- **The monic Montgomery model is elliptic exactly when `2`, `B` and `A² - 4` are units**,
that is, when its discriminant `16 B⁶ (A² - 4)` is a unit. -/
theorem isElliptic_model_iff :
    (model A B).IsElliptic ↔ IsUnit (2 : R) ∧ IsUnit B ∧ IsUnit (A ^ 2 - 4) := by
  rw [isElliptic_iff, model_Δ, show (16 : R) = 2 ^ 4 by norm_num]
  simp only [IsUnit.mul_iff, isUnit_pow_iff (by norm_num : (4 : ℕ) ≠ 0),
    isUnit_pow_iff (by norm_num : (6 : ℕ) ≠ 0), and_assoc]

variable {A B}

/-- Two monic Montgomery models are equal exactly when their coefficients `a₂ = A B` and
`a₄ = B²` agree. -/
theorem model_eq_model_iff {A' B' : R} :
    model A B = model A' B' ↔ A * B = A' * B' ∧ B ^ 2 = B' ^ 2 := by
  refine ⟨fun h ↦ ⟨congr_arg a₂ h, congr_arg a₄ h⟩, fun ⟨h₂, h₄⟩ ↦ ?_⟩
  ext <;> simp [h₂, h₄]

/-- The affine point `(0, 0)` is a nonsingular point of the monic Montgomery model exactly when
`B² ≠ 0`: the cubic `x'³ + A B x'² + B² x'` vanishes at `x' = 0` with derivative `B²` there. -/
theorem nonsingular_model_zero_zero_iff : (model A B).toAffine.Nonsingular 0 0 ↔ B ^ 2 ≠ 0 := by
  simp

end CommRing

section NoZeroDivisors

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {A B : R}

/-- Over a ring without zero divisors, the monic Montgomery model of a Montgomery curve with
`B ≠ 0` and that with coefficients `(A', B')` are equal exactly when `(A', B') = ±(A, B)`. -/
theorem model_eq_model_iff_of_ne_zero (hB : B ≠ 0) {A' B' : R} :
    model A B = model A' B' ↔ A' = A ∧ B' = B ∨ A' = -A ∧ B' = -B := by
  rw [model_eq_model_iff]
  constructor
  · rintro ⟨h₂, h₄⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₄.symm with rfl | rfl
    · exact .inl ⟨mul_right_cancel₀ hB (by simpa using h₂.symm), rfl⟩
    · exact .inr ⟨mul_right_cancel₀ hB (by linear_combination h₂), rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨rfl, rfl⟩
    · exact ⟨by ring, by ring⟩

/-- The affine point `(0, 0)` is a nonsingular point of the monic Montgomery model when
`B ≠ 0`. -/
theorem nonsingular_model_zero_zero (hB : B ≠ 0) : (model A B).toAffine.Nonsingular 0 0 :=
  nonsingular_model_zero_zero_iff.mpr (pow_ne_zero 2 hB)

variable (A) in
/-- The **distinguished `2`-torsion point** `T₀ = (0, 0)` of the monic model of a Montgomery
curve with `B ≠ 0`. It corresponds to the point `(0, 0)` of `B y² = x³ + A x² + x`, and over a
field it has order `2` in the native group (`addOrderOf_twoTorsionPoint`). -/
def twoTorsionPoint (hB : B ≠ 0) : (model A B).toAffine.Point :=
  .some 0 0 (nonsingular_model_zero_zero hB)

theorem twoTorsionPoint_def (hB : B ≠ 0) :
    twoTorsionPoint A hB = .some 0 0 (nonsingular_model_zero_zero hB) := (rfl)

@[simp]
theorem twoTorsionPoint_ne_zero (hB : B ≠ 0) : twoTorsionPoint A hB ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- The distinguished `2`-torsion point is its own negative. -/
@[simp]
theorem neg_twoTorsionPoint (hB : B ≠ 0) : -twoTorsionPoint A hB = twoTorsionPoint A hB := by
  simp [twoTorsionPoint, Affine.Point.neg_some, Affine.negY]

/-- **Montgomery's equation and the monic model.** For `B ≠ 0`, over a ring without zero
divisors, `(x, y)` satisfies `B y² = x³ + A x² + x` exactly when `(B x, B² y)` satisfies the
equation `y'² = x'³ + A B x'² + B² x'` of the monic model. No square root of `B` is needed. -/
theorem equation_model_iff (hB : B ≠ 0) {x y : R} :
    (model A B).toAffine.Equation (B * x) (B ^ 2 * y) ↔ B * y ^ 2 = x ^ 3 + A * x ^ 2 + x := by
  rw [Affine.equation_iff]
  simp only [model_a₁, model_a₂, model_a₃, model_a₄, model_a₆]
  refine ⟨fun h ↦ ?_, fun h ↦ by linear_combination B ^ 3 * h⟩
  have h' : B ^ 3 * (B * y ^ 2 - (x ^ 3 + A * x ^ 2 + x)) = 0 := by linear_combination h
  simpa [hB, sub_eq_zero] using h'

/-- **Nonsingular points of Montgomery's equation and of the monic model.** For `B ≠ 0`, over a
ring without zero divisors, `(B x, B² y)` is a nonsingular point of the monic model exactly when
`(x, y)` is a nonsingular point of `B y² = x³ + A x² + x`, that is, a point of this curve at which
one of the partial derivatives `3 x² + 2 A x + 1` and `2 B y` is nonzero. -/
theorem nonsingular_model_iff (hB : B ≠ 0) {x y : R} :
    (model A B).toAffine.Nonsingular (B * x) (B ^ 2 * y) ↔
      B * y ^ 2 = x ^ 3 + A * x ^ 2 + x ∧ (3 * x ^ 2 + 2 * A * x + 1 ≠ 0 ∨ 2 * B * y ≠ 0) := by
  have hX : (model A B).toAffine.polynomialX.evalEval (B * x) (B ^ 2 * y) =
      -(B ^ 2 * (3 * x ^ 2 + 2 * A * x + 1)) := by
    rw [Affine.evalEval_polynomialX]
    simp only [model_a₁, model_a₂, model_a₄]
    ring
  have hY : (model A B).toAffine.polynomialY.evalEval (B * x) (B ^ 2 * y) = B * (2 * B * y) := by
    rw [Affine.evalEval_polynomialY]
    simp only [model_a₁, model_a₃]
    ring
  rw [Affine.Nonsingular, hX, hY, equation_model_iff hB]
  simp [hB]

end NoZeroDivisors

section Field

variable {K : Type*} [Field K] {A B : K}

/-- **Over a field, the monic Montgomery model is elliptic exactly when `2`, `B` and `A² - 4`
are nonzero.** -/
theorem isElliptic_model_iff_ne_zero :
    (model A B).IsElliptic ↔ (2 : K) ≠ 0 ∧ B ≠ 0 ∧ A ^ 2 ≠ 4 := by
  simp [isElliptic_model_iff, sub_eq_zero]

variable [DecidableEq K]

/-- The distinguished `2`-torsion point added to itself is the point at infinity. -/
@[simp]
theorem twoTorsionPoint_add_self (hB : B ≠ 0) :
    twoTorsionPoint A hB + twoTorsionPoint A hB = 0 :=
  Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])

/-- The distinguished `2`-torsion point `T₀ = (0, 0)` has order `2` in the native group of the
monic Montgomery model. -/
@[simp]
theorem addOrderOf_twoTorsionPoint (hB : B ≠ 0) : addOrderOf (twoTorsionPoint A hB) = 2 :=
  addOrderOf_eq_prime (by simp [two_nsmul]) (twoTorsionPoint_ne_zero hB)

end Field

end TauCeti.Montgomery
