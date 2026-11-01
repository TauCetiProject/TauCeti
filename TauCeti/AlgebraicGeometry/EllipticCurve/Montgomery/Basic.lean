/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The monic model of a Montgomery curve

A **Montgomery curve** is the plane cubic `B y² = x³ + A x² + x`. Its leading coefficient in `y`
is `B` rather than `1`, so it is not itself a Weierstrass equation; the substitution
`x' = B x`, `y' = B² y` turns it into the monic equation

  `y'² = x'³ + A B x'² + B² x'`,

the Weierstrass curve `TauCeti.Montgomery.model A B` with coefficients `(0, A B, 0, B², 0)`.
Its discriminant is `16 B⁶ (A² - 4)`, so over a field it is elliptic exactly when `2`, `B` and
`A² - 4` are nonzero. Points of a Montgomery curve are taken to be the native points
`(model A B).toAffine.Point` of the monic model, with Mathlib's group law; no second group law
is introduced.

When `B ≠ 0` the affine point `(0, 0)` of the monic model is nonsingular and has order two; this
is the distinguished point of order two `TauCeti.Montgomery.twoTorsionPoint`, through which every
Montgomery curve has a rational point of order two. Over a domain with `B ≠ 0`, `(x, y)` solves
the Montgomery equation exactly when its image `(B x, B² y)` under the substitution above solves
the equation of the monic model, and likewise for nonsingular points; no square root of `B` is
needed. Over a field this substitution is therefore a bijection between the two solution sets.

This is the setting of Montgomery's `x`-only arithmetic, used in Lenstra's elliptic-curve
factorization method: the projective `x`-coordinate of a native point determines it up to sign,
and doubling and differential addition can be computed on it alone.

## Main definitions

* `TauCeti.Montgomery.model A B`: the Weierstrass curve `y² = x³ + A B x² + B² x`.
* `TauCeti.Montgomery.twoTorsionPoint`: the native point `(0, 0)` of `model A B` over a domain,
  for `B ≠ 0`.

## Main results

* `TauCeti.Montgomery.model_Δ`: the discriminant of `model A B` is `16 B⁶ (A² - 4)`.
* `TauCeti.Montgomery.isElliptic_model_iff`: `model A B` is elliptic exactly when `2`, `B` and
  `A² - 4` are units; `TauCeti.Montgomery.isElliptic_model_iff_ne_zero` is the field version.
* `TauCeti.Montgomery.map_model`: base change of `model A B` along a ring homomorphism `f` is
  `model (f A) (f B)`.
* `TauCeti.Montgomery.model_eq_model_iff`: two models agree exactly when their `A B` and `B²`
  coefficients do; over a domain with `B ≠ 0`,
  `TauCeti.Montgomery.model_eq_model_iff_of_ne_zero` says this happens exactly for
  `(A', B') = (A, B)` and `(A', B') = (-A, -B)`.
* `TauCeti.Montgomery.some_eq_twoTorsionPoint_iff`: it is the only affine point with
  `x`-coordinate `0`.
* `TauCeti.Montgomery.addOrderOf_twoTorsionPoint`: over a field, `(0, 0)` has order two.
* `TauCeti.Montgomery.equation_model_iff` and `TauCeti.Montgomery.nonsingular_model_iff`: for
  `B ≠ 0` over a domain, `(x, y)` satisfies `B y² = x³ + A x² + x` (and is a nonsingular point of
  that cubic) exactly when `(B x, B² y)` satisfies the equation of `model A B` (and is a
  nonsingular point of it).

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, equation (10.3.1.1).
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R]

/-- The **monic model** of the Montgomery curve `B y² = x³ + A x² + x`: the Weierstrass curve
`y² = x³ + A B x² + B² x`, reached by `x' = B x`, `y' = B² y`. Its coefficients are
`(a₁, a₂, a₃, a₄, a₆) = (0, A B, 0, B², 0)`. -/
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

/-- The `c₄` of the monic model is `16 B² (A² - 3)`. -/
@[simp]
theorem model_c₄ : (model A B).c₄ = 16 * B ^ 2 * (A ^ 2 - 3) := by
  simp [c₄]
  ring

/-- The `c₆` of the monic model is `-32 A B³ (2 A² - 9)`. -/
@[simp]
theorem model_c₆ : (model A B).c₆ = -32 * A * B ^ 3 * (2 * A ^ 2 - 9) := by
  simp [c₆]
  ring

/-- **The discriminant of the monic Montgomery model** is `16 B⁶ (A² - 4)`. -/
@[simp]
theorem model_Δ : (model A B).Δ = 16 * B ^ 6 * (A ^ 2 - 4) := by
  simp [Δ]
  ring

/-- The image of the monic model under a ring homomorphism is the monic model of the images. -/
@[simp]
theorem map_model {S : Type*} [CommRing S] (f : R →+* S) :
    (model A B).map f = model (f A) (f B) := by
  ext <;> simp

/-- **The monic Montgomery model is elliptic exactly when `2`, `B` and `A² - 4` are units.** -/
theorem isElliptic_model_iff :
    (model A B).IsElliptic ↔ IsUnit (2 : R) ∧ IsUnit B ∧ IsUnit (A ^ 2 - 4) := by
  rw [isElliptic_iff, model_Δ, show (16 : R) = 2 ^ 4 by norm_num]
  simp only [IsUnit.mul_iff, isUnit_pow_iff (by norm_num : (4 : ℕ) ≠ 0),
    isUnit_pow_iff (by norm_num : (6 : ℕ) ≠ 0), and_assoc]

variable {A B} in
/-- Two monic models are equal exactly when their `a₂ = A B` and `a₄ = B²` coefficients agree. -/
theorem model_eq_model_iff {A' B' : R} :
    model A B = model A' B' ↔ A * B = A' * B' ∧ B ^ 2 = B' ^ 2 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₂, h₄⟩ ↦ ?_⟩
  · simpa using congr_arg WeierstrassCurve.a₂ h
  · simpa using congr_arg WeierstrassCurve.a₄ h
  · ext <;> simp [h₂, h₄]

/-- The affine point `(0, 0)` of the monic model is nonsingular exactly when `B² ≠ 0`: the
partial derivative of the equation in `x` there is `-B²`. -/
theorem nonsingular_model_zero_zero : (model A B).toAffine.Nonsingular 0 0 ↔ B ^ 2 ≠ 0 := by
  simp [Affine.nonsingular_zero]

end CommRing

section Domain

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {A B : R}

/-- Over a domain, two monic models with `B ≠ 0` are equal exactly when `(A', B')` is `(A, B)`
or `(-A, -B)`. -/
theorem model_eq_model_iff_of_ne_zero (hB : B ≠ 0) {A' B' : R} :
    model A B = model A' B' ↔ A' = A ∧ B' = B ∨ A' = -A ∧ B' = -B := by
  rw [model_eq_model_iff]
  constructor
  · rintro ⟨h₂, h₄⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₄.symm with rfl | rfl
    · exact Or.inl ⟨mul_right_cancel₀ hB h₂.symm, rfl⟩
    · refine Or.inr ⟨mul_right_cancel₀ hB ?_, rfl⟩
      linear_combination h₂
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> ring

/-- **The Montgomery equation and the monic model.** For `B ≠ 0` over a domain, `(x, y)`
satisfies `B y² = x³ + A x² + x` exactly when `(B x, B² y)` lies on `model A B`. -/
theorem equation_model_iff (hB : B ≠ 0) (x y : R) :
    (model A B).toAffine.Equation (B * x) (B ^ 2 * y) ↔ B * y ^ 2 = x ^ 3 + A * x ^ 2 + x := by
  rw [Affine.equation_iff]
  simp only [model_a₁, model_a₂, model_a₃, model_a₄, model_a₆, zero_mul, add_zero]
  constructor
  · intro h
    refine mul_left_cancel₀ (pow_ne_zero 3 hB) ?_
    linear_combination h
  · intro h
    linear_combination B ^ 3 * h

/-- **Nonsingularity on the Montgomery curve and on the monic model.** For `B ≠ 0` over a domain,
`(x, y)` is a nonsingular point of `B y² = x³ + A x² + x`, that is, it lies on the curve and one
of the partial derivatives `3 x² + 2 A x + 1` and `2 B y` is nonzero, exactly when `(B x, B² y)` is
a nonsingular point of `model A B`. -/
theorem nonsingular_model_iff (hB : B ≠ 0) (x y : R) :
    (model A B).toAffine.Nonsingular (B * x) (B ^ 2 * y) ↔
      B * y ^ 2 = x ^ 3 + A * x ^ 2 + x ∧ (3 * x ^ 2 + 2 * A * x + 1 ≠ 0 ∨ 2 * B * y ≠ 0) := by
  rw [Affine.nonsingular_iff', equation_model_iff hB]
  simp only [model_a₁, model_a₂, model_a₃, model_a₄, zero_mul, add_zero, zero_sub, ne_eq,
    neg_eq_zero]
  have h₁ : 3 * (B * x) ^ 2 + 2 * (A * B) * (B * x) + B ^ 2 =
      B ^ 2 * (3 * x ^ 2 + 2 * A * x + 1) := by ring
  have h₂ : 2 * (B ^ 2 * y) = B * (2 * B * y) := by ring
  rw [h₁, h₂, mul_eq_zero, mul_eq_zero, pow_eq_zero_iff two_ne_zero]
  simp [hB]

variable (A) in
/-- The **distinguished point of order two** `T₀` of the monic Montgomery model, the affine point
`(0, 0)`, defined when `B ≠ 0`. -/
def twoTorsionPoint (hB : B ≠ 0) : (model A B).toAffine.Point :=
  .some 0 0 ((nonsingular_model_zero_zero A B).mpr (pow_ne_zero 2 hB))

variable (A) in
/-- The distinguished point of order two is the affine point `(0, 0)` of the monic model. -/
theorem twoTorsionPoint_def (hB : B ≠ 0) :
    twoTorsionPoint A hB = .some 0 0 ((nonsingular_model_zero_zero A B).mpr (pow_ne_zero 2 hB)) :=
  (rfl)

/-- An affine point of the monic model is the distinguished point of order two exactly when its
`x`-coordinate is `0`: the equation forces `y² = 0` there. -/
theorem some_eq_twoTorsionPoint_iff (hB : B ≠ 0) {x y : R}
    (h : (model A B).toAffine.Nonsingular x y) :
    Affine.Point.some x y h = twoTorsionPoint A hB ↔ x = 0 := by
  refine ⟨fun hT ↦ (Affine.Point.some.inj hT).1, fun hx ↦ ?_⟩
  subst hx
  have hy : y ^ 2 = 0 := by simpa [Affine.equation_iff] using h.1
  obtain rfl := pow_eq_zero_iff two_ne_zero |>.mp hy
  rfl

variable (A) in
/-- The distinguished point of order two is not the point at infinity. -/
theorem twoTorsionPoint_ne_zero (hB : B ≠ 0) : twoTorsionPoint A hB ≠ 0 :=
  Affine.Point.some_ne_zero _

variable (A) in
/-- The distinguished point of order two is its own negative. -/
@[simp]
theorem neg_twoTorsionPoint (hB : B ≠ 0) : -twoTorsionPoint A hB = twoTorsionPoint A hB := by
  simp [twoTorsionPoint, Affine.negY]

end Domain

section Field

variable {K : Type*} [Field K] {A B : K}

/-- **The monic Montgomery model over a field** is elliptic exactly when `2`, `B` and `A² - 4`
are nonzero. -/
theorem isElliptic_model_iff_ne_zero :
    (model A B).IsElliptic ↔ (2 : K) ≠ 0 ∧ B ≠ 0 ∧ A ^ 2 ≠ 4 := by
  simp [isElliptic_model_iff, sub_eq_zero]

variable [DecidableEq K]

variable (A) in
/-- The distinguished point of order two is killed by `2`. -/
@[simp]
theorem twoTorsionPoint_add_self (hB : B ≠ 0) :
    twoTorsionPoint A hB + twoTorsionPoint A hB = 0 :=
  Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])

variable (A) in
/-- **The distinguished point `(0, 0)` has order two** in the native group of the monic model. -/
@[simp]
theorem addOrderOf_twoTorsionPoint (hB : B ≠ 0) : addOrderOf (twoTorsionPoint A hB) = 2 :=
  addOrderOf_eq_prime (by rw [two_nsmul, twoTorsionPoint_add_self]) (twoTorsionPoint_ne_zero A hB)

end Field

end TauCeti.Montgomery
