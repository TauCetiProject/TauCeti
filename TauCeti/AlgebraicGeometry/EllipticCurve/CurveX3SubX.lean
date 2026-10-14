/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The curve `y² = x³ - x`

The Weierstrass curve `y² = x³ - x` has discriminant `64`, so it is an elliptic curve over every
field of characteristic other than two. Its points of order dividing two are the point at infinity
`O` and the three points `T₀ = (0, 0)`, `T₁ = (1, 0)` and `T₋₁ = (-1, 0)` on the line `y = 0`, all
rational over the base field.

## Main definitions

* `TauCeti.CurveX3SubX.curve`: the Weierstrass curve `y² = x³ - x`.
* `TauCeti.CurveX3SubX.pointZero`, `TauCeti.CurveX3SubX.pointOne`,
  `TauCeti.CurveX3SubX.pointNegOne`: its affine points of order two.

## Main results

* `TauCeti.CurveX3SubX.curve_a₁` and its siblings: the coefficients of `y² = x³ - x`.
* `TauCeti.CurveX3SubX.Δ_curve`: the discriminant of `y² = x³ - x` is `64`.
* `TauCeti.CurveX3SubX.map_curve`: `y² = x³ - x` is preserved by every ring homomorphism.
* `TauCeti.CurveX3SubX.pointZero_ne_pointOne` and its siblings: `O`, `T₀`, `T₁` and `T₋₁` are
  pairwise distinct.
* `TauCeti.CurveX3SubX.neg_eq_self_iff`: the points of order dividing two are `O`, `T₀`, `T₁`
  and `T₋₁`.
-/

public section

open WeierstrassCurve

namespace TauCeti.CurveX3SubX

/-- The Weierstrass curve `y² = x³ - x`. -/
def curve (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

section Coefficients

variable (R : Type*) [CommRing R]

/-- The coefficient `a₁` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₁ : (curve R).a₁ = 0 :=
  (rfl)

/-- The coefficient `a₂` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₂ : (curve R).a₂ = 0 :=
  (rfl)

/-- The coefficient `a₃` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₃ : (curve R).a₃ = 0 :=
  (rfl)

/-- The coefficient `a₄` of `y² = x³ - x` is `-1`. -/
@[simp]
theorem curve_a₄ : (curve R).a₄ = -1 :=
  (rfl)

/-- The coefficient `a₆` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₆ : (curve R).a₆ = 0 :=
  (rfl)

end Coefficients

/-- The discriminant of `y² = x³ - x` is `64`. -/
@[simp]
theorem Δ_curve (R : Type*) [CommRing R] : (curve R).Δ = 64 := by
  simp only [Δ, b₂, b₄, b₆, b₈, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  ring

/-- `y² = x³ - x` is defined over `ℤ`, so it is preserved by every ring homomorphism. -/
@[simp]
theorem map_curve {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (curve R).map f = curve S := by
  ext <;> simp

/-- The affine points of `y² = x³ - x` are the solutions of `y² = x³ - x`. -/
@[simp]
theorem equation_iff {R : Type*} [CommRing R] (x y : R) :
    (curve R).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [Affine.equation_iff]
  simp only [curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  constructor <;> intro h <;> linear_combination h

variable (K : Type*) [Field K]

/-- Away from characteristic two, `y² = x³ - x` is an elliptic curve: its discriminant
`64 = 2⁶` is a unit. -/
instance [NeZero (2 : K)] : (curve K).IsElliptic := by
  rw [isElliptic_iff, Δ_curve]
  convert (Ne.isUnit (NeZero.ne (2 : K))).pow 6 using 1
  norm_num

/-- The point `T₀ = (0, 0)` of `y² = x³ - x`. It is a nonsingular point in every characteristic,
including two. -/
def pointZero : (curve K).toAffine.Point :=
  .some 0 0 (Affine.nonsingular_zero.mpr ⟨curve_a₆ K, .inr (by simp)⟩)

variable {K} in
/-- `T₀` is not the point at infinity. -/
@[simp]
theorem pointZero_ne_zero : pointZero K ≠ 0 := by
  simp [pointZero, Affine.Point.zero_def]

variable [NeZero (2 : K)]

/-- The point `T₁ = (1, 0)` of `y² = x³ - x`. -/
def pointOne : (curve K).toAffine.Point :=
  .mk ((equation_iff 1 0).mpr (by ring))

/-- The point `T₋₁ = (-1, 0)` of `y² = x³ - x`. -/
def pointNegOne : (curve K).toAffine.Point :=
  .mk ((equation_iff (-1) 0).mpr (by ring))

variable {K}

/-- `T₁` is not the point at infinity. -/
@[simp]
theorem pointOne_ne_zero : pointOne K ≠ 0 := by
  simp [pointOne, Affine.Point.mk, Affine.Point.zero_def]

/-- `T₋₁` is not the point at infinity. -/
@[simp]
theorem pointNegOne_ne_zero : pointNegOne K ≠ 0 := by
  simp [pointNegOne, Affine.Point.mk, Affine.Point.zero_def]

/-- `T₀ ≠ T₁`. -/
@[simp]
theorem pointZero_ne_pointOne : pointZero K ≠ pointOne K := by
  simp [pointZero, pointOne, Affine.Point.mk]

/-- `T₀ ≠ T₋₁`. -/
@[simp]
theorem pointZero_ne_pointNegOne : pointZero K ≠ pointNegOne K := by
  simp [pointZero, pointNegOne, Affine.Point.mk]

/-- `T₁ ≠ T₋₁`, since `1 ≠ -1` away from characteristic two. -/
@[simp]
theorem pointOne_ne_pointNegOne : pointOne K ≠ pointNegOne K := by
  have h1 : (1 : K) ≠ -1 := fun h ↦ NeZero.ne (2 : K) (by linear_combination h)
  simp [pointOne, pointNegOne, Affine.Point.mk, h1]

/-- **The points of order dividing two on `y² = x³ - x`** are the point at infinity and the three
points `(0, 0)`, `(1, 0)` and `(-1, 0)` on the line `y = 0`. -/
@[simp]
theorem neg_eq_self_iff (T : (curve K).toAffine.Point) :
    -T = T ↔ T = 0 ∨ T = pointZero K ∨ T = pointOne K ∨ T = pointNegOne K := by
  cases T with
  | zero => exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ rfl⟩
  | some x y h =>
    simp only [Affine.Point.neg_some, Affine.Point.some.injEq, Affine.negY, pointZero, pointOne,
      pointNegOne, Affine.Point.mk, curve_a₁, curve_a₃, reduceCtorEq, false_or, true_and]
    constructor
    · intro hy
      -- `-y = y` forces `y = 0`, and then `x` is a root of `x³ - x = x (x - 1) (x + 1)`.
      have hy0 : y = 0 := by
        have : (2 : K) * y = 0 := by linear_combination -hy
        simpa [NeZero.ne (2 : K)] using this
      subst hy0
      have hx := (equation_iff x 0).mp h.1
      have hroots : x * ((x - 1) * (x + 1)) = 0 := by linear_combination -hx
      rcases mul_eq_zero.mp hroots with hx | hx
      · exact Or.inl ⟨hx, rfl⟩
      rcases mul_eq_zero.mp hx with hx | hx
      · exact Or.inr (Or.inl ⟨by linear_combination hx, rfl⟩)
      · exact Or.inr (Or.inr ⟨by linear_combination hx, rfl⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

end TauCeti.CurveX3SubX
