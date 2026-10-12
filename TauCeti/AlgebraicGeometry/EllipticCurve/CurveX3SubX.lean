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

* `TauCeti.CurveX3SubX.Δ_curve`: the discriminant of `y² = x³ - x` is `64`.
* `TauCeti.CurveX3SubX.neg_eq_self_iff`: the points of order dividing two are `O`, `T₀`, `T₁`
  and `T₋₁`.
-/

public section

open WeierstrassCurve

namespace TauCeti.CurveX3SubX

/-- The Weierstrass curve `y² = x³ - x`. -/
abbrev curve (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

/-- The discriminant of `y² = x³ - x` is `64`. -/
@[simp]
theorem Δ_curve (R : Type*) [CommRing R] : (curve R).Δ = 64 := by
  simp only [Δ, b₂, b₄, b₆, b₈]
  ring

variable (K : Type*) [Field K]

/-- Away from characteristic two, `y² = x³ - x` is an elliptic curve: its discriminant
`64 = 2⁶` is a unit. -/
instance [NeZero (2 : K)] : (curve K).IsElliptic := by
  rw [isElliptic_iff, Δ_curve]
  convert (Ne.isUnit (NeZero.ne (2 : K))).pow 6 using 1
  norm_num

variable {K}

/-- The affine points of `y² = x³ - x` are the solutions of `y² = x³ - x`. -/
@[simp]
theorem equation_iff (x y : K) : (curve K).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [Affine.equation_iff]
  constructor <;> intro h <;> linear_combination h

variable [NeZero (2 : K)]
variable (K)

/-- The point `T₀ = (0, 0)` of `y² = x³ - x`. -/
def pointZero : (curve K).toAffine.Point :=
  .mk ((equation_iff 0 0).mpr (by ring))

/-- `T₀` is the affine point `(0, 0)`. -/
theorem pointZero_def :
    pointZero K = .mk ((equation_iff 0 0).mpr (by ring)) :=
  (rfl)

/-- The point `T₁ = (1, 0)` of `y² = x³ - x`. -/
def pointOne : (curve K).toAffine.Point :=
  .mk ((equation_iff 1 0).mpr (by ring))

/-- `T₁` is the affine point `(1, 0)`. -/
theorem pointOne_def :
    pointOne K = .mk ((equation_iff 1 0).mpr (by ring)) :=
  (rfl)

/-- The point `T₋₁ = (-1, 0)` of `y² = x³ - x`. -/
def pointNegOne : (curve K).toAffine.Point :=
  .mk ((equation_iff (-1) 0).mpr (by ring))

/-- `T₋₁` is the affine point `(-1, 0)`. -/
theorem pointNegOne_def :
    pointNegOne K = .mk ((equation_iff (-1) 0).mpr (by ring)) :=
  (rfl)

variable {K}

/-- **The points of order dividing two on `y² = x³ - x`** are the point at infinity and the three
points `(0, 0)`, `(1, 0)` and `(-1, 0)` on the line `y = 0`. -/
@[simp]
theorem neg_eq_self_iff (T : (curve K).toAffine.Point) :
    -T = T ↔ T = 0 ∨ T = pointZero K ∨ T = pointOne K ∨ T = pointNegOne K := by
  cases T with
  | zero => exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ rfl⟩
  | some x y h =>
    simp only [Affine.Point.neg_some, Affine.Point.some.injEq, Affine.negY, pointZero_def,
      pointOne_def, pointNegOne_def, Affine.Point.mk, reduceCtorEq, false_or, true_and]
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
