/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Different
-- Proof-only: the Hurwitz genus formula over a rational subfield and the genus of `K(x)`.
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz

/-!
# A tame example: `y² = x³ - x`

Let `W` be the Weierstrass curve `y² = x³ - x` over a field `K` of characteristic other than two,
for instance `ℚ`, and let `K(W) = K(x, y)` be its function field, a quadratic extension of `K(x)`.
Its discriminant is `64`, so `W` is an elliptic curve. This file computes the ramification of
`K(W) / K(x)` and checks it against the Hurwitz genus formula. Every place is tame here, in
contrast to `y² + y = x³` over `𝔽₂`, whose place at infinity is wild
(`TauCeti.ArtinSchreier.isWild_infinity`).

The points of order dividing two are the point at infinity `O` and the three points
`T₀ = (0, 0)`, `T₁ = (1, 0)` and `T₋₁ = (-1, 0)` on the line `y = 0`, all rational over `K`.
Their four places are the places of `K(W)` ramified over `K(x)`: each has ramification index `2`
and different exponent `1`, every other place is unramified, and

`Diff(K(W) / K(x)) = O + T₀ + T₁ + T₋₁`.

The Hurwitz genus formula then reads `2 · 1 - 2 = 2 · (0 - 2) + 4`: the genus `1` of `K(W)` on the
left is computed from the Riemann–Roch spaces `L(n · O)`, while the right side uses only the
degree `[K(W) : K(x)] = 2`, the genus `0` of `K(x)` and the four ramification indices.

## Main definitions

* `TauCeti.CurveX3SubX.curve`: the Weierstrass curve `y² = x³ - x`.
* `TauCeti.CurveX3SubX.pointZero`, `TauCeti.CurveX3SubX.pointOne`,
  `TauCeti.CurveX3SubX.pointNegOne`: its affine points of order two.

## Main results

* `TauCeti.CurveX3SubX.neg_eq_self_iff`: the points of order dividing two are `O`, `T₀`, `T₁`
  and `T₋₁`.
* `TauCeti.CurveX3SubX.different_eq`: `Diff(K(W) / K(x)) = O + T₀ + T₁ + T₋₁`.
* `TauCeti.CurveX3SubX.one_lt_ramificationIdx_iff`: the ramified places are the places of the
  four points of order dividing two.
* `TauCeti.CurveX3SubX.ramificationIdx_pointZero` and its siblings: those places have
  ramification index `2`.
* `TauCeti.CurveX3SubX.hurwitz_genus_formula`: the Hurwitz genus formula in its tame form,
  `2 · 1 - 2 = 2 · (0 - 2) + 4`, the different contributing `e - 1` at each ramified place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.4.14, Theorem 3.5.1, Corollary 3.5.6 and Proposition 6.1.3.
-/

public section

open WeierstrassCurve

open scoped RatFunc

namespace TauCeti.CurveX3SubX

open AlgebraicGeometry

variable (K : Type*) [Field K]

/-- The Weierstrass curve `y² = x³ - x`. -/
abbrev curve : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

/-- The discriminant of `y² = x³ - x` is `64`. -/
@[simp]
theorem Δ_curve : (curve K).Δ = 64 := by
  simp only [Δ, b₂, b₄, b₆, b₈]
  ring

/-- Away from characteristic two, `y² = x³ - x` is an elliptic curve: its discriminant
`64 = 2⁶` is a unit. -/
instance [NeZero (2 : K)] : (curve K).IsElliptic := by
  rw [isElliptic_iff, Δ_curve, show (64 : K) = 2 ^ 6 by norm_num]
  exact (Ne.isUnit (NeZero.ne 2)).pow 6

variable {K}

/-- The affine points of `y² = x³ - x` are the solutions of `y² = x³ - x`. -/
theorem equation_iff (x y : K) : (curve K).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [Affine.equation_iff]
  constructor <;> intro h <;> linear_combination h

variable [NeZero (2 : K)]

/-- A root `a` of `x³ - x` gives the nonsingular point `(a, 0)` of `y² = x³ - x`. -/
theorem nonsingular_of_pow_three_eq {a : K} (ha : a ^ 3 = a) :
    (curve K).toAffine.Nonsingular a 0 :=
  Affine.equation_iff_nonsingular.mp ((equation_iff a 0).mpr (by rw [ha]; ring))

variable (K)

/-- The point `T₀ = (0, 0)` of `y² = x³ - x`. -/
def pointZero : (curve K).toAffine.Point :=
  .some 0 0 (nonsingular_of_pow_three_eq (by ring))

/-- The point `T₁ = (1, 0)` of `y² = x³ - x`. -/
def pointOne : (curve K).toAffine.Point :=
  .some 1 0 (nonsingular_of_pow_three_eq (by ring))

/-- The point `T₋₁ = (-1, 0)` of `y² = x³ - x`. -/
def pointNegOne : (curve K).toAffine.Point :=
  .some (-1) 0 (nonsingular_of_pow_three_eq (by ring))

variable {K}

/-- **The points of order dividing two on `y² = x³ - x`** are the point at infinity and the three
points `(0, 0)`, `(1, 0)` and `(-1, 0)` on the line `y = 0`. -/
theorem neg_eq_self_iff (T : (curve K).toAffine.Point) :
    -T = T ↔ T = 0 ∨ T = pointZero K ∨ T = pointOne K ∨ T = pointNegOne K := by
  cases T with
  | zero => exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ rfl⟩
  | some x y h =>
    simp only [Affine.Point.neg_some, Affine.Point.some.injEq, Affine.negY, pointZero, pointOne,
      pointNegOne, reduceCtorEq, false_or, true_and]
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

/-- The three affine points of order two are pairwise distinct. -/
private theorem pointZero_ne_pointOne_and :
    pointZero K ≠ pointOne K ∧ pointZero K ≠ pointNegOne K ∧ pointOne K ≠ pointNegOne K := by
  have h1 : (1 : K) ≠ -1 := fun h ↦ NeZero.ne (2 : K) (by linear_combination h)
  simp [pointZero, pointOne, pointNegOne, h1]

/-- The four points of order dividing two are pairwise distinct. -/
private theorem card_twoTorsion [DecidableEq K] :
    ({0, pointZero K, pointOne K, pointNegOne K} : Finset (curve K).toAffine.Point).card = 4 := by
  obtain ⟨h01, h0m, h1m⟩ := pointZero_ne_pointOne_and (K := K)
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h1m]
  · simp [h01, h0m]
  · simp [pointZero, pointOne, pointNegOne]

/-- Each listed point has order dividing two. -/
private theorem neg_eq_self_of_mem [DecidableEq K] :
    ∀ T ∈ ({0, pointZero K, pointOne K, pointNegOne K} : Finset (curve K).toAffine.Point),
      -T = T := by
  intro T hT
  rw [neg_eq_self_iff]
  simpa using hT

/-- **The different of `y² = x³ - x` over `K(x)`** is the sum of the places of the four points
of order dividing two: `Diff(K(W) / K(x)) = O + T₀ + T₁ + T₋₁`. -/
theorem different_eq :
    Divisor.different K (curve K).toAffine.FunctionField (IsFunctionField.ratFunc K) =
      WeilDivisor.ofPoint (Place.infinity (curve K).toAffine) +
        WeilDivisor.ofPoint ((curve K).toAffine.pointEquivDegreeOnePlace (pointZero K)).1 +
        WeilDivisor.ofPoint ((curve K).toAffine.pointEquivDegreeOnePlace (pointOne K)).1 +
        WeilDivisor.ofPoint ((curve K).toAffine.pointEquivDegreeOnePlace (pointNegOne K)).1 := by
  classical
  obtain ⟨h01, h0m, h1m⟩ := pointZero_ne_pointOne_and (K := K)
  rw [Affine.different_eq_sum_of_card_eq_four (NeZero.ne 2) neg_eq_self_of_mem card_twoTorsion,
    Finset.sum_insert (by simp [pointZero, pointOne, pointNegOne]),
    Finset.sum_insert (by simp [h01, h0m]), Finset.sum_pair h1m, Affine.Point.zero_def,
    Affine.coe_pointEquivDegreeOnePlace_zero, add_assoc, add_assoc]

/-- **The ramified places of `y² = x³ - x` over `K(x)`** are the places of the four points of
order dividing two: the place at infinity and the places of `(0, 0)`, `(1, 0)` and `(-1, 0)`. -/
theorem one_lt_ramificationIdx_iff (P : Place K (curve K).toAffine.FunctionField) :
    1 < Place.ramificationIdx (RatFunc K) P ↔
      P = Place.infinity (curve K).toAffine ∨
        P = ((curve K).toAffine.pointEquivDegreeOnePlace (pointZero K)).1 ∨
        P = ((curve K).toAffine.pointEquivDegreeOnePlace (pointOne K)).1 ∨
        P = ((curve K).toAffine.pointEquivDegreeOnePlace (pointNegOne K)).1 := by
  classical
  rw [Affine.one_lt_ramificationIdx_iff_of_card_eq_four (NeZero.ne 2) neg_eq_self_of_mem
    card_twoTorsion]
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
    Affine.Point.zero_def, Affine.coe_pointEquivDegreeOnePlace_zero]
  tauto

/-- The place of a point of order dividing two has ramification index `2` over `K(x)`. -/
private theorem ramificationIdx_place_of_mem [DecidableEq K] {T : (curve K).toAffine.Point}
    (hT : T ∈ ({0, pointZero K, pointOne K, pointNegOne K} : Finset (curve K).toAffine.Point)) :
    Place.ramificationIdx (RatFunc K) ((curve K).toAffine.pointEquivDegreeOnePlace T).1 = 2 :=
  Affine.ramificationIdx_pointEquivDegreeOnePlace_of_card_eq_four (NeZero.ne 2) neg_eq_self_of_mem
    card_twoTorsion hT

/-- The place of `(0, 0)` has ramification index `2` over `K(x)`. -/
@[simp]
theorem ramificationIdx_pointZero :
    Place.ramificationIdx (RatFunc K)
      ((curve K).toAffine.pointEquivDegreeOnePlace (pointZero K)).1 = 2 := by
  classical
  exact ramificationIdx_place_of_mem (by simp)

/-- The place of `(1, 0)` has ramification index `2` over `K(x)`. -/
@[simp]
theorem ramificationIdx_pointOne :
    Place.ramificationIdx (RatFunc K)
      ((curve K).toAffine.pointEquivDegreeOnePlace (pointOne K)).1 = 2 := by
  classical
  exact ramificationIdx_place_of_mem (by simp)

/-- The place of `(-1, 0)` has ramification index `2` over `K(x)`. -/
@[simp]
theorem ramificationIdx_pointNegOne :
    Place.ramificationIdx (RatFunc K)
      ((curve K).toAffine.pointEquivDegreeOnePlace (pointNegOne K)).1 = 2 := by
  classical
  exact ramificationIdx_place_of_mem (by simp)

/-- **The Hurwitz genus formula for `y² = x³ - x`** over `K(x)`, in its tame form: every place
is tame, so the different contributes `e - 1` at each of the four ramified places, and

`2 g - 2 = [K(W) : K(x)] (2 g(K(x)) - 2) + ∑ (e - 1)`,

which reads `2 · 1 - 2 = 2 · (0 - 2) + 4`. The genus `g = 1` on the left is computed from the
Riemann–Roch spaces `L(n · O)` (`WeierstrassCurve.Affine.genus_functionField`), independently of
the ramification data on the right. -/
theorem hurwitz_genus_formula :
    2 * (genus K (curve K).toAffine.FunctionField : ℤ) - 2 =
      Module.finrank (RatFunc K) (curve K).toAffine.FunctionField *
          (2 * (genus K (RatFunc K) : ℤ) - 2) +
        ((Place.ramificationIdx (RatFunc K) (Place.infinity (curve K).toAffine) - 1 : ℤ) +
          (Place.ramificationIdx (RatFunc K)
            ((curve K).toAffine.pointEquivDegreeOnePlace (pointZero K)).1 - 1) +
          (Place.ramificationIdx (RatFunc K)
            ((curve K).toAffine.pointEquivDegreeOnePlace (pointOne K)).1 - 1) +
          (Place.ramificationIdx (RatFunc K)
            ((curve K).toAffine.pointEquivDegreeOnePlace (pointNegOne K)).1 - 1)) := by
  rw [Affine.genus_functionField, Affine.finrank_functionField, genus_ratFunc,
    Place.ramificationIdx_infinity, ramificationIdx_pointZero, ramificationIdx_pointOne,
    ramificationIdx_pointNegOne]
  norm_num

end TauCeti.CurveX3SubX
