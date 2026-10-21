/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Different
public import TauCeti.AlgebraicGeometry.EllipticCurve.CurveX3SubX
-- Proof-only: the genus of `K(x)`.
import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc

/-!
# A tame example: `y² = x³ - x`

Let `W` be the Weierstrass curve `y² = x³ - x` (`TauCeti.CurveX3SubX.curve`) over a field `K` of
characteristic other than two, for instance `ℚ`, and let `K(W) = K(x, y)` be its function field, a
quadratic extension of `K(x)`. Its discriminant is `64`, so `W` is an elliptic curve. This file
computes the ramification of `K(W) / K(x)` and checks it against the Hurwitz genus formula. Every
ramified place has ramification index `2`, invertible in `K`, so the ramification is tame, in
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

## Main results

* `TauCeti.CurveX3SubX.different_eq`: `Diff(K(W) / K(x)) = O + T₀ + T₁ + T₋₁`.
* `TauCeti.CurveX3SubX.one_lt_ramificationIdx_iff`: the ramified places are the places of the
  four points of order dividing two.
* `TauCeti.CurveX3SubX.ramificationIdx_pointZero` and its siblings: those places have
  ramification index `2`.
* `TauCeti.CurveX3SubX.hurwitz_genus_formula`: the numerical Hurwitz genus identity
  `2 · 1 - 2 = 2 · (0 - 2) + 4`, with `e - 1` summed over the four ramified places.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.4.14, Theorem 3.5.1, Corollary 3.5.6 and Proposition 6.1.3.
-/

public section

open WeierstrassCurve

open scoped RatFunc

namespace TauCeti.CurveX3SubX

open AlgebraicGeometry

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The four points of order dividing two are pairwise distinct. -/
private theorem card_twoTorsion [DecidableEq K] :
    ({0, pointZero K, pointOne K, pointNegOne K} : Finset (curve K).toAffine.Point).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_pair pointOne_ne_pointNegOne]
  · simp
  · simp [eq_comm (a := (0 : (curve K).toAffine.Point))]

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
  rw [Affine.different_eq_sum_of_card_eq_four (NeZero.ne 2) neg_eq_self_of_mem card_twoTorsion,
    Finset.sum_insert (by simp [eq_comm (a := (0 : (curve K).toAffine.Point))]),
    Finset.sum_insert (by simp), Finset.sum_pair pointOne_ne_pointNegOne, Affine.Point.zero_def,
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

/-- **The Hurwitz genus formula for `y² = x³ - x`** over `K(x)`, as a numerical identity: with
`e - 1` summed over the four ramified places,

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
