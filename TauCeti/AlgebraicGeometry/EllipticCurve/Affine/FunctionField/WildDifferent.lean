/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
public import
  TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Ramification
public import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
-- Separability of `F(W) / F(x)` for an elliptic curve, needed to state different exponents.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Separable
-- Proof-only: `y` generates `F(W)` over `F(x)`, with the Weierstrass polynomial as its minimal
-- polynomial.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
-- Proof-only: the coordinate ring of an elliptic curve is a Dedekind domain.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.CoordinateRingIntegral
-- Proof-only: the different exponent vanishes where the derivative of the equation is a unit.
import TauCeti.FieldTheory.FunctionField.Different.Derivative

/-!
# A wild place: `y² + y = x³` over `𝔽₂`

Let `W` be the Weierstrass curve `y² + y = x³` over `𝔽₂`, Mathlib's model `ofJ0` of `j = 0`,
an elliptic curve, and let `F(W) = 𝔽₂(x, y)` be its function field, a quadratic extension of
`𝔽₂(x)`. This file computes the different of `F(W) / 𝔽₂(x)` and finds it concentrated at the place
at infinity, with exponent `4`, twice the ramification index `2`: the place at infinity is wildly
ramified, and Dedekind's tame formula `d = e - 1` fails there (Stichtenoth, Theorem 3.5.1 and
Proposition 3.7.8).

The computation runs the Hurwitz genus formula backwards. Away from infinity the derivative
`2y + 1 = 1` of the defining equation is a unit, so every finite place is unramified with
different exponent `0`. The place at infinity is the unique place over the infinite place of
`𝔽₂(x)`, with ramification index `2`. Since `F(W)` has genus `1`, the Hurwitz genus formula
`2g - 2 = -2 [F(W) : 𝔽₂(x)] + deg Diff` gives `deg Diff = 4`, and the place at infinity is
rational, so its different exponent is `4`.

## Main results

* `TauCeti.ArtinSchreier.differentExponent_eq_zero_of_ne_infinity`: every finite place of
  `𝔽₂(x, y)` is unramified over `𝔽₂(x)`.
* `TauCeti.ArtinSchreier.differentExponent_infinity`: the different exponent at infinity is `4`.
* `TauCeti.ArtinSchreier.isWild_infinity` and
  `TauCeti.ArtinSchreier.ramificationIdx_infinity_ne_differentExponent_add_one`: the place at
  infinity is wild, and the tame formula `e = d + 1` fails there.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.1, Corollary 3.5.5 and Proposition 3.7.8.
-/

public section

open Polynomial WeierstrassCurve

open scoped IntermediateField RatFunc

namespace TauCeti.ArtinSchreier

open AlgebraicGeometry

/-- `3 = 1` is a unit in `𝔽₂`, so Mathlib's model `y² + y = x³` of `j = 0` is an elliptic curve. -/
instance : Fact (IsUnit (3 : ZMod 2)) :=
  ⟨by rw [show (3 : ZMod 2) = 1 from by decide]; exact isUnit_one⟩

local instance : IsDedekindDomain (ofJ0 (ZMod 2)).toAffine.CoordinateRing :=
  have := Affine.isIntegrallyClosed_coordinateRing (ofJ0 (ZMod 2)).toAffine
  (ofJ0 (ZMod 2)).toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

instance : CharP (ofJ0 (ZMod 2)).toAffine.FunctionField 2 :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (ofJ0 (ZMod 2)).toAffine.FunctionField).injective 2

/-- **Away from infinity, `y² + y = x³` is unramified**: at a place `Q` of `𝔽₂(x, y)` other
than the place at infinity, `x` is regular and the derivative `2y + 1 = 1` of the defining
equation is a unit, so the different exponent of `Q` over `𝔽₂(x)` is `0`. -/
theorem differentExponent_eq_zero_of_ne_infinity
    (Q : Place (ZMod 2) (ofJ0 (ZMod 2)).toAffine.FunctionField)
    (hQ : Q ≠ Place.infinity (ofJ0 (ZMod 2)).toAffine) :
    Place.differentExponent (ZMod 2) (RatFunc (ZMod 2)) Q = 0 := by
  -- `x` is regular at `Q`
  have hx : Q.valuation (algebraMap (ZMod 2)[X] (ofJ0 (ZMod 2)).toAffine.FunctionField X) ≤ 1 := by
    rcases Place.eq_infinity_or_existsUnique_eq_ofPrime Q with h | ⟨𝔭, h𝔭, -⟩
    · exact absurd h hQ
    · exact (Place.exists_eq_ofPrime_iff_valuation_X_le_one Q).mp ⟨𝔭, h𝔭⟩
  have hψ : minpoly (RatFunc (ZMod 2)) (Affine.genericY (ofJ0 (ZMod 2)).toAffine) =
      X ^ 2 + X - C ((RatFunc.X : RatFunc (ZMod 2)) ^ 3) := by
    rw [Affine.minpoly_genericY]
    simp [ofJ0, Affine.polynomial]
  -- `c = x ^ 3` is kept opaque so that `simp` computes the coefficients of `X ^ 2 + X - C c`
  set c : RatFunc (ZMod 2) := RatFunc.X ^ 3 with hc
  have hx' : algebraMap (RatFunc (ZMod 2)) (ofJ0 (ZMod 2)).toAffine.FunctionField c ∈
      Q.integers := by
    rw [hc, map_pow, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply]
    exact pow_mem (Q.mem_integers_iff.mpr hx) 3
  have h2 : (1 + 1 : (ofJ0 (ZMod 2)).toAffine.FunctionField) = 0 := by
    rw [one_add_one_eq_two]
    exact_mod_cast CharP.cast_eq_zero (ofJ0 (ZMod 2)).toAffine.FunctionField 2
  refine Place.differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one (ZMod 2)
    (RatFunc (ZMod 2)) (Affine.adjoin_genericY_eq_top (ofJ0 (ZMod 2)).toAffine (RatFunc (ZMod 2)))
    (minpoly.monic (Algebra.IsIntegral.isIntegral _)) ?_ (minpoly.aeval _ _) ?_
  · intro i
    rw [Place.mem_integers_restrict_iff, hψ]
    rcases i with _ | _ | _ | i
    · simpa using neg_mem hx'
    · simp
    · simp [coeff_X]
    · simp [coeff_X_pow, coeff_X]
  · rw [hψ]
    simp [h2]

/-- The different of `𝔽₂(x, y) / 𝔽₂(x)` is supported at the place at infinity, with multiplicity
its different exponent there. -/
theorem different_eq :
    Divisor.different (ZMod 2) (ofJ0 (ZMod 2)).toAffine.FunctionField
        (IsFunctionField.ratFunc (ZMod 2)) =
      (Place.differentExponent (ZMod 2) (RatFunc (ZMod 2))
          (Place.infinity (ofJ0 (ZMod 2)).toAffine) : ℤ) •
        WeilDivisor.ofPoint (Place.infinity (ofJ0 (ZMod 2)).toAffine) := by
  ext Q
  rw [Divisor.coeff_different, WeilDivisor.coeff_zsmul]
  rcases eq_or_ne Q (Place.infinity (ofJ0 (ZMod 2)).toAffine) with rfl | hQ
  · rw [WeilDivisor.coeff_ofPoint_self, mul_one]
  · rw [differentExponent_eq_zero_of_ne_infinity Q hQ, WeilDivisor.coeff_ofPoint_of_ne hQ,
      mul_zero, Nat.cast_zero]

/-- **The different exponent at infinity is `4`**: the Hurwitz genus formula over `𝔽₂(x)`, with
genus `1` and degree `2`, gives `deg Diff = 4`, and the different is concentrated at the rational
place at infinity. -/
theorem differentExponent_infinity :
    Place.differentExponent (ZMod 2) (RatFunc (ZMod 2)) (Place.infinity (ofJ0 (ZMod 2)).toAffine) =
      4 := by
  have h := hurwitz_genus_formula_ratFunc
    (Affine.isIntegrallyClosedIn_functionField (ofJ0 (ZMod 2)).toAffine)
  rw [Affine.genus_functionField, Affine.finrank_functionField, different_eq,
    Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infinity] at h
  omega

/-- **The place at infinity of `y² + y = x³` is wild**: its different exponent `4` is at least
its ramification index `2`. -/
theorem isWild_infinity :
    Place.IsWild (ZMod 2) (RatFunc (ZMod 2)) (Place.infinity (ofJ0 (ZMod 2)).toAffine) :=
  (Place.ramificationIdx_le_differentExponent_iff _ _ _).mp (by
    rw [Place.ramificationIdx_infinity, differentExponent_infinity]
    norm_num)

/-- **The tame formula fails at infinity**: `e = 2` while `d + 1 = 5`. This is the acceptance test
that no tameness assumption entered the Hurwitz genus formula. -/
theorem ramificationIdx_infinity_ne_differentExponent_add_one :
    Place.ramificationIdx (RatFunc (ZMod 2)) (Place.infinity (ofJ0 (ZMod 2)).toAffine) ≠
      Place.differentExponent (ZMod 2) (RatFunc (ZMod 2))
        (Place.infinity (ofJ0 (ZMod 2)).toAffine) + 1 := by
  rw [Place.ramificationIdx_infinity, differentExponent_infinity]
  norm_num

end TauCeti.ArtinSchreier
