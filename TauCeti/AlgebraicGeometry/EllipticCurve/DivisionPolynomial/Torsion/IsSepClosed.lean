/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Integral
-- Proof-only: the `y`-coordinate of a solution with rational `x` is rational.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsSepClosed
-- Proof-only: torsion abscissae of invertible index have separable minimal polynomial.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.DivisionPolynomialSeparable
-- Proof-only: an even index with nonzero cast keeps `2` nonzero.
import TauCeti.Data.Int.CastNeZero
-- Proof-only: an integral element whose minimal polynomial splits lies in the base field.
import Mathlib.RingTheory.Adjoin.Field

/-!
# Torsion points over a separably closed field are already rational

An `n`-torsion point of `W` with coordinates in an extension of a separably closed `F` already has
them in `F`, provided `n` is invertible in `F`. Its abscissa is integral over `F` with separable
minimal polynomial, and the ordinate then solves a quadratic whose other root is its negative.

Invertibility of `n` is what the separability rests on, and it cannot be dropped. Over the
separable closure `K` of `𝔽₂(t)` the curve `y² + xy = x³ + t` has discriminant `t`, so it is
elliptic, and its nonzero `2`-torsion point is `(0, √t)`: the geometric `2`-torsion is
nontrivial while the `2`-torsion over `K` itself is not.

## Main results

* `WeierstrassCurve.mem_range_x_of_zsmul_eq_zero_of_isSepClosed`: the abscissa of an `n`-torsion
  point over an extension of a separably closed field, with `n` invertible, is already rational.
* `WeierstrassCurve.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed`: the whole torsion point
  is the base change of one over the separably closed field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace WeierstrassCurve

variable {F : Type*} [Field F] [IsSepClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
  {Ω : Type*} [Field Ω] [Algebra F Ω]

/-- **The abscissa of a torsion point is rational** over a separably closed field in which the
index is invertible: it is integral over the base field and its minimal polynomial is separable,
so a separably closed field already contains it. -/
theorem mem_range_x_of_zsmul_eq_zero_of_isSepClosed {n : ℤ} (hchar : (n : F) ≠ 0) {x y : Ω}
    (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    x ∈ Set.range (algebraMap F Ω) := by
  have hn : n ≠ 0 := by rintro rfl; exact hchar (by simp)
  refine (isIntegral_x_of_zsmul_eq_zero W hn hns htors).mem_range_algebraMap_of_minpoly_splits ?_
  simpa using IsSepClosed.splits_of_separable _
    (separable_minpoly_of_zsmul_eq_zero W hchar hns htors)

variable [DecidableEq F] [DecidableEq Ω]

omit [IsSepClosed F] [W.IsElliptic] [DecidableEq F] in
/-- A torsion point of invertible index satisfies the side condition that makes its ordinate
rational: in characteristic `2` it would otherwise be its own negative, hence killed by `2` as
well as by an odd index, hence zero. -/
private theorem two_ne_zero_or_add_ne_zero_of_zsmul_eq_zero {n : ℤ} (hchar : (n : F) ≠ 0)
    {x y : Ω} (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (h : n • Affine.Point.some x y hns = 0) {x₀ : F} (hx₀ : algebraMap F Ω x₀ = x) :
    (2 : F) ≠ 0 ∨ W.a₁ * x₀ + W.a₃ ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h2, hb⟩ := hcon
  have hzero : (2 : Ω) = 0 := by rw [← map_ofNat (algebraMap F Ω) 2, h2, map_zero]
  have hab : (W.baseChange Ω).a₁ * x + (W.baseChange Ω).a₃ = 0 := by
    rw [← hx₀]
    simp only [baseChange, map_a₁, map_a₃]
    rw [← map_mul, ← map_add, hb, map_zero]
  -- The point is its own negative, so it is killed by `2`.
  have hself : -Affine.Point.some x y hns = Affine.Point.some x y hns := by
    rw [Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq, Affine.negY, true_and]
    linear_combination -hab - y * hzero
  have htwo : (2 : ℤ) • Affine.Point.some x y hns = 0 := by
    rw [two_zsmul]
    calc Affine.Point.some x y hns + Affine.Point.some x y hns
        = Affine.Point.some x y hns + -Affine.Point.some x y hns := by rw [hself]
      _ = 0 := add_neg_cancel _
  -- An invertible index in characteristic `2` is odd, so the point itself vanishes.
  obtain ⟨k, hk⟩ : Odd n := Int.not_even_iff_odd.mp fun heven ↦
    Int.two_ne_zero_of_even_of_cast_ne_zero heven hchar (by exact_mod_cast h2)
  refine Affine.Point.some_ne_zero hns ?_
  rwa [hk, add_smul, one_smul, mul_comm (2 : ℤ) k, mul_smul, htwo, smul_zero, zero_add] at h

/-- **A torsion point over an extension of a separably closed field is already rational** when its
index is invertible there: both of its coordinates are separable over the base field. -/
theorem mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed {n : ℤ} (hchar : (n : F) ≠ 0)
    {P : (W.baseChange Ω).toAffine.Point} (h : n • P = 0) :
    P ∈ Set.range (Affine.Point.baseChange (W' := W) F Ω) := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact ⟨0, Affine.Point.map_zero _⟩
  · have hJac : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
      have h' := congrArg (Jacobian.Point.toAffineAddEquiv (W.baseChange Ω)).symm h
      rw [map_zsmul, map_zero] at h'
      simpa using h'
    obtain ⟨x₀, hx₀⟩ := W.mem_range_x_of_zsmul_eq_zero_of_isSepClosed hchar hns hJac
    obtain ⟨y₀, hy₀⟩ := W.mem_range_y_of_equation_of_mem_range_x_of_isSepClosed hns.left hx₀
      (W.two_ne_zero_or_add_ne_zero_of_zsmul_eq_zero hchar hns h hx₀)
    subst hx₀
    subst hy₀
    refine ⟨Affine.Point.some x₀ y₀ ((W.toAffine.baseChange_nonsingular
      (f := Algebra.ofId F Ω) (FaithfulSMul.algebraMap_injective F Ω) x₀ y₀).mp hns), ?_⟩
    rw [Affine.Point.map_some]
    simp only [Algebra.ofId_apply]

end WeierstrassCurve

end
