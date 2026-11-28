/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.TwoTorsion
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# A half of the zero root on the Legendre equation at minus one

If `i² = -1` over a field of characteristic different from two, the point `(i, 1 - i)` on
`y² = x³ - x` doubles to `(0, 0)` and has exact order four. The point retains its chosen
square root under field embeddings. In particular, this gives an order-four point over finite
fields of cardinality congruent to one modulo four, including five modulo eight.

## References

* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, proof of Lemma 6.5, for the point `(i, 1 - i)` and
  its double.
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] {i : K}

/-- The coordinates of the chosen half give a nonsingular point. -/
theorem nonsingular_legendreNegOneHalf (h2 : (2 : K) ≠ 0) (hi : i ^ 2 = -1) :
    (scaledLegendre (1 : K) (-1)).toAffine.Nonsingular i (1 - i) := by
  let : NeZero (2 : K) := ⟨h2⟩
  rw [scaledLegendre_one, legendre_neg_one, ← equation_iff_nonsingular,
    CurveX3SubX.equation_iff]
  linear_combination (1 - i) * hi

/-- The affine point `(i, 1 - i)` on the Legendre equation at parameter `-1`, for the chosen
square root `i` of `-1` in characteristic different from two. -/
def legendreNegOneHalf (h2 : (2 : K) ≠ 0) (hi : i ^ 2 = -1) :
    (scaledLegendre (1 : K) (-1)).toAffine.Point :=
  .some i (1 - i) (nonsingular_legendreNegOneHalf h2 hi)

/-- The coordinates of the chosen half are `i` and `1 - i`. -/
theorem legendreNegOneHalf_eq_some (h2 : (2 : K) ≠ 0) (hi : i ^ 2 = -1) :
    legendreNegOneHalf h2 hi = .some i (1 - i) (nonsingular_legendreNegOneHalf h2 hi) :=
  (rfl)

section Addition

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hi : i ^ 2 = -1)

/-- Twice the chosen half is the labelled root point `(0, 0)`. -/
@[simp]
theorem two_nsmul_legendreNegOneHalf :
    2 • legendreNegOneHalf h2 hi =
      scaledLegendreRootPoint one_ne_zero (neg_ne_zero.mpr one_ne_zero)
        (by
          intro h
          exact h2 (by linear_combination -h)) 0 := by
  have hy : 1 - i ≠ (scaledLegendre (1 : K) (-1)).toAffine.negY i (1 - i) := by
    intro h
    simp only [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, zero_mul, sub_zero] at h
    have hmul : 2 * (1 - i) = 0 := by linear_combination h
    have hi₁ : i = 1 := (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left h2)).symm
    rw [hi₁, one_pow] at hi
    exact h2 (by linear_combination hi)
  have hslope :
      (scaledLegendre (1 : K) (-1)).toAffine.slope i i (1 - i) (1 - i) = -(1 + i) := by
    rw [slope_of_Y_ne rfl hy, div_eq_iff (sub_ne_zero.mpr hy)]
    simp only [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, scaledLegendre_a₂,
      scaledLegendre_a₄]
    linear_combination hi
  rw [two_nsmul, legendreNegOneHalf_eq_some, Point.add_self_of_Y_ne hy,
    scaledLegendreRootPoint_eq_some, Point.some.injEq]
  simp only [Matrix.cons_val_zero, hslope, addY, negY, negAddY, addX, a₁_of_isCharNeTwoNF,
    a₃_of_isCharNeTwoNF, scaledLegendre_a₂, add_neg_cancel, mul_zero, neg_zero, zero_mul,
    sub_zero, add_zero]
  constructor
  · linear_combination hi
  · linear_combination i * hi

/-- The chosen half has exact additive order four. -/
@[simp]
theorem addOrderOf_legendreNegOneHalf : addOrderOf (legendreNegOneHalf h2 hi) = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · simp
  · rw [pow_succ, pow_one, mul_nsmul, two_nsmul_legendreNegOneHalf,
      two_nsmul_scaledLegendreRootPoint]

end Addition

/-- A field embedding sends the half specified by `i` to the half specified by its image. -/
@[simp]
theorem mapAlong_legendreNegOneHalf {L : Type*} [Field L]
    (h2 : (2 : K) ≠ 0) (hi : i ^ 2 = -1) (f : K →+* L) :
    cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point)
      ((map_scaledLegendre (1 : K) (-1) f).trans (by simp)))
      (Point.mapAlong f f.injective (legendreNegOneHalf h2 hi)) =
      legendreNegOneHalf (i := f i) (by simpa only [map_ofNat] using (map_ne_zero f).mpr h2)
        (by simpa only [map_pow, map_neg, map_one] using congrArg f hi) := by
  have hmap : (scaledLegendre (1 : K) (-1)).map f = scaledLegendre (1 : L) (-1) := by simp
  simp only [legendreNegOneHalf_eq_some, Point.mapAlong_some, Point.cast_some hmap,
    map_sub, map_one]

/-- Over a finite field of size one modulo four, the Legendre equation at parameter `-1` has
a point of exact order four. -/
theorem exists_addOrderOf_eq_four_scaledLegendre_neg_one [Fintype K] [DecidableEq K]
    (hq : Fintype.card K % 4 = 1) :
    ∃ P : (scaledLegendre (1 : K) (-1)).toAffine.Point, addOrderOf P = 4 := by
  have hchar : ringChar K ≠ 2 := fun h ↦ by
    have := FiniteField.even_card_of_char_two h
    omega
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨i, hi⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
  have hi' : i ^ 2 = -1 := by simpa [pow_two] using hi.symm
  exact ⟨legendreNegOneHalf h2 hi', addOrderOf_legendreNegOneHalf h2 hi'⟩

end TauCeti
