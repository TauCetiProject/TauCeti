/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.TwoTorsion

/-!
# An order-four point on the Legendre twist by two

Let `l = 2 * t²` and `1 - l = 2 * v²`, with `t` and `v` nonzero, and choose `i` with `i² = -1`.
On the scaled Legendre curve `y² = x (x - 2) (x - 2 l)`, the point with coordinates
`(2 l + 4 i t v, 8 i t v (t + i v))` doubles to the third root point `(2 l, 0)`.
Its choice is preserved by field embeddings. The offset `x - 2 l = 4 i t v` is the representative
used by the third root reading in split two-descent.

## Reference

M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
sums*, Ann. of Math. 191 (2020), 355–392, proof of Lemma 6.6, p. 371. The ordinate here is
the corrected one: with `r = 2 t` and `s = 2 i v` it is `r s (r + s)`.
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] {t v i : K}

private theorem twistTwo_two_ne_zero (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) : (2 : K) ≠ 0 :=
  fun h ↦ by simp [h] at htv

private theorem twistTwo_parameter_ne_one (hv : v ≠ 0)
    (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) : 2 * t ^ 2 ≠ 1 := by
  intro h
  have hz : 2 * v ^ 2 = 0 := by linear_combination htv - h
  exact mul_ne_zero (twistTwo_two_ne_zero htv) (pow_ne_zero 2 hv) hz

/-- The conic relation for nonzero `t, v` gives an elliptic Legendre twist by two. -/
theorem isElliptic_scaledLegendre_twistTwo (ht : t ≠ 0) (hv : v ≠ 0)
    (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) : (scaledLegendre 2 (2 * t ^ 2)).IsElliptic := by
  have h₂ := twistTwo_two_ne_zero htv
  exact (isElliptic_scaledLegendre_iff_ne_zero _ _ h₂).mpr
    ⟨h₂, mul_ne_zero h₂ (pow_ne_zero 2 ht), twistTwo_parameter_ne_one hv htv⟩

private theorem twistTwoHalf_y_ne_zero (ht : t ≠ 0) (hv : v ≠ 0) (hi : i ^ 2 = -1)
    (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) : 8 * i * t * v * (t + i * v) ≠ 0 := by
  have hi₀ : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hsum : t + i * v ≠ 0 := by
    intro h
    have : (1 : K) = 0 := by linear_combination 2 * (t - i * v) * h + 2 * v ^ 2 * hi - htv
    exact one_ne_zero this
  have h8 : (8 : K) ≠ 0 := by
    simpa only [show (2 : K) ^ 3 = 8 by norm_num] using
      pow_ne_zero 3 (twistTwo_two_ne_zero htv)
  simp [h8, hi₀, ht, hv, hsum]

private theorem twistTwoHalf_sub_two (hi : i ^ 2 = -1)
    (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    4 * t ^ 2 + 4 * i * t * v - 2 = (2 * i * v) * (2 * t + 2 * i * v) := by
  linear_combination 2 * htv - 4 * v ^ 2 * hi

/-- The pair `(4 * t² + 4 * i * t * v, 8 * i * t * v * (t + i * v))` is nonsingular on the
Legendre twist by two with parameter `2 * t²`. -/
theorem nonsingular_scaledLegendreTwistTwoHalf (ht : t ≠ 0) (hv : v ≠ 0) (hi : i ^ 2 = -1)
    (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    (scaledLegendre 2 (2 * t ^ 2)).toAffine.Nonsingular
      (4 * t ^ 2 + 4 * i * t * v) (8 * i * t * v * (t + i * v)) := by
  rw [nonsingular_iff', equation_scaledLegendre_iff]
  refine ⟨?_, Or.inr ?_⟩
  · rw [twistTwoHalf_sub_two hi htv]
    ring
  · simpa only [a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, zero_mul, add_zero] using
      mul_ne_zero (twistTwo_two_ne_zero htv) (twistTwoHalf_y_ne_zero ht hv hi htv)

/-- The chosen half of the third root point on the Legendre twist by two with parameter
`2 * t²`, for `i² = -1` and nonzero `t, v` satisfying `2 * t² + 2 * v² = 1`. -/
def scaledLegendreTwistTwoHalf (ht : t ≠ 0) (hv : v ≠ 0) (hi : i ^ 2 = -1)
    (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) : (scaledLegendre 2 (2 * t ^ 2)).toAffine.Point :=
  .some _ _ (nonsingular_scaledLegendreTwistTwoHalf ht hv hi htv)

/-- The affine coordinates of the chosen half. -/
theorem scaledLegendreTwistTwoHalf_eq_some (ht : t ≠ 0) (hv : v ≠ 0) (hi : i ^ 2 = -1)
    (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    scaledLegendreTwistTwoHalf ht hv hi htv =
      .some (4 * t ^ 2 + 4 * i * t * v) (8 * i * t * v * (t + i * v))
        (nonsingular_scaledLegendreTwistTwoHalf ht hv hi htv) :=
  (rfl)

/-- The chosen half has nonzero ordinate. -/
@[simp] theorem yCoord_scaledLegendreTwistTwoHalf_ne_zero (ht : t ≠ 0) (hv : v ≠ 0)
    (hi : i ^ 2 = -1) (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    (scaledLegendreTwistTwoHalf ht hv hi htv).yCoord ≠ 0 := by
  rw [scaledLegendreTwistTwoHalf_eq_some, Point.yCoord_some]
  exact twistTwoHalf_y_ne_zero ht hv hi htv

/-- The offset from the third root, which supplies the third split descent representative. -/
@[simp] theorem xCoord_scaledLegendreTwistTwoHalf_sub (ht : t ≠ 0) (hv : v ≠ 0)
    (hi : i ^ 2 = -1) (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    (scaledLegendreTwistTwoHalf ht hv hi htv).xCoord - 2 * (2 * t ^ 2) = 4 * i * t * v := by
  rw [scaledLegendreTwistTwoHalf_eq_some, Point.xCoord_some]
  ring

/-- The chosen half doubles to the point `(2 l, 0)` at the third root, where `l = 2 * t²`. -/
@[simp] theorem two_nsmul_scaledLegendreTwistTwoHalf [DecidableEq K] (ht : t ≠ 0) (hv : v ≠ 0)
    (hi : i ^ 2 = -1) (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    2 • scaledLegendreTwistTwoHalf ht hv hi htv =
      scaledLegendreRootPoint (by exact twistTwo_two_ne_zero htv)
        (by exact mul_ne_zero (twistTwo_two_ne_zero htv) (pow_ne_zero 2 ht))
        (by exact twistTwo_parameter_ne_one hv htv) 2 := by
  let W := (scaledLegendre (2 : K) (2 * t ^ 2)).toAffine
  set x := 4 * t ^ 2 + 4 * i * t * v
  set y := 8 * i * t * v * (t + i * v)
  set r := 2 * t
  set s := 2 * i * v
  have h₁ : W.a₁ = 0 := a₁_of_isCharNeTwoNF _
  have h₃ : W.a₃ = 0 := a₃_of_isCharNeTwoNF _
  have h₂ : W.a₂ = -(2 * (1 + 2 * t ^ 2)) := scaledLegendre_a₂ _ _
  have h₄ : W.a₄ = 2 ^ 2 * (2 * t ^ 2) := scaledLegendre_a₄ _ _
  have hy : y ≠ 0 := twistTwoHalf_y_ne_zero ht hv hi htv
  have hneg : y ≠ W.negY x y := by
    rw [← sub_ne_zero]
    simpa only [negY, h₁, h₃, zero_mul, sub_zero, sub_neg_eq_add, ← two_mul] using
      mul_ne_zero (twistTwo_two_ne_zero htv) hy
  -- In the factorization at the half, the three root differences are r(r+s), s(r+s), and rs.
  have hx₀ : x = r * (r + s) := by dsimp [x, r, s]; ring
  have hx₁ : x - 2 = s * (r + s) := twistTwoHalf_sub_two hi htv
  have hx₂ : x - 2 * (2 * t ^ 2) = r * s := by dsimp [x, r, s]; ring
  have hy' : y = r * s * (r + s) := by dsimp [y, r, s]; ring
  have hslope : W.slope x x y y = r + s := by
    rw [slope_of_Y_ne rfl hneg, div_eq_iff (sub_ne_zero.mpr hneg)]
    simp only [negY, h₁, h₂, h₃, h₄, zero_mul, sub_zero]
    calc
      _ = (x - 2) * (x - 2 * (2 * t ^ 2)) + x * (x - 2 * (2 * t ^ 2)) + x * (x - 2) := by ring
      _ = _ := by rw [hx₂, hx₁, hx₀, hy']; ring
  have hX : W.addX x x (r + s) = 2 * (2 * t ^ 2) := by
    simp only [addX, h₁, h₂, zero_mul, add_zero]
    dsimp [x, r, s]
    linear_combination 4 * v ^ 2 * hi - 2 * htv
  have hY : W.addY x x y (r + s) = 0 := by
    simp only [addY, negY, negAddY, hX, h₁, h₃, zero_mul, sub_zero]
    rw [← neg_sub, hx₂, hy']
    ring
  rw [two_nsmul, scaledLegendreTwistTwoHalf_eq_some, Point.add_self_of_Y_ne hneg,
    scaledLegendreRootPoint_eq_some]
  simp only [hX, hY, hslope, Matrix.cons_val]

/-- The chosen half has exact additive order four. -/
@[simp] theorem addOrderOf_scaledLegendreTwistTwoHalf [DecidableEq K] (ht : t ≠ 0) (hv : v ≠ 0)
    (hi : i ^ 2 = -1) (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    addOrderOf (scaledLegendreTwistTwoHalf ht hv hi htv) = 4 := by
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · simp
  · simp only [pow_succ', mul_nsmul, two_nsmul_scaledLegendreTwistTwoHalf,
      two_nsmul_scaledLegendreRootPoint, smul_zero]

/-- Transport along a field embedding preserves the chosen half, with `t, v, i` mapped into
the target field. -/
theorem mapAlong_scaledLegendreTwistTwoHalf {L : Type*} [Field L] (f : K →+* L)
    (ht : t ≠ 0) (hv : v ≠ 0) (hi : i ^ 2 = -1) (htv : 2 * t ^ 2 + 2 * v ^ 2 = 1) :
    cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point)
      (by simp [map_ofNat] :
        (scaledLegendre 2 (2 * t ^ 2)).map f = scaledLegendre 2 (2 * (f t) ^ 2)))
      ((scaledLegendreTwistTwoHalf ht hv hi htv).mapAlong f f.injective) =
        scaledLegendreTwistTwoHalf
          (t := f t) (v := f v) (i := f i)
          ((map_ne_zero f).mpr ht) ((map_ne_zero f).mpr hv)
          (by simpa using congrArg f hi) (by simpa [map_ofNat] using congrArg f htv) := by
  simp [scaledLegendreTwistTwoHalf_eq_some, Point.cast_some, map_ofNat]

end TauCeti
