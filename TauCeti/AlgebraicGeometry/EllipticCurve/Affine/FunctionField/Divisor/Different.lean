/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Ramification
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace

/-!
# The different of the function field of an elliptic curve over `F(x)`

Let `W` be an elliptic Weierstrass curve over a field `F`, with function field `F(W)`, coordinate
functions `x` and `y`, and place at infinity `O`. The function field is a separable quadratic
extension of the rational function field `F(x)`, and this file computes its different exactly:

`Diff(F(W) / F(x)) = div (2y + a₁x + a₃) + 4 O`,

in every characteristic. At a place `P ≠ O` the different exponent is therefore the order of
vanishing of `2y + a₁x + a₃`, the partial derivative of the Weierstrass equation in `y`, and at
`O` it is `4 + ord_O (2y + a₁x + a₃)`.

The formula is the divisor identity behind the invariant differential. The divisor of the Weil
differential `dx` is `-2 (x)_∞ + Diff(F(W) / F(x))`, the pole divisor of `x` is `2 O`, and the
invariant differential `dx / (2y + a₁x + a₃)` has divisor zero, so `(dx) = div (2y + a₁x + a₃)`.

Away from characteristic two, `2y + a₁x + a₃` has a pole of order three at `O` and no other pole,
so `d_O = 1` and `Diff(F(W) / F(x))` is the divisor of zeros of `2y + a₁x + a₃` plus `O`. Since
`-(x, y) = (x, -y - a₁x - a₃)`, the function `2y + a₁x + a₃` vanishes at the place of every
rational point of order two. Its zeros have degree `3`, so when all four points of order dividing
two are rational, as for `y² = x³ - x` over `ℚ`, the different is the sum of their four places:

`Diff(F(W) / F(x)) = O + T₁ + T₂ + T₃`.

In every characteristic the different has degree `4`, as the Hurwitz genus formula
`2 · 1 - 2 = 2 · (0 - 2) + deg Diff` requires.

## Main results

All in the namespace `WeierstrassCurve.Affine`:

* `poles_genericX`: the pole divisor of `x` is `2 O`.
* `weilDifferentialDivisor_weilDifferentialOfSeparating_genericX`: the Weil differential `dx` has
  divisor `div (2y + a₁x + a₃)`.
* `different_eq_principal_invariantDifferentialDenom_add`: **the different of `F(W) / F(x)` is
  `div (2y + a₁x + a₃) + 4 O`.**
* `differentExponent_eq_ord_invariantDifferentialDenom` and
  `differentExponent_infinity_eq_four_add_ord`: the different exponents, place by place.
* `degree_different`: the different has degree `4`.
* `ord_infinity_invariantDifferentialDenom`, `poles_invariantDifferentialDenom` and
  `degree_zeros_invariantDifferentialDenom`: away from characteristic two, `2y + a₁x + a₃` has a
  triple pole at `O`, no other pole, and zeros of degree `3`.
* `differentExponent_infinity_of_two_ne_zero` and `different_eq_zeros_add_of_two_ne_zero`: away
  from characteristic two, `d_O = 1` and the different is the divisor of zeros of
  `2y + a₁x + a₃` plus `O`.
* `different_eq_sum_of_card_eq_four`: away from characteristic two, if four rational points of
  `W` have order dividing two, the different is the sum of their places.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Remark 4.3.7 and Proposition 6.1.3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Proposition III.1.5.
-/

public section

open Polynomial TauCeti AlgebraicGeometry

open scoped IntermediateField RatFunc

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The coordinate `x` is the image of the rational function `X`. -/
private theorem genericX_eq_algebraMap_ratFunc_X :
    genericX W = algebraMap (RatFunc F) W.FunctionField RatFunc.X := by
  rw [genericX_eq_algebraMap, ← toAlgHom_ratFuncX, IsScalarTower.toAlgHom_apply]

/-- **The pole divisor of `x` is `2 O`**: the coordinate `x` is regular at every affine place and
has a double pole at the place at infinity. -/
@[simp]
theorem poles_genericX :
    Divisor.poles W.isFunctionField (Units.mk0 (genericX W) (transcendental_genericX W).ne_zero) =
      (2 : ℤ) • WeilDivisor.ofPoint (Place.infinity W) := by
  ext P
  rw [Divisor.coeff_poles, WeilDivisor.coeff_zsmul, Units.val_mk0]
  rcases eq_or_ne P (Place.infinity W) with rfl | hP
  · rw [WeilDivisor.coeff_ofPoint_self, genericX_eq_algebraMap_ratFunc_X,
      Place.ord_infinity_algebraMap, Place.ord_infty, RatFunc.intDegree_X]
    norm_num
  · have h := Place.valuation_algebraMap_le_one_of_ne_infinity hP (CoordinateRing.mk W (C X))
    rw [← genericX_def, ← P.mem_integers_iff, P.mem_integers_iff_ord_nonneg] at h
    rw [WeilDivisor.coeff_ofPoint_of_ne hP]
    omega

variable {W} in
/-- `2y + a₁x + a₃` is regular at every affine place. -/
private theorem ord_invariantDifferentialDenom_nonneg {P : Place F W.FunctionField}
    (hP : P ≠ Place.infinity W) : 0 ≤ P.ord (invariantDifferentialDenom W) := by
  have hx := Place.valuation_algebraMap_le_one_of_ne_infinity hP (CoordinateRing.mk W (C X))
  have hy := Place.valuation_algebraMap_le_one_of_ne_infinity hP (CoordinateRing.mk W X)
  rw [← genericX_def, ← P.mem_integers_iff] at hx
  rw [← genericY_def, ← P.mem_integers_iff] at hy
  rw [← P.mem_integers_iff_ord_nonneg, invariantDifferentialDenom_def]
  have hc (c : F) := P.algebraMap_mem_integers c
  refine add_mem (add_mem (mul_mem ?_ hy) (mul_mem (hc _) hx)) (hc _)
  simp

variable [W.IsElliptic]

/-- **The divisor of `dx` is `div (2y + a₁x + a₃)`**: the Weil differential `dx` attached to the
separating element `x` is `2y + a₁x + a₃` times the invariant differential, which has divisor
zero. -/
theorem weilDifferentialDivisor_weilDifferentialOfSeparating_genericX :
    weilDifferentialDivisor W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (weilDifferentialOfSeparating W.isFunctionField (transcendental_genericX W)).2
        (by simpa using
          weilDifferentialOfSeparating_ne_zero W.isFunctionField (transcendental_genericX W)) =
      Divisor.principal W.isFunctionField
        (Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W)) := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  let hF := W.isFunctionField
  let hex := isIntegrallyClosedIn_functionField W
  let hx := transcendental_genericX W
  set u := Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W)
  -- The invariant differential is `u⁻¹ · dx`, whose divisor is `div u⁻¹ + (dx)`.
  have hD := weilDifferentialDivisor_repartitionDualMul hF hex
    (weilDifferentialOfSeparating hF hx).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) u⁻¹
  have hω : ((kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx
      (invariantDifferential W) : ↥(weilDifferentialSpace F W.FunctionField)) :
        Module.Dual F ↥(repartitionSpace F W.FunctionField)) =
      repartitionDualMul hF ((u⁻¹ : (W.FunctionField)ˣ) : W.FunctionField)
        (weilDifferentialOfSeparating hF hx) := by
    rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential,
      coe_weilDifferentialSpaceModule_smul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have h0 := weilDifferentialDivisor_invariantDifferential W
  rw [(weilDifferentialDivisor_congr hF hex hω _ _ _ _).trans hD, Divisor.principal_inv] at h0
  exact (neg_add_eq_zero.mp h0).symm

/-- **The different of the function field of an elliptic curve over `F(x)`**: in every
characteristic, `Diff(F(W) / F(x)) = div (2y + a₁x + a₃) + 4 O`. -/
theorem different_eq_principal_invariantDifferentialDenom_add :
    Divisor.different F W.FunctionField (IsFunctionField.ratFunc F) =
      Divisor.principal W.isFunctionField
          (Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W)) +
        (4 : ℤ) • WeilDivisor.ofPoint (Place.infinity W) := by
  -- `(dx) = -2 (x)_∞ + Diff`, computed for the `F(x)`-algebra structure induced by `x`.
  have key := weilDifferentialDivisor_weilDifferentialOfSeparating W.isFunctionField
    (isIntegrallyClosedIn_functionField W) (transcendental_genericX W)
  rw [weilDifferentialDivisor_weilDifferentialOfSeparating_genericX, poles_genericX,
    smul_smul] at key
  convert (neg_add_eq_iff_eq_add.mpr key).symm using 1
  · -- That structure is the one `F(W)` carries as a `F[X]`-algebra.
    congr! 1
    exact (ratFuncAlgebraOfTranscendental_eq_liftAlgebra (transcendental_genericX W)
      (genericX_eq_algebraMap W).symm).symm
  · rw [← neg_smul, add_comm]
    norm_num

/-- **The different exponents away from infinity**: at a place `P ≠ O`, the different exponent
of `F(W) / F(x)` is the order of `2y + a₁x + a₃` at `P`. -/
theorem differentExponent_eq_ord_invariantDifferentialDenom {P : Place F W.FunctionField}
    (hP : P ≠ Place.infinity W) :
    (Place.differentExponent F (RatFunc F) P : ℤ) = P.ord (invariantDifferentialDenom W) := by
  have h := congrArg (WeilDivisor.coeff · P)
    (different_eq_principal_invariantDifferentialDenom_add W)
  simp only [Divisor.coeff_different, WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul,
    Divisor.coeff_principal, Units.val_mk0, WeilDivisor.coeff_ofPoint_of_ne hP] at h
  omega

/-- **The different exponent at infinity** is `4 + ord_O (2y + a₁x + a₃)`. -/
theorem differentExponent_infinity_eq_four_add_ord :
    (Place.differentExponent F (RatFunc F) (Place.infinity W) : ℤ) =
      4 + (Place.infinity W).ord (invariantDifferentialDenom W) := by
  have h := congrArg (WeilDivisor.coeff · (Place.infinity W))
    (different_eq_principal_invariantDifferentialDenom_add W)
  simp only [Divisor.coeff_different, WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul,
    Divisor.coeff_principal, Units.val_mk0, WeilDivisor.coeff_ofPoint_self] at h
  omega

/-- **The different of `F(W) / F(x)` has degree `4`**, in every characteristic: principal
divisors have degree zero and the place at infinity is rational. -/
@[simp]
theorem degree_different :
    Divisor.degree (Divisor.different F W.FunctionField (IsFunctionField.ratFunc F)) = 4 := by
  rw [different_eq_principal_invariantDifferentialDenom_add, Divisor.degree_add,
    Divisor.degree_principal, Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infinity]
  norm_num

/-! ### Away from characteristic two -/

section TwoNeZero

variable {W}

/-- **`2y + a₁x + a₃` has a triple pole at infinity** away from characteristic two: `2y` has a
pole of order three there and `a₁x + a₃` one of order at most two. -/
@[simp]
theorem ord_infinity_invariantDifferentialDenom (h2 : (2 : F) ≠ 0) :
    (Place.infinity W).ord (invariantDifferentialDenom W) = -3 := by
  rw [Place.ord_eq_iff_valuation_eq_exp_neg _ (invariantDifferentialDenom_ne_zero W), neg_neg,
    Place.valuation_infinity, invariantDifferentialDenom_def]
  have h2' : W.infinityPlace (2 : W.FunctionField) = 1 := by
    rw [← map_ofNat (algebraMap F W.FunctionField) 2]
    exact Valuation.IsTrivialOn.eq_one _ h2
  have hy : W.infinityPlace (2 * genericY W) = WithZero.exp 3 := by
    rw [map_mul, h2', one_mul, genericY_def, infinityPlace.mk_Y]
  have hc (c : F) : W.infinityPlace (algebraMap F W.FunctionField c) ≤ 1 := by
    rw [← Place.valuation_infinity, ← Place.mem_integers_iff]
    exact (Place.infinity W).algebraMap_mem_integers c
  have hx : W.infinityPlace (genericX W) = WithZero.exp 2 := by
    rw [genericX_eq_algebraMap_ratFunc_X, infinityPlace_algebraMap_ratFunc W RatFunc.X_ne_zero,
      RatFunc.intDegree_X]
    norm_num
  have hlt : W.infinityPlace
      (algebraMap F W.FunctionField W.a₁ * genericX W + algebraMap F W.FunctionField W.a₃) <
      W.infinityPlace (2 * genericY W) := by
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul, hx, hy]
      calc W.infinityPlace (algebraMap F W.FunctionField W.a₁) * WithZero.exp 2
          ≤ 1 * WithZero.exp 2 := by gcongr; exact hc _
        _ < WithZero.exp 3 := by rw [one_mul, WithZero.exp_lt_exp]; norm_num
    · rw [hy]
      exact (hc _).trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
  rw [add_assoc, Valuation.map_add_eq_of_lt_left _ hlt, hy]

/-- **The pole divisor of `2y + a₁x + a₃` is `3 O`** away from characteristic two. -/
@[simp]
theorem poles_invariantDifferentialDenom (h2 : (2 : F) ≠ 0) :
    Divisor.poles W.isFunctionField
        (Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W)) =
      (3 : ℤ) • WeilDivisor.ofPoint (Place.infinity W) := by
  ext P
  rw [Divisor.coeff_poles, WeilDivisor.coeff_zsmul, Units.val_mk0]
  rcases eq_or_ne P (Place.infinity W) with rfl | hP
  · rw [WeilDivisor.coeff_ofPoint_self, ord_infinity_invariantDifferentialDenom h2]
    norm_num
  · have h := ord_invariantDifferentialDenom_nonneg hP
    rw [WeilDivisor.coeff_ofPoint_of_ne hP]
    omega

/-- **The place at infinity is tamely ramified** away from characteristic two: its different
exponent over `F(x)` is `1 = e - 1`. -/
@[simp]
theorem differentExponent_infinity_of_two_ne_zero (h2 : (2 : F) ≠ 0) :
    Place.differentExponent F (RatFunc F) (Place.infinity W) = 1 := by
  have h := differentExponent_infinity_eq_four_add_ord W
  rw [ord_infinity_invariantDifferentialDenom h2] at h
  omega

/-- **The different away from characteristic two**: `Diff(F(W) / F(x))` is the divisor of zeros
of `2y + a₁x + a₃` plus the place at infinity. -/
theorem different_eq_zeros_add_of_two_ne_zero (h2 : (2 : F) ≠ 0) :
    Divisor.different F W.FunctionField (IsFunctionField.ratFunc F) =
      Divisor.zeros W.isFunctionField
          (Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W)) +
        WeilDivisor.ofPoint (Place.infinity W) := by
  rw [different_eq_principal_invariantDifferentialDenom_add, ← Divisor.zeros_sub_poles,
    poles_invariantDifferentialDenom h2]
  abel

/-- `2y + a₁x + a₃` vanishes at the place of an affine point of order two. -/
private theorem ord_invariantDifferentialDenom_pos {x y : F} (h : W.Nonsingular x y)
    (hT : -Point.some x y h = Point.some x y h) :
    0 < (pointEquivDegreeOnePlace W (.some x y h)).1.ord (invariantDifferentialDenom W) := by
  have : IsDedekindDomain W.CoordinateRing :=
    have := isIntegrallyClosed_coordinateRing W
    W.isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  -- A point of order two is its own negative, so `y = -y - a₁x - a₃`.
  have hy : W.polynomialY.evalEval x y = 0 := by
    rw [Point.neg_some, Point.some.injEq] at hT
    rw [evalEval_polynomialY]
    have h := hT.2
    simp only [negY] at h
    linear_combination -h
  have hv := CoordinateRing.valuation_pointPlace_div_lt_one W.FunctionField h.left
    (p := W.polynomialY) (q := 1) (by simp) hy
  rw [map_one, map_one, div_one, ← invariantDifferentialDenom_eq_algebraMap_mk_polynomialY,
    ← Place.valuation_ofPrime F W.FunctionField] at hv
  rw [coe_pointEquivDegreeOnePlace_some]
  exact (Place.valuation_lt_one_iff_ord_pos _ (invariantDifferentialDenom_ne_zero W)).mp hv

/-- **The zeros of `2y + a₁x + a₃` have degree `3`** away from characteristic two: by the product
formula they have the degree of its pole divisor `3 O`. -/
@[simp]
theorem degree_zeros_invariantDifferentialDenom (h2 : (2 : F) ≠ 0) :
    Divisor.degree (Divisor.zeros W.isFunctionField
        (Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W))) = 3 := by
  have h := Divisor.degree_principal W.isFunctionField
    (Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W))
  rw [← Divisor.zeros_sub_poles, Divisor.degree_sub, poles_invariantDifferentialDenom h2,
    Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infinity] at h
  omega

/-- The places of a finite set of affine points of order two are zeros of `2y + a₁x + a₃`. -/
private theorem sum_ofPoint_le_zeros {A : Finset W.Point} (hA0 : (0 : W.Point) ∉ A)
    (hA : ∀ T ∈ A, -T = T) :
    ∑ T ∈ A, WeilDivisor.ofPoint (pointEquivDegreeOnePlace W T).1 ≤
      Divisor.zeros W.isFunctionField
        (Units.mk0 (invariantDifferentialDenom W) (invariantDifferentialDenom_ne_zero W)) := by
  classical
  have hpl : Function.Injective fun T ↦ (pointEquivDegreeOnePlace W T).1 :=
    Subtype.val_injective.comp (pointEquivDegreeOnePlace W).injective
  rw [← Finset.sum_image fun _ _ _ _ h ↦ hpl h, WeilDivisor.le_iff]
  intro Q
  rw [WeilDivisor.coeff_sum_ofPoint, Divisor.coeff_zeros, Units.val_mk0]
  split_ifs with hQ
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hQ
    cases T with
    | zero => exact absurd hT hA0
    | some x y h => exact (ord_invariantDifferentialDenom_pos h (hA _ hT)).trans_le le_sup_left
  · exact le_sup_right

/-- **The different when the points of order two are rational**: away from characteristic two,
if `S` is a set of four rational points of order dividing two, then `Diff(F(W) / F(x))` is the
sum of their places. This applies when `W` has full rational `2`-torsion, as `y² = x³ - x`
does. -/
theorem different_eq_sum_of_card_eq_four (h2 : (2 : F) ≠ 0) {S : Finset W.Point}
    (hS : ∀ T ∈ S, -T = T) (hcard : S.card = 4) :
    Divisor.different F W.FunctionField (IsFunctionField.ratFunc F) =
      ∑ T ∈ S, WeilDivisor.ofPoint (pointEquivDegreeOnePlace W T).1 := by
  classical
  -- The affine points of `S` give at most `3` zeros of `2y + a₁x + a₃`, counted with degree.
  have hle := sum_ofPoint_le_zeros (A := S.erase 0) (Finset.notMem_erase 0 S)
    fun T hT ↦ hS T (Finset.mem_of_mem_erase hT)
  have hdeg : Divisor.degree (∑ T ∈ S.erase 0,
      WeilDivisor.ofPoint (pointEquivDegreeOnePlace W T).1) = (S.erase 0).card := by
    simp [map_sum, Divisor.degree_ofPoint, (pointEquivDegreeOnePlace W _).2]
  have hA := Divisor.degree_le_of_le hle
  rw [hdeg, degree_zeros_invariantDifferentialDenom h2] at hA
  -- So `S` contains the point at infinity, and the inequality is an equality of divisors.
  have h0 : (0 : W.Point) ∈ S := by
    by_contra h0
    rw [Finset.erase_eq_of_notMem h0, hcard] at hA
    omega
  have heq := Divisor.eq_of_le_of_degree_eq W.isFunctionField hle (by
    rw [hdeg, degree_zeros_invariantDifferentialDenom h2, Finset.card_erase_of_mem h0, hcard]
    norm_num)
  rw [← Finset.add_sum_erase S _ h0, heq, different_eq_zeros_add_of_two_ne_zero h2, add_comm,
    Point.zero_def, coe_pointEquivDegreeOnePlace_zero]

end TwoNeZero

end WeierstrassCurve.Affine
