/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Different
public import TauCeti.FieldTheory.FunctionField.Different.Separating
public import TauCeti.FieldTheory.FunctionField.Elliptic.Weierstrass.Model
-- Proof-only: transport of different exponents along algebra isomorphisms.
import TauCeti.FieldTheory.FunctionField.Different.Tower
-- Proof-only: the different exponents of a quadratic extension away from characteristic two are at
-- most one.
import TauCeti.FieldTheory.FunctionField.Hyperelliptic.BranchPlaces

/-!
# The different of a function field in Weierstrass coordinates

Let `F / k` be an algebraic function field with Weierstrass coordinates `x` and `y` at a place `P`
of degree one for an elliptic Weierstrass curve `W` over `k`: `x` and `y` have pole divisors `2P`
and `3P` and satisfy the Weierstrass equation

`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, `aᵢ ∈ k`.

Then `F = k(x, y)` is isomorphic over `k(x)` to the function field `k(W)` of `W`, with `P`
corresponding to the place at infinity of `W`.  Transporting the different of `k(W) / k(x)`
(`WeierstrassCurve.Affine.different_eq_principal_invariantDifferentialDenom_add`) along this
isomorphism shows that `F / k(x)` is separable of degree two and computes its different in every
characteristic:

`Diff(F / k(x)) = div (2y + a₁x + a₃) + 4P`.

Away from characteristic two, `2y + a₁x + a₃` has pole divisor `3P` and only simple zeros, so

`Diff(F / k(x)) = (2y + a₁x + a₃)₀ + P = Q₁ + ⋯ + Q_r + P`,

where `Q₁, …, Q_r` are the zeros of `2y + a₁x + a₃`.  When `W` is in the characteristic-not-two
normal form `y² = x³ + a₂x² + a₄x + a₆` (`W.IsCharNeTwoNF`), `2y + a₁x + a₃ = 2y`, so `y` has only
simple zeros and

`Diff(F / k(x)) = (y)₀ + P = Q₁ + ⋯ + Q_r + P`,

where `Q₁, …, Q_r` are the zeros of `y`.  This is part (b) of Stichtenoth's Proposition 6.1.3.

## Main results

* `TauCeti.Place.IsWeierstrassCoordinates.different_eq_principal_add`: **in every characteristic,
  `Diff(F / k(x)) = div (2y + a₁x + a₃) + 4P`.**
* `TauCeti.Place.IsWeierstrassCoordinates.differentExponent_eq_ord` and
  `TauCeti.Place.IsWeierstrassCoordinates.differentExponent_self`: the different exponents of
  `F / k(x)` away from `P` and at `P`.
* `TauCeti.Place.IsWeierstrassCoordinates.different_eq_zeros_add_of_two_ne_zero` and
  `TauCeti.Place.IsWeierstrassCoordinates.different_eq_sum_support_zeros_add_of_two_ne_zero`: away
  from characteristic two, `2y + a₁x + a₃` has only simple zeros and
  `Diff(F / k(x)) = (2y + a₁x + a₃)₀ + P`.
* `TauCeti.Place.IsWeierstrassCoordinates.different_eq_zeros_y_add` and
  `TauCeti.Place.IsWeierstrassCoordinates.different_eq_sum_support_zeros_y_add`: **in the normal
  form `y² = x³ + a₂x² + a₄x + a₆` away from characteristic two, `y` has only simple zeros and
  `Diff(F / k(x)) = (y)₀ + P = Q₁ + ⋯ + Q_r + P`** (Stichtenoth, Proposition 6.1.3(b)).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 6.1.3.
-/

public section

namespace TauCeti

open AlgebraicGeometry WeierstrassCurve

open scoped _root_.IntermediateField _root_.RatFunc

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place.IsWeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : P.IsWeierstrassCoordinates W x y)
include h

section Elliptic

variable [W.IsElliptic]

variable (hF : IsFunctionField k F) (hP : P.degree = 1)
include hF hP

/-- Transporting a place of `F` to `k(W)` along the isomorphism induced by Weierstrass coordinates
preserves its different exponent over `k(x)`. -/
private theorem differentExponent_eq_differentExponent_map_symm (Q : Place k F) :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Place.differentExponent k k⟮x⟯ Q =
      Place.differentExponent k (RatFunc k)
        (Q.map (W.toAffine.functionFieldEquivOfAdjoinEqTop
          h.equation h.transcendental_x (h.adjoin_eq_top hF hP)).symm) := by
  have hx := h.transcendental_x
  have hxy := h.adjoin_eq_top hF hP
  let _ := hF.finiteDimensional_adjoin hx
  let _ := h.isSeparable_adjoin_x hF hP
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  rw [← Place.differentExponent_ratFunc_eq_differentExponent_adjoin hF hx Q,
    ← Place.differentExponent_map_restrictScalars Q
      (W.toAffine.functionFieldRatFuncEquivOfAdjoinEqTop h.equation hx hxy).symm,
    Affine.restrictScalars_symm_functionFieldRatFuncEquivOfAdjoinEqTop]

/-- **The different exponents away from `P`**: at every place `Q ≠ P`, the different exponent of
`F / k(x)` is the order of `2y + a₁x + a₃` at `Q`. -/
theorem differentExponent_eq_ord {Q : Place k F} (hQ : Q ≠ P) :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    (Place.differentExponent k k⟮x⟯ Q : ℤ) =
      Q.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) := by
  have hx := h.transcendental_x
  have hxy := h.adjoin_eq_top hF hP
  let _ := hF.finiteDimensional_adjoin hx
  let _ := h.isSeparable_adjoin_x hF hP
  set e := W.toAffine.functionFieldEquivOfAdjoinEqTop h.equation hx hxy
  have hQ' : Q.map e.symm ≠ infinity W.toAffine := by
    rw [← h.map_symm_functionFieldEquivOfAdjoinEqTop hxy, ← mapEquiv_apply, ← mapEquiv_apply]
    exact (mapEquiv e.symm).injective.ne hQ
  rw [h.differentExponent_eq_differentExponent_map_symm hF hP Q,
    W.toAffine.differentExponent_eq_ord_invariantDifferentialDenom hQ', ord_map,
    AlgEquiv.symm_symm, ← Affine.functionFieldEquivOfAdjoinEqTop_symm_two_mul_add h.equation hx hxy,
    e.apply_symm_apply]

/-- **The different exponent at `P`** is `4 + ord_P (2y + a₁x + a₃)`. -/
theorem differentExponent_self :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    (Place.differentExponent k k⟮x⟯ P : ℤ) =
      4 + P.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) := by
  have hx := h.transcendental_x
  have hxy := h.adjoin_eq_top hF hP
  let _ := hF.finiteDimensional_adjoin hx
  let _ := h.isSeparable_adjoin_x hF hP
  set e := W.toAffine.functionFieldEquivOfAdjoinEqTop h.equation hx hxy
  rw [h.differentExponent_eq_differentExponent_map_symm hF hP P,
    h.map_symm_functionFieldEquivOfAdjoinEqTop hxy,
    W.toAffine.differentExponent_infinity_eq_four_add_ord,
    ← h.map_infinity_functionFieldEquivOfAdjoinEqTop hxy, ord_map,
    Affine.functionFieldEquivOfAdjoinEqTop_symm_two_mul_add]

/-- **The different of an elliptic function field over `k(x)`**: in every characteristic,
`Diff(F / k(x)) = div (2y + a₁x + a₃) + 4P`. -/
theorem different_eq_principal_add :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Divisor.different k F h.transcendental_x.isFunctionField_adjoin =
      Divisor.principal hF
          (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
            h.two_mul_add_ne_zero) +
        (4 : ℤ) • WeilDivisor.ofPoint P := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  ext Q
  rw [Divisor.coeff_different, WeilDivisor.coeff_add, Divisor.coeff_principal, Units.val_mk0,
    WeilDivisor.coeff_zsmul]
  rcases eq_or_ne Q P with rfl | hQ
  · rw [h.differentExponent_self hF hP, WeilDivisor.coeff_ofPoint_self]
    ring
  · rw [h.differentExponent_eq_ord hF hP hQ, WeilDivisor.coeff_ofPoint_of_ne hQ]
    ring

/-- **The different of `F / k(x)` has degree `4`** in every characteristic. -/
theorem degree_different :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Divisor.degree (Divisor.different k F h.transcendental_x.isFunctionField_adjoin) = 4 := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  rw [h.different_eq_principal_add hF hP, Divisor.degree_add, Divisor.degree_principal,
    Divisor.degree_zsmul, Divisor.degree_ofPoint, hP]
  norm_num

/-! ### Away from characteristic two -/

section TwoNeZero

variable (h2 : (2 : k) ≠ 0)
include h2

/-- **The place `P` is tamely ramified over `k(x)`** away from characteristic two: its different
exponent is `1`. -/
theorem differentExponent_self_of_two_ne_zero :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Place.differentExponent k k⟮x⟯ P = 1 := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  have hself := h.differentExponent_self hF hP
  rw [h.ord_two_mul_add h2] at hself
  omega

/-- **The different away from characteristic two**: `Diff(F / k(x))` is the zero divisor of
`2y + a₁x + a₃` plus `P`. -/
theorem different_eq_zeros_add_of_two_ne_zero :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Divisor.different k F h.transcendental_x.isFunctionField_adjoin =
      Divisor.zeros hF
          (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
            h.two_mul_add_ne_zero) +
        WeilDivisor.ofPoint P := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  rw [h.different_eq_principal_add hF hP, ← Divisor.zeros_sub_poles, h.poles_two_mul_add hF h2]
  abel

/-- **Every zero of `2y + a₁x + a₃` has order at most one** away from characteristic two, because
the order away from `P` equals the different exponent of the quadratic extension `F / k(x)`. -/
theorem ord_two_mul_add_le_one (Q : Place k F) :
    Q.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) ≤ 1 := by
  rcases eq_or_ne Q P with rfl | hQ
  · rw [h.ord_two_mul_add h2]
    decide
  · let _ : NeZero (2 : k) := ⟨h2⟩
    let _ := hF.finiteDimensional_adjoin h.transcendental_x
    let _ := h.isSeparable_adjoin_x hF hP
    rw [← h.differentExponent_eq_ord hF hP hQ]
    exact_mod_cast differentExponent_adjoin_le_one (h.finrank_adjoin_x_eq_two hF hP) Q

/-- **Every zero of `2y + a₁x + a₃` is simple** away from characteristic two. -/
theorem ord_two_mul_add_eq_one_of_pos {Q : Place k F}
    (hQ : 0 < Q.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)) :
    Q.ord (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) = 1 :=
  le_antisymm (h.ord_two_mul_add_le_one hF hP h2 Q) hQ

/-- **The zero divisor of `2y + a₁x + a₃` is the sum of its support** away from characteristic two,
since every zero is simple. -/
theorem zeros_two_mul_add_eq_sum_support :
    Divisor.zeros hF
        (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
          h.two_mul_add_ne_zero) =
      ∑ Q ∈ (Divisor.zeros hF
          (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
            h.two_mul_add_ne_zero)).support,
        WeilDivisor.ofPoint Q := by
  classical
  ext Q
  rw [WeilDivisor.coeff_sum_ofPoint, Divisor.coeff_zeros, Units.val_mk0]
  split_ifs with hQ
  · rw [Divisor.mem_support_zeros_iff, Units.val_mk0] at hQ
    rw [h.ord_two_mul_add_eq_one_of_pos hF hP h2 hQ]
    rfl
  · rw [Divisor.mem_support_zeros_iff, Units.val_mk0, not_lt] at hQ
    exact sup_eq_right.mpr hQ

/-- **The different as a sum of places away from characteristic two**: `Diff(F / k(x))` is the sum
of the distinct zeros of `2y + a₁x + a₃` plus `P`. -/
theorem different_eq_sum_support_zeros_add_of_two_ne_zero :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Divisor.different k F h.transcendental_x.isFunctionField_adjoin =
      (∑ Q ∈ (Divisor.zeros hF
          (Units.mk0 (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)
            h.two_mul_add_ne_zero)).support,
        WeilDivisor.ofPoint Q) +
        WeilDivisor.ofPoint P := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  exact (h.different_eq_zeros_add_of_two_ne_zero hF hP h2).trans
    (congrArg (· + WeilDivisor.ofPoint P) (h.zeros_two_mul_add_eq_sum_support hF hP h2))

/-! ### The characteristic-not-two normal form `y² = x³ + a₂x² + a₄x + a₆` -/

section CharNeTwoNF

variable [W.IsCharNeTwoNF]

/-- **The different exponent away from `P` in the normal form `y² = x³ + a₂x² + a₄x + a₆`**: at
every place `Q ≠ P`, the different exponent of `F / k(x)` is `ord_Q y`. -/
theorem differentExponent_eq_ord_y {Q : Place k F} (hQ : Q ≠ P) :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    (Place.differentExponent k k⟮x⟯ Q : ℤ) = Q.ord y := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  rw [h.differentExponent_eq_ord hF hP hQ, h.ord_two_mul_add_eq_ord_y h2 Q]

/-- **Every zero of `y` has order at most one** in the normal form `y² = x³ + a₂x² + a₄x + a₆`
away from characteristic two (Stichtenoth, Proposition 6.1.3(b)). -/
theorem ord_y_le_one (Q : Place k F) : Q.ord y ≤ 1 := by
  rw [← h.ord_two_mul_add_eq_ord_y h2 Q]
  exact h.ord_two_mul_add_le_one hF hP h2 Q

/-- **Every zero of `y` is simple** in the normal form `y² = x³ + a₂x² + a₄x + a₆` away from
characteristic two (Stichtenoth, Proposition 6.1.3(b)). -/
theorem ord_y_eq_one_of_pos {Q : Place k F} (hQ : 0 < Q.ord y) : Q.ord y = 1 :=
  le_antisymm (h.ord_y_le_one hF hP h2 Q) hQ

/-- **The zero divisor of `y` is the sum of its support** in the normal form
`y² = x³ + a₂x² + a₄x + a₆` away from characteristic two (Stichtenoth, Proposition 6.1.3(b)). -/
theorem zeros_y_eq_sum_support :
    Divisor.zeros hF (Units.mk0 y h.y_ne_zero) =
      ∑ Q ∈ (Divisor.zeros hF (Units.mk0 y h.y_ne_zero)).support, WeilDivisor.ofPoint Q := by
  simpa only [h.zeros_two_mul_add_eq_zeros_y hF h2] using
    h.zeros_two_mul_add_eq_sum_support hF hP h2

/-- **The different in the normal form `y² = x³ + a₂x² + a₄x + a₆`** away from characteristic two:
`Diff(F / k(x)) = div y + 4P`. -/
theorem different_eq_principal_y_add :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Divisor.different k F h.transcendental_x.isFunctionField_adjoin =
      Divisor.principal hF (Units.mk0 y h.y_ne_zero) + (4 : ℤ) • WeilDivisor.ofPoint P := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  rw [h.different_eq_principal_add hF hP, h.principal_two_mul_add_eq_principal_y hF h2]

/-- **The different in the normal form `y² = x³ + a₂x² + a₄x + a₆`** (Stichtenoth,
Proposition 6.1.3(b)): away from characteristic two, `Diff(F / k(x)) = (y)₀ + P`. -/
theorem different_eq_zeros_y_add :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Divisor.different k F h.transcendental_x.isFunctionField_adjoin =
      Divisor.zeros hF (Units.mk0 y h.y_ne_zero) + WeilDivisor.ofPoint P := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  rw [h.different_eq_zeros_add_of_two_ne_zero hF hP h2, h.zeros_two_mul_add_eq_zeros_y hF h2]

/-- **The different as a sum of places in the normal form `y² = x³ + a₂x² + a₄x + a₆`**
(Stichtenoth, Proposition 6.1.3(b)): away from characteristic two,
`Diff(F / k(x)) = Q₁ + ⋯ + Q_r + P`, where `Q₁, …, Q_r` are the zeros of `y`. -/
theorem different_eq_sum_support_zeros_y_add :
    haveI := hF.finiteDimensional_adjoin h.transcendental_x
    haveI := h.isSeparable_adjoin_x hF hP
    Divisor.different k F h.transcendental_x.isFunctionField_adjoin =
      (∑ Q ∈ (Divisor.zeros hF (Units.mk0 y h.y_ne_zero)).support, WeilDivisor.ofPoint Q) +
        WeilDivisor.ofPoint P := by
  let _ := hF.finiteDimensional_adjoin h.transcendental_x
  let _ := h.isSeparable_adjoin_x hF hP
  exact (h.different_eq_zeros_y_add hF hP h2).trans
    (congrArg (· + WeilDivisor.ofPoint P) (h.zeros_y_eq_sum_support hF hP h2))

end CharNeTwoNF

end TwoNeZero

end Elliptic

end Place.IsWeierstrassCoordinates

end TauCeti
