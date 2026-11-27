/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Resultant of the doubling polynomials

`WeierstrassCurve.resultant_Φ_two_ΨSq_two` computes the resultant of the numerator and
denominator of the doubling map on the x-coordinate. This supplies the unit-resultant condition
for a model of unit discriminant, including in residue characteristic two.

`WeierstrassCurve.sixteen_mul_Φ_two` shows that modulo the denominator `Ψ₂Sq`, the scaled
numerator `16 Φ₂` is the square of the derivative of `Ψ₂Sq`. This relates the resultant to
`WeierstrassCurve.twoTorsionPolynomial_discr`
via `Polynomial.resultant_add_mul_left`. Specialization of the universal equation preserves the
resultant at fixed degrees.

For the multiplication-polynomial resultant formula, see H. Schmidt,
*Resultants and discriminants of multiplication polynomials for elliptic curves*,
J. Number Theory (2015), doi:10.1016/j.jnt.2014.10.007.
-/

open Polynomial

namespace WeierstrassCurve

/-- The scaled doubling numerator is the square of the derivative of the denominator modulo
the denominator. This identity holds over any commutative ring. -/
public theorem sixteen_mul_Φ_two {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    C 16 * W.Φ 2 = W.Ψ₂Sq.derivative ^ 2 + W.Ψ₂Sq * (-(C 32 * X + C (4 * W.b₂))) := by
  have h := congrArg (C : R →+* R[X]) W.b_relation
  simp only [map_mul, map_sub, map_pow, map_ofNat] at h
  simp only [Φ_two, Ψ₂Sq, derivative_add, derivative_mul, derivative_X_pow, derivative_X,
    derivative_C, derivative_ofNat, map_ofNat, Nat.cast_ofNat, mul_one, map_mul,
    zero_mul, zero_add]
  linear_combination -4 * h

/-- The resultant of the doubling polynomials, both taken at formal degree four, equals the
square of the Weierstrass discriminant over any commutative ring. -/
public theorem resultant_Φ_two_ΨSq_two {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (W.Φ 2).resultant (W.ΨSq 2) 4 4 = W.Δ ^ 2 := by
  -- Compute over the universal integral coefficient ring, where 16 can be cancelled.
  have huniversal :
      (Universal.curve.Φ 2).resultant Universal.curve.Ψ₂Sq 4 3 = Universal.curve.Δ ^ 2 := by
    let U := Universal.curve
    have ha : U.twoTorsionPolynomial.a ≠ 0 := by
      dsimp only [twoTorsionPolynomial]
      norm_num
    have hdeg : U.Ψ₂Sq.degree = 3 :=
      Ψ₂Sq_eq U ▸ Cubic.degree_of_a_ne_zero ha
    have hnat : U.Ψ₂Sq.natDegree = 3 := natDegree_eq_of_degree_eq_some hdeg
    have hc : U.Ψ₂Sq.leadingCoeff = 4 :=
      (Ψ₂Sq_eq U).symm ▸ Cubic.leadingCoeff_of_a_ne_zero ha
    have hd : U.Ψ₂Sq.derivative.natDegree ≤ 2 := by
      simpa only [hnat] using natDegree_derivative_le U.Ψ₂Sq
    have hdisc : U.Ψ₂Sq.discr = 16 * U.Δ := by
      rw [Ψ₂Sq_eq, Cubic.toPoly_discr ha, twoTorsionPolynomial_discr]
    have hres : U.Ψ₂Sq.derivative.resultant U.Ψ₂Sq 2 3 = -64 * U.Δ := by
      rw [resultant_comm]
      have h := resultant_deriv (f := U.Ψ₂Sq) (by simp [hdeg])
      rw [hnat, hc, hdisc] at h
      norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv] at h ⊢
      linear_combination h
    have hbound : (-(C 32 * X + C (4 * U.b₂))).natDegree + 3 ≤ 4 := by
      rw [natDegree_neg]
      exact Nat.add_le_add_right natDegree_linear_le 3
    have hscaled : (16 : MvPolynomial Coeff ℤ) ^ 3 * (U.Φ 2).resultant U.Ψ₂Sq 4 3 =
        (U.Ψ₂Sq.derivative.resultant U.Ψ₂Sq 2 3) ^ 2 := by
      rw [← resultant_C_mul_left, sixteen_mul_Φ_two,
        resultant_add_mul_left _ _ _ _ _ hbound hnat.le, pow_two,
        resultant_mul_left_of_natDegree_le hd hd hnat.le, sq]
    apply mul_left_cancel₀ (a := (16 : MvPolynomial Coeff ℤ) ^ 3) (by norm_num)
    rw [hscaled, hres]
    ring
  have h := congrArg W.specialize huniversal
  rw [← resultant_map_map, ← map_Φ, ← map_Ψ₂Sq, map_pow, ← map_Δ] at h
  have hspecialized : (W.Φ 2).resultant W.Ψ₂Sq 4 3 = W.Δ ^ 2 :=
    map_specialize W ▸ h
  have hcoeff : (W.Φ 2).coeff 4 = 1 := W.coeff_Φ 2
  have hdeg : (W.ΨSq 2).natDegree ≤ 3 := W.natDegree_ΨSq_le 2
  rw [resultant_add_right_deg _ _ _ _ 1 hdeg, hcoeff, one_pow, one_mul, ΨSq_two, hspecialized]

end WeierstrassCurve
