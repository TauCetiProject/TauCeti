/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Divisors of the rational function field

The rational function field `k(x)` is the base case of the theory of algebraic function fields,
and this file computes its principal divisors: the divisor of an irreducible polynomial, its
special case the divisor of `x`, and the degree of the pole divisor of a nonzero rational
function.  It continues the rational-function-field thread begun in
`TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic`, where the places of `k(x)` are
classified, and its Riemann–Roch consequences are
`TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc`.

Both calculations run on the classification of the places of `k(x)` together with the order
computations of `TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order`: an irreducible `p` has a
simple zero at the place it defines, a pole of order `deg p` at infinity, and no other zeros or
poles.

## Main results

* `TauCeti.Divisor.principal_irreducible`: `div p = P_(p) - (deg p) · P_∞` for `p` irreducible,
  and its special case `TauCeti.Divisor.principal_X`: `div x = P_(X) - P_∞`.
* `TauCeti.AlgebraicGeometry.WeilDivisor.degree_principal_irreducible`: the unweighted
  coefficient sum of `div p` is `1 - deg p`.
* `TauCeti.Divisor.principal_X_sq_add_one`: `div (x ^ 2 + 1) = P_(X ^ 2 + 1) - 2 P_∞` when
  `X ^ 2 + 1` is irreducible.
* `TauCeti.AlgebraicGeometry.WeilDivisor.degree_principal_X_sq_add_one`: the unweighted
  coefficient sum of `div (x ^ 2 + 1)` is `-1`, although its degree is `0`.
* `TauCeti.Divisor.poles_X`: the pole divisor of `x` is `P_∞`.
* `TauCeti.Divisor.degree_poles_eq_max_natDegree`: the pole divisor of `z ∈ k(x)ˣ` has degree
  `max (deg z.num) (deg z.denom)`, which for nonconstant `z` is the degree of `k(x) / k(z)`.
* `TauCeti.Place.finsum_natDegree_mul_ord_adicOfIrreducible`: the finite-place weighted
  product formula, summing orders against the degrees of monic irreducible polynomials.
* `TauCeti.Divisor.degree_zeros_algebraMap`: the zero divisor of a nonzero polynomial has
  degree equal to its polynomial degree.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.2 and I.4.
-/

public section

noncomputable section

open IsDedekindDomain Polynomial

namespace TauCeti

open AlgebraicGeometry

variable {k : Type*} [Field k]

/-! ### The divisor of an irreducible polynomial -/

/-- **The divisor of an irreducible polynomial**: `div p = P_(p) - (deg p) · P_∞`.  An irreducible
`p` has a simple zero at the finite place it defines, a pole of order `deg p` at infinity, and no
other zeros or poles. -/
theorem Divisor.principal_irreducible {p : k[X]} (hp : Irreducible p) :
    Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (algebraMap k[X] (RatFunc k) p)
          (RatFunc.algebraMap_ne_zero hp.ne_zero)) =
      WeilDivisor.ofPoint (Place.adicOfIrreducible hp) -
        p.natDegree • WeilDivisor.ofPoint (Place.infty k) := by
  refine WeilDivisor.ext fun P ↦ ?_
  rw [Divisor.coeff_principal, WeilDivisor.coeff_sub, Units.val_mk0]
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
  · simp [WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hp).symm]
  · rw [Place.ord_adicOfIrreducible_algebraMap_irreducible hq hp]
    by_cases hqp : Associated q p
    · rw [(Place.adicOfIrreducible_eq_adicOfIrreducible_iff hq hp).mpr hqp]
      simp [WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hp), hqp]
    · simp [WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hq),
        WeilDivisor.coeff_ofPoint_of_ne fun h ↦
          hqp ((Place.adicOfIrreducible_eq_adicOfIrreducible_iff hq hp).mp h), hqp]

/-- **The divisor of `x`**: `div x = P_(X) - P_∞`.  The function `x` has a simple zero at the
place of the polynomial `X`, a simple pole at infinity, and no other zeros or poles. -/
theorem Divisor.principal_X :
    Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) =
      WeilDivisor.ofPoint (Place.adicOfIrreducible (irreducible_X (R := k))) -
        WeilDivisor.ofPoint (Place.infty k) := by
  have hX : Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero =
      Units.mk0 (algebraMap k[X] (RatFunc k) X)
        (RatFunc.algebraMap_ne_zero (irreducible_X (R := k)).ne_zero) :=
    Units.ext RatFunc.algebraMap_X.symm
  rw [hX, Divisor.principal_irreducible, natDegree_X, one_nsmul]

/-- **The unweighted degree of the divisor of an irreducible polynomial** is `1 - deg p`: the
plain sum of the coefficients of `div p = P_(p) - (deg p) · P_∞`. The degree
`TauCeti.Divisor.degree`, which weights each place by its degree, gives `deg p - deg p = 0`
instead, as the product formula `TauCeti.Divisor.degree_principal` requires. -/
theorem AlgebraicGeometry.WeilDivisor.degree_principal_irreducible {p : k[X]}
    (hp : Irreducible p) :
    WeilDivisor.degree (Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (algebraMap k[X] (RatFunc k) p) (RatFunc.algebraMap_ne_zero hp.ne_zero))) =
      1 - (p.natDegree : ℤ) := by
  rw [Divisor.principal_irreducible hp, map_sub, map_nsmul, WeilDivisor.degree_ofPoint,
    WeilDivisor.degree_ofPoint, nsmul_one]

/-- **The divisor of `x ^ 2 + 1`**, when `X ^ 2 + 1` is irreducible: a simple zero at the place
of `X ^ 2 + 1` and a double pole at infinity. The place of `X ^ 2 + 1` is studied in
`TauCeti.FieldTheory.FunctionField.Place.RatFunc.XSqAddOne`. -/
theorem Divisor.principal_X_sq_add_one (h : Irreducible (X ^ 2 + 1 : k[X])) :
    Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (algebraMap k[X] (RatFunc k) (X ^ 2 + 1))
          (RatFunc.algebraMap_ne_zero h.ne_zero)) =
      WeilDivisor.ofPoint (Place.adicOfIrreducible h) -
        2 • WeilDivisor.ofPoint (Place.infty k) := by
  simpa using Divisor.principal_irreducible h

/-- **The unweighted degree of `div (x ^ 2 + 1)` is `-1`**: the plain sum of the coefficients of
a principal divisor need not vanish. The degree `TauCeti.Divisor.degree`, which weights each place
by its degree, gives `1 · 2 - 2 · 1 = 0` instead, as the product formula
`TauCeti.Divisor.degree_principal` requires. -/
theorem AlgebraicGeometry.WeilDivisor.degree_principal_X_sq_add_one
    (h : Irreducible (X ^ 2 + 1 : k[X])) :
    WeilDivisor.degree (Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (algebraMap k[X] (RatFunc k) (X ^ 2 + 1))
          (RatFunc.algebraMap_ne_zero h.ne_zero))) = -1 := by
  rw [WeilDivisor.degree_principal_irreducible h]
  norm_num

/-- **The pole divisor of `x`**: `(x)_∞ = P_∞`.  The function `x` has a simple pole at infinity
and is regular at every other place. -/
@[simp]
theorem Divisor.poles_X :
    Divisor.poles (IsFunctionField.ratFunc k)
        (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) =
      WeilDivisor.ofPoint (Place.infty k) := by
  have hne := Place.adicOfIrreducible_ne_infty (irreducible_X (R := k))
  refine WeilDivisor.ext fun P ↦ ?_
  rw [Divisor.coeff_poles, ← Divisor.coeff_principal (IsFunctionField.ratFunc k),
    Divisor.principal_X, WeilDivisor.coeff_sub]
  by_cases hP : P = Place.infty k
  · subst hP
    simp [WeilDivisor.coeff_ofPoint_of_ne hne.symm]
  · by_cases hP' : P = Place.adicOfIrreducible (irreducible_X (R := k))
    · subst hP'
      simp [WeilDivisor.coeff_ofPoint_of_ne hne]
    · simp [WeilDivisor.coeff_ofPoint_of_ne hP, WeilDivisor.coeff_ofPoint_of_ne hP']

/-! ### The degree of a rational map -/

/-- **Stichtenoth, Theorem 1.4.11 on `ℙ¹`**: the pole divisor of a nonzero rational function
`z ∈ k(x)ˣ` has degree `max (deg z.num) (deg z.denom)`.  For nonconstant `z` this is
`[k(x) : k(z)]`, the degree of the covering `ℙ¹ → ℙ¹` that `z` defines; a constant `z = c` is a
unit at every place, and both sides are `0`.  A rational function is transcendental over `k`
exactly when it is not a constant, by `RatFunc.transcendental_of_ne_C`. -/
theorem Divisor.degree_poles_eq_max_natDegree (z : (RatFunc k)ˣ) :
    Divisor.degree (Divisor.poles (IsFunctionField.ratFunc k) z) =
      max (z : RatFunc k).num.natDegree (z : RatFunc k).denom.natDegree := by
  by_cases hz : IsAlgebraic k (z : RatFunc k)
  · obtain ⟨c, hc⟩ := not_not.mp fun h ↦ RatFunc.transcendental_of_ne_C (z : RatFunc k) h hz
    have hpoles : Divisor.poles (IsFunctionField.ratFunc k) z = 0 :=
      WeilDivisor.ext fun P ↦ by simp [P.ord_eq_zero_of_isAlgebraic hz]
    rw [hpoles, hc]
    simp
  · rw [Divisor.degree_poles _ _ hz, RatFunc.finrank_eq_max_natDegree]

/-- The zero divisor of a nonzero polynomial in `k(x)` has degree equal to the degree of the
polynomial. By the product formula its zeros and poles have equal degrees. -/
theorem Divisor.degree_zeros_algebraMap {f : k[X]} (hf : f ≠ 0) :
    Divisor.degree (Divisor.zeros (IsFunctionField.ratFunc k)
      (Units.mk0 (algebraMap k[X] (RatFunc k) f) (RatFunc.algebraMap_ne_zero hf))) =
        (f.natDegree : ℤ) := by
  set z := Units.mk0 (algebraMap k[X] (RatFunc k) f) (RatFunc.algebraMap_ne_zero hf)
  have hzp : Divisor.degree (Divisor.zeros (IsFunctionField.ratFunc k) z) =
      Divisor.degree (Divisor.poles (IsFunctionField.ratFunc k) z) := by
    have := Divisor.degree_principal (IsFunctionField.ratFunc k) z
    rw [← Divisor.zeros_sub_poles, Divisor.degree_sub] at this
    omega
  rw [hzp, Divisor.degree_poles_eq_max_natDegree]
  simp [z, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]

/-- The finite-place product formula for `k(x)`: the degree-weighted sum of the orders
at monic irreducible polynomials equals `f.intDegree`, the negative of the order at infinity. -/
theorem Place.finsum_natDegree_mul_ord_adicOfIrreducible (f : (RatFunc k)ˣ) :
    (∑ᶠ q : {q : k[X] // q.Monic ∧ Irreducible q},
      (q.val.natDegree : ℤ) * (Place.adicOfIrreducible q.property.2).ord f) =
      (f : RatFunc k).intDegree := by
  classical
  have hord : (fun P : Place k (RatFunc k) => P.ord f).HasFiniteSupport :=
    Place.finite_setOf_ord_ne_zero (IsFunctionField.ratFunc k) f
  have hfin := hord.mul_left (fun P : Place k (RatFunc k) => (P.degree : ℤ))
  have h : ∑ᶠ P : Place k (RatFunc k), P.ord f * P.degree = 0 := by
    let D := Divisor.principal (IsFunctionField.ratFunc k) f
    rw [finsum_eq_sum_of_support_subset _ (s := D.support)]
    · have hc (P : Place k (RatFunc k)) : D P = P.ord f :=
        Divisor.coeff_principal (IsFunctionField.ratFunc k) f P
      have h : Divisor.degree D = 0 := Divisor.degree_principal (IsFunctionField.ratFunc k) f
      simpa only [Divisor.degree_eq_sum_support, hc] using h
    · intro P hP
      apply (Divisor.mem_support_principal_iff (IsFunctionField.ratFunc k)).mpr
      intro h0
      exact hP (by dsimp; rw [h0, zero_mul])
  rw [← finsum_comp_equiv (Place.ratFuncEquivMonicIrreducible k)] at h
  rw [finsum_option] at h
  · simp only [Place.ratFuncEquivMonicIrreducible_none,
      Place.ratFuncEquivMonicIrreducible_some, Place.degree_infty, Place.ord_infty,
      Nat.cast_one, Place.degree_adicOfIrreducible, mul_comm] at h
    omega
  · exact Function.HasFiniteSupport.comp_of_injective (Option.some_injective _)
      (hfin.comp_of_injective (Place.ratFuncEquivMonicIrreducible k).injective)


end TauCeti
