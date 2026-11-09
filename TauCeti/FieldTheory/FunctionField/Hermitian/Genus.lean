/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hermitian.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.FunctionField.Radical.Genus
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# The genus of a Hermitian function field

For Hermitian coordinates `y ^ q + y = x ^ (q + 1)`, with `q > 1` and `q = 0` in the
constant field, the exact constant field is `K` and the genus is `q(q - 1)/2`.
The projection to `y` is a tame radical extension of degree `q + 1`. Its radicand
`T ^ q + T` is squarefree, and its zeros and its pole at infinity are totally ramified.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 6.4 and Proposition 3.7.3.
-/

public section

open Polynomial
open TauCeti.AlgebraicGeometry
open scoped IntermediateField

namespace TauCeti.IsHermitianCoordinates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {q : ℕ} {x y : F} (h : IsHermitianCoordinates K q x y)
include h

omit h in
private theorem radicand_degree (hq : 1 < q) : (X ^ q + X : K[X]).natDegree = q := by
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa using hq

omit h in
private theorem radicand_squarefree (hchar : (q : K) = 0) : Squarefree (X ^ q + X : K[X]) := by
  simpa using
    (separable_C_mul_X_pow_add_C_mul_X_add_C (1 : K) 1 0 hchar isUnit_one).squarefree

section RationalBase

variable (hq : 1 < q)

private theorem rational_equation :
    let := ratFuncAlgebraOfTranscendental h.transcendental_y
    x ^ (q + 1) = algebraMap (RatFunc K) F
      (algebraMap K[X] (RatFunc K) (X ^ q + X)) := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  simpa [map_add, map_pow, RatFunc.algebraMap_X] using h.equation.symm

omit h in
private theorem radicand_gcd_ord_infty (hq : 1 < q) :
    Int.gcd (q + 1 : ℕ) ((Place.infty K).ord (algebraMap K[X] (RatFunc K) (X ^ q + X))) = 1 := by
  rw [Place.ord_infty, RatFunc.intDegree_polynomial, radicand_degree hq, Int.gcd_neg,
    Int.gcd_natCast_natCast]
  simp

/-- A Hermitian equation with `q = 0` in `K` acquires no new constants. -/
theorem isIntegrallyClosedIn (hq : 1 < q) (hchar : (q : K) = 0) : IsIntegrallyClosedIn K F := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  let := isScalarTower_ratFuncAlgebraOfTranscendental h.transcendental_y
  exact isIntegrallyClosedIn_of_pow_eq_of_gcd_ord_eq_one (IsFunctionField.ratFunc K) inferInstance
    (adjoin_eq_top_ratFunc_of_adjoin_pair_eq_top h.transcendental_y h.adjoin_eq_top)
    h.rational_equation (by simp [hchar])
    (RatFunc.algebraMap_ne_zero (radicand_squarefree hchar).ne_zero) (Place.infty K)
    (radicand_gcd_ord_infty hq)

end RationalBase

/-- **The Hermitian genus formula**: `2g = q(q - 1)` when `q > 1` and `q = 0` in `K`. -/
theorem two_mul_genus_eq (hq : 1 < q) (hchar : (q : K) = 0) :
    2 * genus K F = q * (q - 1) := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  let := isScalarTower_ratFuncAlgebraOfTranscendental h.transcendental_y
  have hg := two_mul_genus_eq_of_pow_eq_of_squarefree
    (adjoin_eq_top_ratFunc_of_adjoin_pair_eq_top h.transcendental_y h.adjoin_eq_top)
    h.rational_equation (by simp [hchar]) (radicand_squarefree hchar)
    (by rw [radicand_degree hq]; omega)
  rw [radicand_degree hq, show Nat.gcd (q + 1) q = 1 by simp] at hg
  have hg' : (2 * genus K F : ℤ) = (q : ℤ) * (q - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    push_cast at hg
    linear_combination hg
  exact_mod_cast hg'

/-- A Hermitian function field with parameter at least three has genus at least two. -/
theorem two_le_genus (hq : 3 ≤ q) (hchar : (q : K) = 0) : 2 ≤ genus K F := by
  have hg := h.two_mul_genus_eq (by omega) hchar
  have hq1 := Nat.sub_add_cancel (by omega : 1 ≤ q)
  nlinarith

end TauCeti.IsHermitianCoordinates
