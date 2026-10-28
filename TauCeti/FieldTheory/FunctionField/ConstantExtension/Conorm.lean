/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Fibre
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm

/-!
# Divisor degrees under algebraic extension of constants

For a function field with exact constants, conorm along a separable algebraic constant
extension preserves divisor degrees, even when the extension is infinite. Each place is
unramified and the degrees of its finitely many extensions sum to its degree. Additivity
then gives the identity for every divisor. Together with preservation of Riemann–Roch
dimensions, this identifies canonical classes and detects principal divisors after extending
constants.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
  Theorem 3.6.3(c).
-/

public section

namespace TauCeti

open AlgebraicGeometry

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral F F'] [Algebra.IsSeparable k k']
variable [∀ P : Place k F, Finite {P' : Place k' F' // P'.restrict k F = P}]

/-- **Conorm preserves degrees under separable algebraic extension of exact constants**
(Stichtenoth, Theorem 3.6.3(c)). The constant extension may be infinite; finiteness of its
place fibres is supplied by
`Place.finite_setOf_restrict_eq_of_constantCompositum_eq_top`. -/
@[simp]
theorem Divisor.degree_conorm_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) (D : Divisor k F) :
    Divisor.degree (Divisor.conorm k' F' D) = Divisor.degree D := by
  classical
  have hpoint (P : Place k F) :
      Divisor.degree (Divisor.conorm k' F' (WeilDivisor.ofPoint P)) = P.degree := by
    have hfin := Place.finite_setOf_restrict_eq_of_constantCompositum_eq_top hF h P
    have hsum := Place.finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top hF hex h P
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    rw [Divisor.conorm_ofPoint, WeilDivisor.ofFinsetWithMultiplicity_eq_sum, map_sum]
    simp only [Divisor.degree_zsmul, Divisor.degree_ofPoint,
      Place.ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h,
      Nat.cast_one, one_mul]
    exact_mod_cast hsum
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, hD, hE]
  | single P n =>
    rw [WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, Divisor.degree_zsmul,
      Divisor.degree_zsmul, Divisor.degree_ofPoint, hpoint]

end TauCeti
