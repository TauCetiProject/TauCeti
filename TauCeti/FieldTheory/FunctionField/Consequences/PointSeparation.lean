/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.WeierstrassGaps

/-!
# Separation of rational places in positive genus

In a function field of positive genus with exact constants, a rational place `P` has
`ℓ(P) = 1`: there is no nonconstant function with just a simple pole at `P`, since `1` is
its first Weierstrass gap. Consequently the complete linear system of `P` consists of `P`
alone. Distinct rational places therefore give distinct divisor classes, also after
translation by any fixed base divisor `P₀`.

This is the divisor-class point-separation input to the Abel–Jacobi embedding of a curve
of positive genus. It does not assert the existence of a Picard scheme or an immersion.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1 and Theorem 4.17.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 1.6.8.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- At a rational place of a positive-genus function field with exact constants, the
Riemann–Roch space allowing a simple pole has dimension one. -/
theorem Divisor.dim_ofPoint_eq_one_of_genus_pos (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : 0 < genus k F) {P : Place k F}
    (hP : P.degree = 1) : Divisor.dim (WeilDivisor.ofPoint P : Divisor k F) = 1 := by
  have hgap := (P.mem_weierstrassGaps_iff_isGap hF hex 1).mp
    (P.one_mem_weierstrassGaps hF hex hP hg)
  have hdim := (P.isGap_iff_dim_eq hF (by norm_num : 0 < (1 : ℕ))).mp hgap
  simpa [Divisor.dim_zero_of_isIntegrallyClosedIn hF hex] using hdim

/-- Linearly equivalent places coincide if one is rational and the function field has
positive genus and exact constants. The second place need not be assumed rational. -/
theorem Place.eq_of_linearlyEquivalent_ofPoint_of_genus_pos (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : 0 < genus k F) {P Q : Place k F} (hP : P.degree = 1)
    (h : (Place.orderSystem hF).LinearlyEquivalent
      (WeilDivisor.ofPoint P) (WeilDivisor.ofPoint Q)) : P = Q := by
  exact WeilDivisor.ofPoint_injective (Divisor.eq_of_linearlyEquivalent_of_dim_eq_one hF
    (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P))
    (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint Q))
    (Divisor.dim_ofPoint_eq_one_of_genus_pos hF hex hg hP) h)

namespace Place

variable {P₀ : Place k F}

/-- **Distinct places of degree one of a positive-genus function field have distinct classes**
relative to a base place. -/
theorem eq_of_divisorClass_pointDifference_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : 0 < genus k F) {P Q : Place k F} (hP : P.degree = 1)
    (h : (Place.orderSystem hF).divisorClass (WeilDivisor.pointDifference P P₀) =
      (Place.orderSystem hF).divisorClass (WeilDivisor.pointDifference Q P₀)) :
    P = Q := by
  apply eq_of_linearlyEquivalent_ofPoint_of_genus_pos hF hex hg hP
  apply ((Place.orderSystem hF).divisorClass_eq_iff).mp
  simpa [WeilDivisor.pointDifference] using h

end Place

end TauCeti
