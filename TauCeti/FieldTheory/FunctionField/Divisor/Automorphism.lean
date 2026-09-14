/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Action
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois

/-!
# The automorphism group acting on the divisors of a function field

An `F`-automorphism `σ` of `F'` permutes the places of `F' / k`
(`TauCeti.Place.instMulActionAlgEquiv`), hence permutes the divisors of `F' / k`. Taking the
middle field to be `k` itself, this is the action of `Aut(F'/k)` on the divisor group of
`F' / k`.

The formal action is the one a permutation of the points induces on formal divisors
(`TauCeti.AlgebraicGeometry.WeilDivisor.instDistribMulAction`); what is new here is that it is
compatible with the two pieces of structure that make a formal divisor a divisor of a function
field. The degree is preserved, because an automorphism identifies the residue field of `σ • P`
with that of `P` over the constants; and the divisor map `z ↦ div z` is equivariant, so the
action carries principal divisors to principal divisors and descends to divisor classes.

## Main results

* `TauCeti.Divisor.degree_smul`: an automorphism preserves the degree of a divisor;
* `TauCeti.Divisor.principal_smul`: `div (σ z) = σ • div z`, the equivariance of the principal
  divisor map;
* `TauCeti.Divisor.smul_mem_principalSubgroup_iff` and
  `TauCeti.Divisor.linearlyEquivalent_smul_iff`: the action preserves the principal divisors and
  linear equivalence, so it descends to the divisor classes.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4 for divisors and Section III.5 for the automorphism action on places.
* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser, 2006,
  Chapter 9, for automorphism groups of function fields.
-/

public section

namespace TauCeti

namespace Divisor

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (σ : F' ≃ₐ[F] F')

/-- **An automorphism preserves the degree of a divisor**: it permutes the places and leaves
each residue degree unchanged, so the weighted sum defining the degree is only reindexed. -/
@[simp]
theorem degree_smul (D : Divisor k F') : degree (σ • D) = degree D := by
  rw [degree_eq_weightedDegree, degree_eq_weightedDegree,
    AlgebraicGeometry.WeilDivisor.weightedDegree_smul]
  simp

/-- **The principal divisor map is equivariant**: an automorphism carries `div z` to
`div (σ z)`. -/
theorem principal_smul (hF : IsFunctionField k F') (z : F'ˣ) :
    principal hF (Units.map (σ : F' →* F') z) = σ • principal hF z := by
  refine AlgebraicGeometry.WeilDivisor.ext fun Q ↦ ?_
  rw [coeff_principal, AlgebraicGeometry.WeilDivisor.coeff_smul, coeff_principal,
    Place.ord_smul, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  simp

/-- **The action preserves the principal divisors**, so it descends to the divisor classes. -/
@[simp]
theorem smul_mem_principalSubgroup_iff (hF : IsFunctionField k F') {D : Divisor k F'} :
    σ • D ∈ (Place.orderSystem hF).principalSubgroup ↔
      D ∈ (Place.orderSystem hF).principalSubgroup := by
  simp only [mem_principalSubgroup_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨Units.map ((σ⁻¹ : F' ≃ₐ[F] F') : F' →* F') z, by
      rw [principal_smul, hz, inv_smul_smul]⟩
  · rintro ⟨z, hz⟩
    exact ⟨Units.map (σ : F' →* F') z, by rw [principal_smul, hz]⟩

/-- **Linear equivalence is preserved by the automorphism group**: `σ • A` and `σ • B` are
linearly equivalent exactly when `A` and `B` are. -/
@[simp]
theorem linearlyEquivalent_smul_iff (hF : IsFunctionField k F') {A B : Divisor k F'} :
    (Place.orderSystem hF).LinearlyEquivalent (σ • A) (σ • B) ↔
      (Place.orderSystem hF).LinearlyEquivalent A B := by
  rw [AlgebraicGeometry.WeilDivisor.OrderSystem.linearlyEquivalent_iff,
    AlgebraicGeometry.WeilDivisor.OrderSystem.linearlyEquivalent_iff, ← smul_sub,
    smul_mem_principalSubgroup_iff]

end Divisor

end TauCeti
