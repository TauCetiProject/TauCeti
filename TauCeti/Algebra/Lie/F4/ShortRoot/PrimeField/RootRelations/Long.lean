/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup
public import TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.Long

/-!
# The adjacent-long-root relation in the characteristic-two F₄ carrier

The two long simple-root subgroups of the short-root carrier generated over 𝔽₂ satisfy
`[x₀(a), x₁(b)] = n₀ x₁(ab) n₀⁻¹`. The sum-root subgroup is the existing closed
Weyl-transported subgroup, not a newly chosen parametrization. The relation is valid over
every commutative 𝔽₂-algebra, including nonreduced algebras.

The proof transfers the integral matrix identity from
`TauCeti.Algebra.Lie.F4.ShortRoot.RootRelations.Long`. It does not identify the carrier
generated over 𝔽₂ with the specialization of the integral toral closure, or with an
independently constructed pinned group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open scoped commutatorElement

universe v

/-- The commutator of the two long positive simple-root subgroups is the closed
Weyl-transported subgroup at their sum, with parameter `a * b`. -/
theorem commutatorElement_rootSubgroupPoints_long (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b)⁆ =
        weylRootSubgroupPoints [0] 1 A (Multiplicative.ofAdd (a * b)) := by
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply, coe_rootSubgroupPoints,
    coe_weylRootSubgroupPoints]
  exact congrArg Subtype.val (F4ShortRoot.commutatorElement_rootSubgroupPoints_long A a b)

/-- The reverse commutator uses the same sum-root subgroup and parameter: minus signs
coincide with plus signs over every 𝔽₂-algebra. -/
theorem commutatorElement_rootSubgroupPoints_long_reverse (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a)⁆ =
        weylRootSubgroupPoints [0] 1 A (Multiplicative.ofAdd (a * b)) := by
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply, coe_rootSubgroupPoints,
    coe_weylRootSubgroupPoints]
  have htwo : (2 : A) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap (ZMod 2) A) (by decide : (2 : ZMod 2) = 0)
  have hneg : -(a * b) = a * b := by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, htwo, zero_mul]
  have h := congrArg (F4ShortRoot.points A).subtype
    (F4ShortRoot.commutatorElement_rootSubgroupPoints_long_reverse A a b)
  simpa only [map_commutatorElement, Subgroup.subtype_apply, hneg] using h

end TauCeti.F4ShortRoot.PrimeField
