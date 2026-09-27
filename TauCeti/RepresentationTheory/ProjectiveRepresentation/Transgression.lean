/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Character
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.CommonExtension
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Finite

/-!
# Surjective character transgression for the common lifting extension

Every second-cohomology class in `H²(G, kˣ)` is obtained by pushing the common lifting factor set
forward along a character of its kernel. Together with the extension criterion in
`TauCeti.FactorSet.characterTransgression_eq_iff`, this describes both the image and
the fibers of its character transgression. The kernel characters that extend to the
whole group are exactly those invisible to second cohomology.

This is the character-side input to reducing a common lifting extension to a Schur
cover: stem extensions have injective transgression, while this extension has
surjective transgression. No stem property of the common extension is asserted.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

variable (k G : Type) [Field k] [IsAlgClosed k] [Group G] [Finite G]

/-- The character transgression of the common finite lifting extension is surjective
onto `H²(G, kˣ)`, in arbitrary characteristic. -/
theorem projectiveLiftingFactorSet_characterTransgression_surjective :
    Function.Surjective
      ((projectiveLiftingFactorSet k G).characterTransgression (A := kˣ)) := by
  intro x
  obtain ⟨α, hα, hpow, hx⟩ := exists_isFactorSet_pow_card_eq_one_cohomologyClass_eq x
  let b := hα.toRootsOfUnityFactorSet hpow
  let ev := projectiveLiftingCharacter k G b
  refine ⟨Additive.ofMul ((equivariantCharacterEquiv G _ kˣ).symm ev), ?_⟩
  rw [FactorSet.characterTransgression_apply, toMul_ofMul, Equiv.apply_symm_apply]
  have hfac : (projectiveLiftingFactorSet k G).map ev =
      (isProjectiveRep_twistedRegularRep k G α).factorSet := by
    ext p
    simp only [FactorSet.map_apply, ev, projectiveLiftingCharacter_apply,
      projectiveLiftingFactorSet_apply, b, IsFactorSet.coe_toRootsOfUnityFactorSet_apply,
      IsProjectiveRep.factorSet_apply]
  exact (congrArg FactorSet.cohomologyClass hfac).trans
    ((IsProjectiveRep.cohomologyClass_def _).symm.trans hx)

end TauCeti
