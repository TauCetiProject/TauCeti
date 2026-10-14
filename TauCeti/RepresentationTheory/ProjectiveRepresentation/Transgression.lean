/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Character.Duality
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.CommonExtension
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Finite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Surjective character transgression for the common lifting extension

Every second-cohomology class in `H²(G, kˣ)` is obtained by pushing the common lifting factor set
forward along a character of its kernel. Together with the extension criterion in
`TauCeti.FactorSet.characterTransgression_eq_iff`, this describes both the image and
the fibers of its character transgression. The kernel characters that extend to the
whole group are exactly those invisible to second cohomology.

Over an algebraically closed field whose characteristic does not divide `|G|`,
`projectiveLiftingCohomologyEquiv` identifies second cohomology
with the character dual of the part of the common lifting kernel lying in the commutator
subgroup. This is the kernel comparison needed when reducing the common lifting extension
to a Schur cover. No stem property of the common extension is asserted.

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

section Duality

variable [NeZero (Nat.card G : k)]

local instance : HasEnoughRootsOfUnity k (Monoid.exponent
    (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k)) := by
  apply HasEnoughRootsOfUnity.of_dvd k
    (Monoid.exponent_dvd_of_forall_pow_eq_one (n := Nat.card G) ?_)
  intro m
  funext i
  apply Subtype.ext
  exact (m i).property

local instance : HasEnoughRootsOfUnity k (Monoid.exponent
    (Abelianization (projectiveLiftingFactorSet k G).Extension)) := by
  have hcard : Nat.card (projectiveLiftingFactorSet k G).Extension =
      Nat.card G ^ (Nat.card (FactorSet G (rootsOfUnity (Nat.card G) k)) + 1) := by
    rw [Nat.card_congr (FactorSet.Extension.equivProd (projectiveLiftingFactorSet k G)),
      Nat.card_prod, Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, pow_succ]
  apply HasEnoughRootsOfUnity.of_dvd k (n :=
    Nat.card G ^ (Nat.card (FactorSet G (rootsOfUnity (Nat.card G) k)) + 1))
  rw [← hcard]
  exact (Group.exponent_quotient_dvd _).trans Group.exponent_dvd_nat_card

/-- Over an algebraically closed field whose characteristic does not divide the group order,
the second-cohomology group of a finite group is the character dual of the part of the common
lifting kernel lying in the extension's commutator subgroup.
This identifies the kernel detected by all projective representations; it does not assert
that the common lifting extension itself is a stem extension. -/
noncomputable def projectiveLiftingCohomologyEquiv :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ) ≃+
      Additive (((commutator (projectiveLiftingFactorSet k G).Extension).comap
        (FactorSet.inl (projectiveLiftingFactorSet k G))) →* kˣ) := by
  exact ((AddEquiv.addSubgroupCongr (AddMonoidHom.range_eq_top.mpr
    (projectiveLiftingFactorSet_characterTransgression_surjective k G))).trans
      AddSubgroup.topEquiv).symm.trans
        ((projectiveLiftingFactorSet k G).characterTransgressionRangeEquiv
          trivialMulDistribMulAction_smul)

/-- The cohomology-duality isomorphism reads the transgression of a kernel character as
its restriction to the commutator part of the common lifting kernel. -/
@[simp↓]
theorem projectiveLiftingCohomologyEquiv_characterTransgression
    (χ : Additive (equivariantCharacterSubgroup G
      (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) kˣ)) :
    projectiveLiftingCohomologyEquiv k G
      ((projectiveLiftingFactorSet k G).characterTransgression χ) =
        (projectiveLiftingFactorSet k G).commutatorCharacterRestriction χ := by
  simp only [projectiveLiftingCohomologyEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_trans_apply]
  rw [← (projectiveLiftingFactorSet k G).characterTransgressionRangeEquiv_apply
    trivialMulDistribMulAction_smul χ]
  apply congrArg ((projectiveLiftingFactorSet k G).characterTransgressionRangeEquiv
    trivialMulDistribMulAction_smul)
  apply Subtype.ext
  simp only [AddEquiv.addSubgroupCongr_symm_apply, AddSubgroup.topEquiv_symm_apply_coe]

/-- Conversely, transgression recovers the cohomology class from the restricted kernel
character under the inverse duality isomorphism. -/
@[simp↓]
theorem projectiveLiftingCohomologyEquiv_symm_commutatorCharacterRestriction
    (χ : Additive (equivariantCharacterSubgroup G
      (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) kˣ)) :
    (projectiveLiftingCohomologyEquiv k G).symm
      ((projectiveLiftingFactorSet k G).commutatorCharacterRestriction χ) =
        (projectiveLiftingFactorSet k G).characterTransgression χ := by
  rw [← projectiveLiftingCohomologyEquiv_characterTransgression]
  exact (projectiveLiftingCohomologyEquiv k G).symm_apply_apply _

end Duality

end TauCeti
