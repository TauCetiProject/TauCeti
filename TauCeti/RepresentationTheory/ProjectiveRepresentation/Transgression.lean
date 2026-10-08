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

In characteristic zero, `projectiveLiftingCohomologyEquiv` identifies second cohomology
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

/-- In characteristic zero, the second-cohomology group of a finite group is the character
dual of the part of the common lifting kernel lying in the extension's commutator subgroup.
This identifies the kernel detected by all projective representations; it does not assert
that the common lifting extension itself is a stem extension. -/
noncomputable def projectiveLiftingCohomologyEquiv [CharZero k] :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ) ≃+
      Additive (((commutator (projectiveLiftingFactorSet k G).Extension).comap
        (FactorSet.inl (projectiveLiftingFactorSet k G))) →* kˣ) := by
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  let M := FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k
  letI : NeZero ((Monoid.exponent M : ℕ) : k) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  letI : NeZero ((Monoid.exponent
      (Abelianization (projectiveLiftingFactorSet k G).Extension) : ℕ) : k) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  exact ((AddEquiv.addSubgroupCongr (AddMonoidHom.range_eq_top.mpr
    (projectiveLiftingFactorSet_characterTransgression_surjective k G))).trans
      AddSubgroup.topEquiv).symm.trans
        ((projectiveLiftingFactorSet k G).characterTransgressionRangeEquiv
          trivialMulDistribMulAction_smul)

/-- The cohomology-duality isomorphism reads the transgression of a kernel character as
its restriction to the commutator part of the common lifting kernel. -/
@[simp↓]
theorem projectiveLiftingCohomologyEquiv_characterTransgression [CharZero k]
    (χ : Additive (equivariantCharacterSubgroup G
      (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) kˣ)) :
    projectiveLiftingCohomologyEquiv k G
      ((projectiveLiftingFactorSet k G).characterTransgression χ) =
        (projectiveLiftingFactorSet k G).commutatorCharacterRestriction χ := by
  let : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  let M := FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k
  let : NeZero ((Monoid.exponent M : ℕ) : k) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  let : NeZero ((Monoid.exponent
      (Abelianization (projectiveLiftingFactorSet k G).Extension) : ℕ) : k) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  simp only [projectiveLiftingCohomologyEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_trans_apply]
  rw [← (projectiveLiftingFactorSet k G).characterTransgressionRangeEquiv_apply
    trivialMulDistribMulAction_smul χ]
  congr 1

/-- Conversely, transgression recovers the cohomology class from the restricted kernel
character under the inverse duality isomorphism. -/
@[simp↓]
theorem projectiveLiftingCohomologyEquiv_symm_commutatorCharacterRestriction [CharZero k]
    (χ : Additive (equivariantCharacterSubgroup G
      (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) kˣ)) :
    (projectiveLiftingCohomologyEquiv k G).symm
      ((projectiveLiftingFactorSet k G).commutatorCharacterRestriction χ) =
        (projectiveLiftingFactorSet k G).characterTransgression χ := by
  rw [← projectiveLiftingCohomologyEquiv_characterTransgression]
  exact (projectiveLiftingCohomologyEquiv k G).symm_apply_apply _

end TauCeti
