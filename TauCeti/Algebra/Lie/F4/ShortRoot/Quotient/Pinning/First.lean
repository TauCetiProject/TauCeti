/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Pinning.Basic

/-!
# First-order pinning on the modular F4 quotient

This file compares the first adjoint columns of long signed-simple roots on the quotient by the
short-root ideal with the corresponding columns for the reversed short roots on the ideal.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.F4ShortRoot
open _root_.LieAlgebra
open LieModule

noncomputable section

/-- The special root permutation preserves Cartan integers between roots of equal length. -/
theorem f4_pairing_specialIsogenyIndexEquiv_eq_of_length_eq
    (α β : Fin 48) (hαβ : f4Length α = f4Length β) :
    f4SimplyConnectedRootDatum.pairing
        (f4SpecialIsogenyIndexEquiv α) (f4SpecialIsogenyIndexEquiv β) =
      f4SimplyConnectedRootDatum.pairing α β := by
  have h := f4Length_mul_pairing_f4SpecialIsogenyIndex α β
  rw [← hαβ] at h
  rcases f4Length_eq_one_or_eq_two α with hα | hα <;>
    rw [hα] at h <;> omega

/-- Evaluation of the quotient-to-ideal equivalence on a long root vector. -/
theorem f4ShortRootQuotientToIdealEquiv_mkQ_rootVector
    (γ : Fin 48) (hγ : f4Length γ = 2) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootSubspace.mkQ (f4ModularRootVector γ)) =
      f4ShortRootLieIdealBasis
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl
          ⟨f4SpecialIsogenyIndexEquiv γ, by
            exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff γ).2 hγ⟩)) := by
  let i : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv γ, by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff γ).2 hγ⟩
  have hq := f4ShortRootSubspace_mkQ_rootVector_eq_quotientBasis γ hγ
  calc
    _ = f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientBasis
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl i))) :=
      congrArg f4ShortRootQuotientToIdealEquiv hq
    _ = _ := f4ShortRootQuotientToIdealEquiv_basis _

private theorem f4ShortRootIdealFirstColumn_eq_zero_of_no_short_sum
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hβ : f4Length β = 1)
    (hopp : f4SignedSimpleRootIndex k ≠ f4OppositeRootIndex β)
    (hno : ∀ δ : Fin 48, f4Length δ = 1 →
      f4SimplyConnectedRootDatum.root δ ≠
        f4SimplyConnectedRootDatum.root β +
          f4SimplyConnectedRootDatum.root (f4SignedSimpleRootIndex k)) :
    f4ShortRootIdealFirstColumn k
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩)) = 0 := by
  let α := f4SignedSimpleRootIndex k
  let H := F4.cartanSubalgebra valid_F4
  have hsum := f4KillingRoot_add_ne_zero_of_ne_opposite α β hopp
  by_cases hbot : rootSpace H
      ((f4KillingRoot α : H → ℚ) + (f4KillingRoot β : H → ℚ)) = ⊥
  · apply Subtype.ext
    calc
      (f4ShortRootIdealFirstColumn k
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩)) :
          f4ModularChevalleyLieAlgebra) =
          ⁅f4ModularRootVector α, f4ModularRootVector β⁆ := by
        rw [coe_f4ShortRootIdealFirstColumn,
          coe_f4ShortRootLieIdealBasis_symm_inl]
      _ = 0 := f4Modular_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot α β hbot
      _ = ((0 : f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl
  · obtain ⟨δ, hδroot⟩ := exists_f4_root_eq_add_of_rootSpace_ne_bot α β hsum hbot
    have hδlong : f4Length δ = 2 := by
      rcases f4Length_eq_one_or_eq_two δ with hδ | hδ
      · exact False.elim (hno δ hδ hδroot)
      · exact hδ
    apply Subtype.ext
    calc
      (f4ShortRootIdealFirstColumn k
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩)) :
          f4ModularChevalleyLieAlgebra) =
          ⁅f4ModularRootVector α, f4ModularRootVector β⁆ := by
        rw [coe_f4ShortRootIdealFirstColumn,
          coe_f4ShortRootLieIdealBasis_symm_inl]
      _ = 0 := f4Modular_lie_rootVector_eq_zero_of_short_add_short_eq_long
        α β δ hα hβ hδlong hδroot
      _ = ((0 : f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl

/-- A surviving long-source first-order quotient edge is the matching first-order edge for the
reversed short source on the short-root ideal. -/
theorem f4ShortRootQuotientToIdealEquiv_firstColumn_eq_firstColumn_of_specialMap_add
    (k : Fin 4 ⊕ Fin 4) (β γ : Fin 48)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (hβ : f4Length β = 2) (hγ : f4Length γ = 2)
    (hadd : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
      f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
        f4SimplyConnectedRootDatum.root
          (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))) :
    let iβ : F4ShortRootIndex :=
      ⟨f4SpecialIsogenyIndexEquiv β, by
        exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff β).2 hβ⟩
    let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl iβ)
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) a := by
  dsimp only
  let iβ : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv β, by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff β).2 hβ⟩
  let iγ : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv γ, by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff γ).2 hγ⟩
  let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl iβ)
  let b := f4ShortRootWeightIndexEquiv.symm (Sum.inl iγ)
  have hlift : f4ShortRootQuotientLift a = f4ModularRootVector β := by
    rw [f4ShortRootQuotientLift_eq_basis,
      f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
    dsimp only [iβ]
    simp only [f4SpecialIsogenyIndexEquiv_apply]
    rw [f4SpecialIsogenyIndex_involutive]
  have hquot : f4ShortRootQuotientFirstColumn k a =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
    rw [f4ShortRootQuotientFirstColumn_eq, hlift]
    exact f4ShortRootSubspace_mkQ_lie_rootVector_of_specialMap_add
      (f4SignedSimpleRootIndex k) β γ hk hβ hγ hadd
  have hout : f4ShortRootQuotientToIdealEquiv
      (f4ShortRootSubspace.mkQ (f4ModularRootVector γ)) =
        f4ShortRootLieIdealBasis b := by
    have hq := f4ShortRootSubspace_mkQ_rootVector_eq_quotientBasis γ hγ
    calc
      _ = f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientBasis b) :=
        congrArg f4ShortRootQuotientToIdealEquiv hq
      _ = _ := f4ShortRootQuotientToIdealEquiv_basis b
  have htargetSource : f4SignedSimpleRootIndex (isogenyReverse k) =
      f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k) := by
    exact (f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k).symm
  have hedge : f4ShortRootAdjoint
      (f4ModularRootVector
        (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)))
      (f4ShortRootLieIdealBasis a) = f4ShortRootLieIdealBasis b := by
    change f4ShortRootAdjoint
        (f4ModularRootVector
          (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)))
        (f4ShortRootLieIdealBasis
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl iβ))) =
      f4ShortRootLieIdealBasis
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl iγ))
    exact f4ShortRootAdjoint_rootVector_of_add_eq_short
      (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))
      (f4SpecialIsogenyIndexEquiv β) (f4SpecialIsogenyIndexEquiv γ)
      iβ.property iγ.property hadd
  have hideal : f4ShortRootIdealFirstColumn (isogenyReverse k) a =
      f4ShortRootLieIdealBasis b := by
    apply Subtype.ext
    have hsignedBracket := congrArg
      (fun δ => ⁅f4ModularRootVector δ,
        (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆) htargetSource
    exact (coe_f4ShortRootIdealFirstColumn _ _).trans
      (hsignedBracket.trans ((coe_f4ShortRootAdjoint_apply _ _).symm.trans
        (congrArg Subtype.val hedge)))
  calc
    _ = f4ShortRootQuotientToIdealEquiv
        (f4ShortRootSubspace.mkQ (f4ModularRootVector γ)) :=
      congrArg f4ShortRootQuotientToIdealEquiv hquot
    _ = f4ShortRootLieIdealBasis b := hout
    _ = _ := hideal.symm

private theorem exists_f4SignedLongCoroot_quotient_ideal_coordinate
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    ∃ c : Fin 26,
      f4ShortRootSubspace.mkQ
          (f4ModularCoroot (f4SignedSimpleRootIndex k)) =
        f4ShortRootQuotientBasis c ∧
      f4ModularCoroot (f4SignedSimpleRootIndex (isogenyReverse k)) =
        (f4ShortRootLieIdealBasis c : f4ModularChevalleyLieAlgebra) := by
  have hzero : f4ShortRootSubspace.mkQ
      (f4ModularCoroot (f4SignedSimpleRootIndex (.inl 0))) =
        f4ShortRootQuotientBasis 13 := by
    exact (congrArg f4ShortRootSubspace.mkQ
      ((congrArg f4ModularCoroot (f4SignedSimpleRootIndex_inl 0)).trans
        (f4ModularCoroot_castAdd 0))).trans
      f4ShortRootQuotientBasis_thirteen.symm
  have hone : f4ShortRootSubspace.mkQ
      (f4ModularCoroot (f4SignedSimpleRootIndex (.inl 1))) =
        f4ShortRootQuotientBasis 12 := by
    exact (congrArg f4ShortRootSubspace.mkQ
      ((congrArg f4ModularCoroot (f4SignedSimpleRootIndex_inl 1)).trans
        (f4ModularCoroot_castAdd 1))).trans
      f4ShortRootQuotientBasis_twelve.symm
  rcases k with ⟨j⟩ | ⟨j⟩ <;> fin_cases j
  · exact ⟨13, hzero,
      (coe_f4ShortRootLieIdealBasis_thirteen.trans (by
        simp only [isogenyReverse, Sum.map_inl, Fin.revPerm_apply, Fin.rev,
          f4SignedSimpleRootIndex_inl, f4ModularCoroot_castAdd]
        rfl)).symm⟩
  · exact ⟨12, hone,
      (coe_f4ShortRootLieIdealBasis_twelve.trans (by
        simp only [isogenyReverse, Sum.map_inl, Fin.revPerm_apply, Fin.rev,
          f4SignedSimpleRootIndex_inl, f4ModularCoroot_castAdd]
        rfl)).symm⟩
  · rw [f4SignedSimpleRootIndex_inl, f4Length_def] at hk
    contradiction
  · rw [f4SignedSimpleRootIndex_inl, f4Length_def] at hk
    contradiction
  · exact ⟨13,
      (congrArg f4ShortRootSubspace.mkQ
        (by simp)).trans hzero,
      (coe_f4ShortRootLieIdealBasis_thirteen.trans (by
        simp only [isogenyReverse, Sum.map_inr, Fin.revPerm_apply, Fin.rev,
          f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_castAdd, f4ModularCoroot_addNat_castAdd]
        rfl)).symm⟩
  · exact ⟨12,
      (congrArg f4ShortRootSubspace.mkQ
        (by simp)).trans hone,
      (coe_f4ShortRootLieIdealBasis_twelve.trans (by
        simp only [isogenyReverse, Sum.map_inr, Fin.revPerm_apply, Fin.rev,
          f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_castAdd, f4ModularCoroot_addNat_castAdd]
        rfl)).symm⟩
  · rw [f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_castAdd, f4Length_def] at hk
    contradiction
  · rw [f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_castAdd, f4Length_def] at hk
    contradiction

private theorem coe_f4ShortRootQuotientToIdealEquiv_mkQ_coroot_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    (f4ShortRootQuotientToIdealEquiv
        (f4ShortRootSubspace.mkQ
          (f4ModularCoroot (f4SignedSimpleRootIndex k))) :
        f4ModularChevalleyLieAlgebra) =
      f4ModularCoroot (f4SignedSimpleRootIndex (isogenyReverse k)) := by
  let hex := exists_f4SignedLongCoroot_quotient_ideal_coordinate k hk
  let c : Fin 26 := Classical.choose hex
  have hquot := (Classical.choose_spec hex).1
  have hideal := (Classical.choose_spec hex).2
  calc
    _ = (f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientBasis c) :
        f4ModularChevalleyLieAlgebra) := congrArg
      (fun x => (f4ShortRootQuotientToIdealEquiv x :
        f4ModularChevalleyLieAlgebra)) hquot
    _ = (f4ShortRootLieIdealBasis c : f4ModularChevalleyLieAlgebra) :=
      congrArg Subtype.val (f4ShortRootQuotientToIdealEquiv_basis c)
    _ = _ := hideal.symm

/-- On the opposite long-root coordinate, the first-order quotient column agrees with the
opposite-root column for the reversed short source. -/
theorem f4ShortRootQuotientToIdealEquiv_firstColumn_opposite_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    let i : F4ShortRootIndex :=
      ⟨f4SpecialIsogenyIndexEquiv (f4OppositeRootIndex (f4SignedSimpleRootIndex k)), by
        exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff
            (f4OppositeRootIndex (f4SignedSimpleRootIndex k))).2 (by
              rw [f4Length_opposite, hk])⟩
    let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl i)
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) a := by
  dsimp only
  let α := f4SignedSimpleRootIndex k
  let β := f4OppositeRootIndex (f4SignedSimpleRootIndex k)
  have hβ : f4Length β = 2 := by
    dsimp only [β]
    rw [f4Length_opposite, hk]
  let i : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv β, by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff β).2 hβ⟩
  let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl i)
  have hlift : f4ShortRootQuotientLift a = f4ModularRootVector β := by
    rw [f4ShortRootQuotientLift_eq_basis,
      f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
    dsimp only [i, β]
    simp only [f4SpecialIsogenyIndexEquiv_apply]
    rw [f4SpecialIsogenyIndex_involutive]
  have hquot : f4ShortRootQuotientFirstColumn k a =
      f4ShortRootSubspace.mkQ (f4ModularCoroot α) := by
    rw [f4ShortRootQuotientFirstColumn_eq, hlift,
      show β = f4OppositeRootIndex α from rfl]
    exact congrArg f4ShortRootSubspace.mkQ (f4Modular_lie_rootVector_opposite α)
  let α' := f4SignedSimpleRootIndex (isogenyReverse k)
  have hα'short : f4Length α' = 1 := by
    have hα'eq : α' = f4SpecialIsogenyIndexEquiv α :=
      (f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k).symm
    rw [hα'eq]
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff α).2 hk
  have hinput : (i : Fin 48) = f4OppositeRootIndex α' := by
    change f4SpecialIsogenyIndexEquiv β = f4OppositeRootIndex α'
    rw [show β = f4OppositeRootIndex (f4SignedSimpleRootIndex k) by rfl,
      f4SpecialIsogenyIndexEquiv_opposite_f4SignedSimpleRootIndex]
  apply Subtype.ext
  calc
    (f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a) :
        f4ModularChevalleyLieAlgebra) =
        (f4ShortRootQuotientToIdealEquiv
          (f4ShortRootSubspace.mkQ (f4ModularCoroot α)) :
            f4ModularChevalleyLieAlgebra) := congrArg
      (fun x => (f4ShortRootQuotientToIdealEquiv x :
        f4ModularChevalleyLieAlgebra)) hquot
    _ = f4ModularCoroot α' :=
      coe_f4ShortRootQuotientToIdealEquiv_mkQ_coroot_of_long k hk
    _ = ⁅f4ModularRootVector α',
          f4ModularRootVector (f4OppositeRootIndex α')⁆ :=
      (f4Modular_lie_rootVector_opposite α').symm
    _ = ⁅f4ModularRootVector α',
          (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆ := by
      exact congrArg (fun x : f4ModularChevalleyLieAlgebra =>
        ⁅f4ModularRootVector α', x⁆)
        ((coe_f4ShortRootLieIdealBasis_symm_inl i).trans
          (congrArg f4ModularRootVector hinput)).symm
    _ = (f4ShortRootIdealFirstColumn (isogenyReverse k) a :
          f4ModularChevalleyLieAlgebra) :=
      (coe_f4ShortRootIdealFirstColumn _ _).symm

/-- For a long signed-simple source, every root-coordinate quotient first-order column agrees
with the reversed short-source first-order column on the short-root ideal. -/
theorem f4ShortRootQuotientToIdealEquiv_firstColumn_rootColumn_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (i : F4ShortRootIndex) :
    let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl i)
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) a := by
  dsimp only
  let α := f4SignedSimpleRootIndex k
  let β := f4SpecialIsogenyIndexEquiv i
  have hβ : f4Length β = 2 := by
    dsimp only [β]
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff i).2 i.property
  have hlift : f4ShortRootQuotientLift
      (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
        f4ModularRootVector β := by
    rw [f4ShortRootQuotientLift_eq_basis,
      f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
  have htargetSource : f4SignedSimpleRootIndex (isogenyReverse k) =
      f4SpecialIsogenyIndexEquiv α :=
    (f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k).symm
  have htargetShort :
      f4Length (f4SignedSimpleRootIndex (isogenyReverse k)) = 1 := by
    rw [htargetSource]
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff α).2 hk
  by_cases hopp : β = f4OppositeRootIndex (f4SignedSimpleRootIndex k)
  · have hi : i = ⟨f4SpecialIsogenyIndexEquiv
        (f4OppositeRootIndex (f4SignedSimpleRootIndex k)), by
          exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff
              (f4OppositeRootIndex (f4SignedSimpleRootIndex k))).2 (by
                rw [f4Length_opposite, hk])⟩ := by
      apply Subtype.ext
      change (i : Fin 48) =
        f4SpecialIsogenyIndexEquiv (f4OppositeRootIndex (f4SignedSimpleRootIndex k))
      calc
        (i : Fin 48) = f4SpecialIsogenyIndexEquiv β := by
          simp only [β, f4SpecialIsogenyIndexEquiv_apply]
          exact (f4SpecialIsogenyIndex_involutive i).symm
        _ = _ := congrArg f4SpecialIsogenyIndexEquiv hopp
    subst i
    exact f4ShortRootQuotientToIdealEquiv_firstColumn_opposite_of_long k hk
  · have hnopp : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k) := hopp
    by_cases hedge : ∃ δ : Fin 48, f4Length δ = 1 ∧
        f4SimplyConnectedRootDatum.root δ =
          f4SimplyConnectedRootDatum.root i +
            f4SimplyConnectedRootDatum.root
              (f4SpecialIsogenyIndexEquiv α)
    · obtain ⟨δ, hδ, hadd⟩ := hedge
      let γ := f4SpecialIsogenyIndexEquiv δ
      have hγ : f4Length γ = 2 := by
        dsimp only [γ]
        exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff δ).2 hδ
      have hmap : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
          f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
            f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv α) := by
        rw [show f4SpecialIsogenyIndexEquiv γ = δ by
            dsimp only [γ]
            simp only [f4SpecialIsogenyIndexEquiv_apply]
            exact f4SpecialIsogenyIndex_involutive δ,
          show f4SpecialIsogenyIndexEquiv β = i by
            dsimp only [β]
            simp only [f4SpecialIsogenyIndexEquiv_apply]
            exact f4SpecialIsogenyIndex_involutive i]
        exact hadd
      have hcomparison :=
        f4ShortRootQuotientToIdealEquiv_firstColumn_eq_firstColumn_of_specialMap_add
          k β γ hk hβ hγ hmap
      dsimp only at hcomparison
      have hi : (⟨f4SpecialIsogenyIndexEquiv β, by
          exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff β).2 hβ⟩ :
            F4ShortRootIndex) = i := by
        apply Subtype.ext
        dsimp only [β]
        simp only [f4SpecialIsogenyIndexEquiv_apply]
        exact f4SpecialIsogenyIndex_involutive i
      simpa only [hi] using hcomparison
    · have hqzero : f4ShortRootQuotientFirstColumn k
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) = 0 := by
        rw [f4ShortRootQuotientFirstColumn_eq, hlift]
        apply f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_no_specialMap_edge
          α β hk hβ
        · intro heq
          exact hnopp heq
        · intro δ hδ hδeq
          apply hedge
          refine ⟨δ, hδ, ?_⟩
          rw [show f4SpecialIsogenyIndexEquiv β = i by
            dsimp only [β]
            simp only [f4SpecialIsogenyIndexEquiv_apply]
            exact f4SpecialIsogenyIndex_involutive i] at hδeq
          exact hδeq
      have htargetNe : f4SignedSimpleRootIndex (isogenyReverse k) ≠
          f4OppositeRootIndex i := by
        intro heq
        apply hnopp
        have hi : (i : Fin 48) =
            f4OppositeRootIndex (f4SignedSimpleRootIndex (isogenyReverse k)) := by
          calc
            (i : Fin 48) = f4OppositeRootIndex (f4OppositeRootIndex i) :=
              (f4OppositeRootIndex_f4OppositeRootIndex i).symm
            _ = f4OppositeRootIndex
                (f4SignedSimpleRootIndex (isogenyReverse k)) :=
              congrArg f4OppositeRootIndex heq.symm
        dsimp only [β]
        rw [hi, f4SpecialIsogenyIndexEquiv_opposite_f4SignedSimpleRootIndex,
          isogenyReverse_isogenyReverse]
      have hizero : f4ShortRootIdealFirstColumn (isogenyReverse k)
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) = 0 := by
        apply f4ShortRootIdealFirstColumn_eq_zero_of_no_short_sum
          (isogenyReverse k) i htargetShort i.property htargetNe
        intro δ hδ hδeq
        apply hedge
        refine ⟨δ, hδ, ?_⟩
        simpa only [htargetSource] using hδeq
      calc
        _ = f4ShortRootQuotientToIdealEquiv 0 :=
          congrArg f4ShortRootQuotientToIdealEquiv hqzero
        _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv
        _ = _ := hizero.symm

private theorem f4ShortRootQuotientToIdealEquiv_firstColumn_cartan_of_long
    (k : Fin 4 ⊕ Fin 4) (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (j s : Fin 4) (a : Fin 26)
    (hj : f4Length (Fin.castAdd 44 j) = 2)
    (hs : f4SpecialIsogenyIndexEquiv (Fin.castAdd 44 j) = Fin.castAdd 44 s)
    (hsourceBasis : f4ShortRootQuotientLift a =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm j))
    (htargetBasis : (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm s)) :
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) a := by
  let α := f4SignedSimpleRootIndex k
  let α' := f4SignedSimpleRootIndex (isogenyReverse k)
  have hα' : f4SpecialIsogenyIndexEquiv α = α' :=
    f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k
  have hα'short : f4Length α' = 1 := by
    rw [← hα']
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff α).2 hk
  let iα : F4ShortRootIndex := ⟨f4SpecialIsogenyIndexEquiv α, by
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff α).2 hk⟩
  let b := f4ShortRootWeightIndexEquiv.symm (Sum.inl iα)
  have hpair := f4_pairing_specialIsogenyIndexEquiv_eq_of_length_eq
    α (Fin.castAdd 44 j) (hk.trans hj.symm)
  rw [hα', hs] at hpair
  have hsource : f4ShortRootQuotientToIdealEquiv
      (f4ShortRootQuotientFirstColumn k a) =
        -(f4SimplyConnectedRootDatum.pairing α (Fin.castAdd 44 j) : ZMod 2) •
          f4ShortRootLieIdealBasis b := by
    have hcolumn : f4ShortRootQuotientFirstColumn k a =
        -(f4SimplyConnectedRootDatum.pairing α
          (Fin.castAdd 44 j) : ZMod 2) •
            f4ShortRootSubspace.mkQ (f4ModularRootVector α) := by
      calc
        _ = f4ShortRootSubspace.mkQ
            ⁅f4ModularRootVector α, f4ShortRootQuotientLift a⁆ :=
          f4ShortRootQuotientFirstColumn_eq k a
        _ = f4ShortRootSubspace.mkQ
            ⁅f4ModularRootVector α,
              f4ModularSimpleCoroot (Fin.cast rank_F4.symm j)⁆ :=
          congrArg (fun x : f4ModularChevalleyLieAlgebra =>
            f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, x⁆) hsourceBasis
        _ = _ := f4ShortRootSubspace_mkQ_lie_rootVector_simpleCoroot α _
    have hroot := f4ShortRootQuotientToIdealEquiv_mkQ_rootVector α hk
    calc
      _ = f4ShortRootQuotientToIdealEquiv
          (-(f4SimplyConnectedRootDatum.pairing α
            (Fin.castAdd 44 j) : ZMod 2) •
              f4ShortRootSubspace.mkQ (f4ModularRootVector α)) :=
        congrArg f4ShortRootQuotientToIdealEquiv hcolumn
      _ = -(f4SimplyConnectedRootDatum.pairing α
            (Fin.castAdd 44 j) : ZMod 2) •
          f4ShortRootQuotientToIdealEquiv
            (f4ShortRootSubspace.mkQ (f4ModularRootVector α)) :=
        map_smul f4ShortRootQuotientToIdealEquiv _ _
      _ = _ := by
        simpa only [iα, b] using congrArg
          (fun x => -(f4SimplyConnectedRootDatum.pairing α
            (Fin.castAdd 44 j) : ZMod 2) • x) hroot
  have htarget : f4ShortRootIdealFirstColumn (isogenyReverse k) a =
      -(f4SimplyConnectedRootDatum.pairing α' (Fin.castAdd 44 s) : ZMod 2) •
        f4ShortRootLieIdealBasis b := by
    apply Subtype.ext
    have hcast : Fin.cast rank_F4 (Fin.cast rank_F4.symm s) = s := by
      apply Fin.ext
      rfl
    calc
      (f4ShortRootIdealFirstColumn (isogenyReverse k) a :
          f4ModularChevalleyLieAlgebra) =
          ⁅f4ModularRootVector α',
            (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆ :=
        coe_f4ShortRootIdealFirstColumn _ _
      _ = ⁅f4ModularRootVector α',
            f4ModularSimpleCoroot (Fin.cast rank_F4.symm s)⁆ :=
        congrArg (fun x : f4ModularChevalleyLieAlgebra =>
          ⁅f4ModularRootVector α', x⁆) htargetBasis
      _ = -(f4SimplyConnectedRootDatum.pairing α'
            (Fin.castAdd 44 s) : ZMod 2) • f4ModularRootVector α' := by
        rw [← lie_skew, f4Modular_lie_simpleCoroot_rootVector, neg_smul, hcast]
      _ = -(f4SimplyConnectedRootDatum.pairing α'
            (Fin.castAdd 44 s) : ZMod 2) •
          (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) := by
        apply congrArg (fun x : f4ModularChevalleyLieAlgebra =>
          -(f4SimplyConnectedRootDatum.pairing α'
            (Fin.castAdd 44 s) : ZMod 2) • x)
        change f4ModularRootVector α' =
          (f4ShortRootLieIdealBasis
            (f4ShortRootWeightIndexEquiv.symm (Sum.inl iα)) :
              f4ModularChevalleyLieAlgebra)
        rw [coe_f4ShortRootLieIdealBasis_symm_inl]
        exact congrArg f4ModularRootVector hα'.symm
      _ = ((-(f4SimplyConnectedRootDatum.pairing α'
            (Fin.castAdd 44 s) : ZMod 2) • f4ShortRootLieIdealBasis b :
          f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl
  have hpairMod :
      (f4SimplyConnectedRootDatum.pairing α' (Fin.castAdd 44 s) : ZMod 2) =
        (f4SimplyConnectedRootDatum.pairing α (Fin.castAdd 44 j) : ZMod 2) :=
    congrArg (Int.cast : ℤ → ZMod 2) hpair
  calc
    _ = -(f4SimplyConnectedRootDatum.pairing α
          (Fin.castAdd 44 j) : ZMod 2) • f4ShortRootLieIdealBasis b := hsource
    _ = -(f4SimplyConnectedRootDatum.pairing α'
          (Fin.castAdd 44 s) : ZMod 2) • f4ShortRootLieIdealBasis b := by
      exact congrArg (fun c : ZMod 2 => -c • f4ShortRootLieIdealBasis b)
        hpairMod.symm
    _ = _ := htarget.symm

/-- A long source has matching first-order quotient and ideal columns at coordinate `12`. -/
theorem f4ShortRootQuotientToIdealEquiv_firstColumn_twelve_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k 12) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) 12 := by
  apply f4ShortRootQuotientToIdealEquiv_firstColumn_cartan_of_long
    k hk 1 2 12
  · rw [f4Length_castAdd, rootLength_F4]
    rfl
  · simp only [f4SpecialIsogenyIndexEquiv_apply, f4SpecialIsogenyIndex_castAdd,
      lengthPermF4_apply]
    rfl
  · rw [f4ShortRootQuotientLift_eq_basis]
    exact f4ModularChevalleyBasis_longRootBasisCoordinate_twelve
  · exact coe_f4ShortRootLieIdealBasis_twelve

/-- A long source has matching first-order quotient and ideal columns at coordinate `13`. -/
theorem f4ShortRootQuotientToIdealEquiv_firstColumn_thirteen_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k 13) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) 13 := by
  apply f4ShortRootQuotientToIdealEquiv_firstColumn_cartan_of_long
    k hk 0 3 13
  · rw [f4Length_castAdd, rootLength_F4]
    rfl
  · simp only [f4SpecialIsogenyIndexEquiv_apply, f4SpecialIsogenyIndex_castAdd,
      lengthPermF4_apply]
    rfl
  · rw [f4ShortRootQuotientLift_eq_basis]
    exact f4ModularChevalleyBasis_longRootBasisCoordinate_thirteen
  · exact coe_f4ShortRootLieIdealBasis_thirteen

/-- Every long-source quotient first-order column is the matching first-order column for the
reversed short source on the short-root ideal. -/
theorem f4ShortRootQuotientToIdealEquiv_firstColumn_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (a : Fin 26) :
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) a := by
  let P : Fin 26 → Prop := fun b ↦
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k b) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) b
  have h : ∀ s, P (f4ShortRootWeightIndexEquiv.symm s) :=
    Sum.rec (fun i => f4ShortRootQuotientToIdealEquiv_firstColumn_rootColumn_of_long k hk i)
    (fun j => by
      fin_cases j
      · change P (f4ShortRootWeightIndexEquiv.symm (Sum.inr (0 : Fin 2)))
        rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_zero]
        exact f4ShortRootQuotientToIdealEquiv_firstColumn_twelve_of_long k hk
      · change P (f4ShortRootWeightIndexEquiv.symm (Sum.inr (1 : Fin 2)))
        rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_one]
        exact f4ShortRootQuotientToIdealEquiv_firstColumn_thirteen_of_long k hk)
  exact (congrArg P (f4ShortRootWeightIndexEquiv.symm_apply_apply a)).mp
    (h (f4ShortRootWeightIndexEquiv a))


end

end TauCeti.DynkinType
