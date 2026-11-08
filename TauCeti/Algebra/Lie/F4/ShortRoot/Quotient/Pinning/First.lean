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

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
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
  intro iβ a
  let iγ : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv γ, by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff γ).2 hγ⟩
  let b := f4ShortRootWeightIndexEquiv.symm (Sum.inl iγ)
  have hlift : f4ShortRootQuotientLift a = f4ModularRootVector β :=
    (f4ShortRootQuotientLift_symm_inl iβ).trans
      (congrArg f4ModularRootVector (f4SpecialIsogenyIndexEquiv_f4SpecialIsogenyIndexEquiv β))
  have hquot : f4ShortRootQuotientFirstColumn k a =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
    rw [f4ShortRootQuotientFirstColumn_eq, hlift]
    exact f4ShortRootSubspace_mkQ_lie_rootVector_of_specialMap_add
      (f4SignedSimpleRootIndex k) β γ hk hβ hγ hadd
  have hout : f4ShortRootQuotientToIdealEquiv
      (f4ShortRootSubspace.mkQ (f4ModularRootVector γ)) =
        f4ShortRootLieIdealBasis b :=
    f4ShortRootQuotientToIdealEquiv_mkQ_rootVector γ hγ
  have htargetSource : f4SignedSimpleRootIndex (isogenyReverse k) =
      f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k) := by
    exact (f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k).symm
  have hedge : f4ShortRootAdjoint
      (f4ModularRootVector
        (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)))
      (f4ShortRootLieIdealBasis a) = f4ShortRootLieIdealBasis b :=
    -- `a` and `b` are the source and target weight-basis labels.
    f4ShortRootAdjoint_rootVector_of_add_eq_short
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
  apply Subtype.ext
  simp only [coe_f4ShortRootIdealFirstColumn, coe_f4ShortRootLieIdealBasis_symm_inl,
    f4ShortRootQuotientFirstColumn_eq, f4ShortRootQuotientLift_symm_inl,
    f4Modular_lie_rootVector_opposite,
    coe_f4ShortRootQuotientToIdealEquiv_mkQ_coroot_of_long k hk,
    f4SpecialIsogenyIndexEquiv_opposite_f4SignedSimpleRootIndex, isogenyReverse_isogenyReverse]

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
  have hii := f4SpecialIsogenyIndexEquiv_f4SpecialIsogenyIndexEquiv (i : Fin 48)
  have htargetSource := f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k
  by_cases hopp : f4SpecialIsogenyIndexEquiv i = f4OppositeRootIndex (f4SignedSimpleRootIndex k)
  · obtain rfl : i = ⟨_, (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff _).2
        ((f4Length_opposite _).trans hk)⟩ :=
      Subtype.ext (hii.symm.trans (congrArg f4SpecialIsogenyIndexEquiv hopp))
    exact f4ShortRootQuotientToIdealEquiv_firstColumn_opposite_of_long k hk
  by_cases hedge : ∃ δ : Fin 48, f4Length δ = 1 ∧
      f4SimplyConnectedRootDatum.root δ = f4SimplyConnectedRootDatum.root i +
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))
  · obtain ⟨δ, hδ, hadd⟩ := hedge
    have h := f4ShortRootQuotientToIdealEquiv_firstColumn_eq_firstColumn_of_specialMap_add k
      (f4SpecialIsogenyIndexEquiv i) (f4SpecialIsogenyIndexEquiv δ) hk
      ((f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff i).2 i.property)
      ((f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff δ).2 hδ)
      (by rwa [f4SpecialIsogenyIndexEquiv_f4SpecialIsogenyIndexEquiv δ, hii])
    simpa only [hii, Subtype.coe_eta] using h
  simp only [f4ShortRootQuotientFirstColumn_eq, f4ShortRootQuotientLift_symm_inl,
    f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_no_specialMap_edge _ _ hk
      ((f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff i).2 i.property) hopp
      fun δ hδ hδeq => hedge ⟨δ, hδ, by rwa [hii] at hδeq⟩, map_zero]
  refine (f4ShortRootIdealFirstColumn_eq_zero_of_no_short_sum (isogenyReverse k) i
    (by rw [← htargetSource]; exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff _).2 hk)
    i.property (fun heq => hopp ?_) fun δ hδ hδeq =>
      hedge ⟨δ, hδ, by rwa [← htargetSource] at hδeq⟩).symm
  simpa only [heq, f4OppositeRootIndex_f4OppositeRootIndex, isogenyReverse_isogenyReverse] using
    f4SpecialIsogenyIndexEquiv_opposite_f4SignedSimpleRootIndex (isogenyReverse k)

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
  have hpair := f4_pairing_specialIsogenyIndexEquiv_eq_of_length_eq
    (f4SignedSimpleRootIndex k) (Fin.castAdd 44 j) (hk.trans hj.symm)
  rw [f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k, hs] at hpair
  simp only [f4ShortRootQuotientFirstColumn_eq, hsourceBasis,
    f4ShortRootSubspace_mkQ_lie_rootVector_simpleCoroot, map_smul,
    f4ShortRootQuotientToIdealEquiv_mkQ_rootVector _ hk]
  apply Subtype.ext
  simp only [LieSubmodule.coe_smul, coe_f4ShortRootLieIdealBasis_symm_inl,
    coe_f4ShortRootIdealFirstColumn, htargetBasis, f4Modular_lie_rootVector_simpleCoroot,
    f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex]
  exact congrArg (fun c : ℤ => -(c : ZMod 2) •
    f4ModularRootVector (f4SignedSimpleRootIndex (isogenyReverse k))) hpair.symm

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
      -- `fin_cases` leaves proof-specific `Fin 2` terms; normalize them to canonical numerals
      -- before rewriting with the coordinate lemmas.
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
