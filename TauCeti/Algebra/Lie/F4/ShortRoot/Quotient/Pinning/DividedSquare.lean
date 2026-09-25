/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Pinning.Basic

/-!
# Divided-square pinning on the modular F4 quotient

This file compares divided-square quotient columns with the reversed first-order and
second-order columns on the short-root ideal.

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

/-- On the opposite long-root coordinate, the quotient divided square is exactly the target
short-root divided-square column after reversing the signed simple-root label. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_opposite_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    let i : F4ShortRootIndex :=
      ⟨f4SpecialIsogenyIndexEquiv (f4OppositeRootIndex (f4SignedSimpleRootIndex k)), by
        exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff
            (f4OppositeRootIndex (f4SignedSimpleRootIndex k))).2 (by
              exact (f4Length_opposite _).trans hk)⟩
    let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl i)
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k a) =
      f4ShortRootIdealDividedSquareColumn (isogenyReverse k) a := by
  dsimp only
  let α := f4SignedSimpleRootIndex k
  let β := f4OppositeRootIndex (f4SignedSimpleRootIndex k)
  have hβ : f4Length β = 2 := by
    exact (f4Length_opposite _).trans hk
  have hi : f4Length (f4SpecialIsogenyIndexEquiv β) = 1 := by
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff β).2 hβ
  let i : F4ShortRootIndex := ⟨f4SpecialIsogenyIndexEquiv β, hi⟩
  let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl i)
  have hlift : f4ShortRootQuotientLift a = f4ModularRootVector β := by
    unfold f4ShortRootQuotientLift a
    rw [f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
    dsimp only [i]
    simp only [f4SpecialIsogenyIndexEquiv_apply]
    rw [f4SpecialIsogenyIndex_involutive]
  have hquot : f4ShortRootQuotientDividedSquareColumn k a =
      f4ShortRootSubspace.mkQ (f4ModularRootVector α) := by
    unfold f4ShortRootQuotientDividedSquareColumn
    rw [hlift]
    exact congrArg f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare_rootVector_opposite k)
  let j : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv α, by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff α).2 hk⟩
  let b := f4ShortRootWeightIndexEquiv.symm (Sum.inl j)
  have hout : f4ShortRootQuotientToIdealEquiv
      (f4ShortRootSubspace.mkQ (f4ModularRootVector α)) =
        f4ShortRootLieIdealBasis b := by
    have hq := f4ShortRootSubspace_mkQ_rootVector_eq_quotientBasis α hk
    calc
      _ = f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientBasis b) :=
        congrArg f4ShortRootQuotientToIdealEquiv hq
      _ = _ := f4ShortRootQuotientToIdealEquiv_basis b
  have htargetSource : f4SignedSimpleRootIndex (isogenyReverse k) =
      f4SpecialIsogenyIndexEquiv α := by
    simpa only [α] using
      (f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k).symm
  have htargetInput : f4OppositeRootIndex (f4SignedSimpleRootIndex (isogenyReverse k)) =
      f4SpecialIsogenyIndexEquiv β := by
    simpa only [β] using
      (f4SpecialIsogenyIndexEquiv_opposite_f4SignedSimpleRootIndex k).symm
  have hideal : f4ShortRootIdealDividedSquareColumn (isogenyReverse k) a =
      f4ShortRootLieIdealBasis b := by
    unfold f4ShortRootIdealDividedSquareColumn
    apply Subtype.ext
    calc
      ((f4ShortRootDividedAdjointSquare (isogenyReverse k)
          (f4ShortRootLieIdealBasis a) : f4ShortRootLieIdeal) :
          f4ModularChevalleyLieAlgebra) =
          f4ModularDividedAdjointSquare (isogenyReverse k)
            (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) :=
        (f4ModularDividedAdjointSquare_basis (isogenyReverse k) a).symm
      _ = f4ModularRootVector (f4SpecialIsogenyIndexEquiv α) := by
        -- Rewrite the ideal basis vector as its ambient root vector.
        rw [show (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) =
            f4ModularRootVector (f4SpecialIsogenyIndexEquiv β) by
              exact coe_f4ShortRootLieIdealBasis_symm_inl i,
          htargetInput.symm,
          f4ModularDividedAdjointSquare_rootVector_opposite,
          htargetSource]
      _ = (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) :=
        (coe_f4ShortRootLieIdealBasis_symm_inl j).symm
  calc
    _ = f4ShortRootQuotientToIdealEquiv
        (f4ShortRootSubspace.mkQ (f4ModularRootVector α)) :=
      congrArg f4ShortRootQuotientToIdealEquiv hquot
    _ = f4ShortRootLieIdealBasis b := hout
    _ = _ := hideal.symm

/-- For a long signed-simple source, every root-coordinate quotient divided-square column agrees
with the reversed short-root ideal divided-square column. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_rootColumn_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (i : F4ShortRootIndex) :
    let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl i)
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k a) =
      f4ShortRootIdealDividedSquareColumn (isogenyReverse k) a := by
  dsimp only
  let β := f4SpecialIsogenyIndexEquiv i
  have hβ : f4Length β = 2 := by
    dsimp only [β]
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff i).2 i.property
  have hlift : f4ShortRootQuotientLift
      (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
        f4ModularRootVector β := by
    unfold f4ShortRootQuotientLift
    rw [f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
  let iopp : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv (f4OppositeRootIndex (f4SignedSimpleRootIndex k)), by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff
          (f4OppositeRootIndex (f4SignedSimpleRootIndex k))).2 (by
            exact (f4Length_opposite _).trans hk)⟩
  by_cases hi : i = iopp
  · subst i
    exact f4ShortRootQuotientToIdealEquiv_dividedSquare_opposite_of_long k hk
  · have hβne : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k) := by
      intro h
      apply hi
      apply Subtype.ext
      dsimp only [iopp, β]
      have h' : f4SpecialIsogenyIndexEquiv i =
          f4OppositeRootIndex (f4SignedSimpleRootIndex k) := by
        simpa only [β] using h
      calc
        (i : Fin 48) = f4SpecialIsogenyIndexEquiv
            (f4SpecialIsogenyIndexEquiv i) := by
          simp only [f4SpecialIsogenyIndexEquiv_apply]
          exact (f4SpecialIsogenyIndex_involutive i).symm
        _ = f4SpecialIsogenyIndexEquiv
            (f4OppositeRootIndex (f4SignedSimpleRootIndex k)) := congrArg _ h'
    have hqzero : f4ShortRootQuotientDividedSquareColumn k
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) = 0 := by
      unfold f4ShortRootQuotientDividedSquareColumn
      rw [hlift]
      exact f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_long
        k β hk hβ hβne
    have htargetShort :
        f4Length (f4SignedSimpleRootIndex (isogenyReverse k)) = 1 := by
      rw [← f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex]
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff _).2 hk
    have htargetNe : i ≠
        f4OppositeRootIndex (f4SignedSimpleRootIndex (isogenyReverse k)) := by
      intro h
      apply hi
      apply Subtype.ext
      -- The subtype index equality is determined by its underlying root index.
      change (i : Fin 48) = f4SpecialIsogenyIndexEquiv
        (f4OppositeRootIndex (f4SignedSimpleRootIndex k))
      rw [h, f4SpecialIsogenyIndexEquiv_opposite_f4SignedSimpleRootIndex]
    have hizero : f4ShortRootIdealDividedSquareColumn (isogenyReverse k)
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) = 0 := by
      unfold f4ShortRootIdealDividedSquareColumn
      apply Subtype.ext
      calc
        ((f4ShortRootDividedAdjointSquare (isogenyReverse k)
            (f4ShortRootLieIdealBasis
              (f4ShortRootWeightIndexEquiv.symm (Sum.inl i))) :
              f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) =
            f4ModularDividedAdjointSquare (isogenyReverse k)
              (f4ShortRootLieIdealBasis
                (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) :
                  f4ModularChevalleyLieAlgebra) :=
          (f4ModularDividedAdjointSquare_basis (isogenyReverse k) _).symm
        _ = f4ModularDividedAdjointSquare (isogenyReverse k)
              (f4ModularRootVector i) := congrArg _
            (coe_f4ShortRootLieIdealBasis_symm_inl i)
        _ = 0 := f4ModularDividedAdjointSquare_rootVector_eq_zero_of_short
          (isogenyReverse k) i i.property htargetNe
        _ = ((0 : f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl
    calc
      _ = f4ShortRootQuotientToIdealEquiv 0 :=
        congrArg f4ShortRootQuotientToIdealEquiv hqzero
      _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv
      _ = _ := hizero.symm

/-- On zero-weight coordinate `12`, the quotient and ideal divided-square columns both vanish. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_twelve
    (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k 12) =
      f4ShortRootIdealDividedSquareColumn (isogenyReverse k) 12 := by
  have hqzero : f4ShortRootQuotientDividedSquareColumn k 12 = 0 := by
      unfold f4ShortRootQuotientDividedSquareColumn f4ShortRootQuotientLift
      rw [f4ModularChevalleyBasis_longRootBasisCoordinate_twelve]
      rw [f4ModularDividedAdjointSquare_simpleCoroot_eq_zero, map_zero]
  have hizero : f4ShortRootIdealDividedSquareColumn (isogenyReverse k) 12 = 0 := by
      unfold f4ShortRootIdealDividedSquareColumn
      apply Subtype.ext
      calc
        ((f4ShortRootDividedAdjointSquare (isogenyReverse k)
            (f4ShortRootLieIdealBasis 12) : f4ShortRootLieIdeal) :
            f4ModularChevalleyLieAlgebra) =
            f4ModularDividedAdjointSquare (isogenyReverse k)
              (f4ShortRootLieIdealBasis 12 : f4ModularChevalleyLieAlgebra) :=
          (f4ModularDividedAdjointSquare_basis (isogenyReverse k) 12).symm
        _ = f4ModularDividedAdjointSquare (isogenyReverse k)
              (f4ModularSimpleCoroot (Fin.cast rank_F4.symm (2 : Fin 4))) :=
          congrArg _ coe_f4ShortRootLieIdealBasis_twelve
        _ = 0 := f4ModularDividedAdjointSquare_simpleCoroot_eq_zero _ _
        _ = ((0 : f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl
  calc
    _ = f4ShortRootQuotientToIdealEquiv 0 :=
      congrArg f4ShortRootQuotientToIdealEquiv hqzero
    _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv
    _ = _ := hizero.symm

/-- On zero-weight coordinate `13`, the quotient and ideal divided-square columns both vanish. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_thirteen
    (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k 13) =
      f4ShortRootIdealDividedSquareColumn (isogenyReverse k) 13 := by
  have hqzero : f4ShortRootQuotientDividedSquareColumn k 13 = 0 := by
      unfold f4ShortRootQuotientDividedSquareColumn f4ShortRootQuotientLift
      rw [f4ModularChevalleyBasis_longRootBasisCoordinate_thirteen]
      rw [f4ModularDividedAdjointSquare_simpleCoroot_eq_zero, map_zero]
  have hizero : f4ShortRootIdealDividedSquareColumn (isogenyReverse k) 13 = 0 := by
      unfold f4ShortRootIdealDividedSquareColumn
      apply Subtype.ext
      calc
        ((f4ShortRootDividedAdjointSquare (isogenyReverse k)
            (f4ShortRootLieIdealBasis 13) : f4ShortRootLieIdeal) :
            f4ModularChevalleyLieAlgebra) =
            f4ModularDividedAdjointSquare (isogenyReverse k)
              (f4ShortRootLieIdealBasis 13 : f4ModularChevalleyLieAlgebra) :=
          (f4ModularDividedAdjointSquare_basis (isogenyReverse k) 13).symm
        _ = f4ModularDividedAdjointSquare (isogenyReverse k)
              (f4ModularSimpleCoroot (Fin.cast rank_F4.symm (3 : Fin 4))) :=
          congrArg _ coe_f4ShortRootLieIdealBasis_thirteen
        _ = 0 := f4ModularDividedAdjointSquare_simpleCoroot_eq_zero _ _
        _ = ((0 : f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl
  calc
    _ = f4ShortRootQuotientToIdealEquiv 0 :=
      congrArg f4ShortRootQuotientToIdealEquiv hqzero
    _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv
    _ = _ := hizero.symm

/-- Every long-source quotient divided-square column is the corresponding ideal divided-square
column after reversing the signed simple-root label. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (a : Fin 26) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k a) =
      f4ShortRootIdealDividedSquareColumn (isogenyReverse k) a := by
  let P : Fin 26 → Prop := fun b ↦
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k b) =
      f4ShortRootIdealDividedSquareColumn (isogenyReverse k) b
  have h : ∀ s, P (f4ShortRootWeightIndexEquiv.symm s) :=
    Sum.rec (fun i => f4ShortRootQuotientToIdealEquiv_dividedSquare_rootColumn_of_long k hk i)
    (fun j => by
      fin_cases j
      -- These two `Fin 2` cases are the central weight coordinates.
      · change P (f4ShortRootWeightIndexEquiv.symm (Sum.inr (0 : Fin 2)))
        rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_zero]
        exact f4ShortRootQuotientToIdealEquiv_dividedSquare_twelve k
      · change P (f4ShortRootWeightIndexEquiv.symm (Sum.inr (1 : Fin 2)))
        rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_one]
        exact f4ShortRootQuotientToIdealEquiv_dividedSquare_thirteen k)
  exact (congrArg P (f4ShortRootWeightIndexEquiv.symm_apply_apply a)).mp
    (h (f4ShortRootWeightIndexEquiv a))

/-- A surviving short-source quadratic quotient edge is the ordinary first-order edge for the
reversed long source on the short-root ideal. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_of_specialMap_add
    (k : Fin 4 ⊕ Fin 4) (β γ : Fin 48)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hβ : f4Length β = 2) (hγ : f4Length γ = 2)
    (hadd : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
      f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
        f4SimplyConnectedRootDatum.root
          (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))) :
    let iβ : F4ShortRootIndex :=
      ⟨f4SpecialIsogenyIndexEquiv β, by
        exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff β).2 hβ⟩
    let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl iβ)
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k a) =
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
    unfold f4ShortRootQuotientLift a
    rw [f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
    dsimp only [iβ]
    simp only [f4SpecialIsogenyIndexEquiv_apply]
    rw [f4SpecialIsogenyIndex_involutive]
  have hquot : f4ShortRootQuotientDividedSquareColumn k a =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
    unfold f4ShortRootQuotientDividedSquareColumn
    rw [hlift]
    exact f4ShortRootSubspace_mkQ_dividedSquare_rootVector_of_specialMap_add
      k β γ hk hβ hγ hadd
  have hout : f4ShortRootQuotientToIdealEquiv
      (f4ShortRootSubspace.mkQ (f4ModularRootVector γ)) =
        f4ShortRootLieIdealBasis b := by
    have hq := f4ShortRootSubspace_mkQ_rootVector_eq_quotientBasis γ hγ
    calc
      _ = f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientBasis b) :=
        congrArg f4ShortRootQuotientToIdealEquiv hq
      _ = _ := f4ShortRootQuotientToIdealEquiv_basis b
  have htargetSource : f4SignedSimpleRootIndex (isogenyReverse k) =
      f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k) :=
    (f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k).symm
  have hideal : f4ShortRootIdealFirstColumn (isogenyReverse k) a =
      f4ShortRootLieIdealBasis b := by
    unfold f4ShortRootIdealFirstColumn
    apply Subtype.ext
    have hsigned : f4SignedSimpleRootIndex (isogenyReverse k) =
        f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k) := by
      rw [htargetSource]
    have hedge : f4ShortRootAdjoint
        (f4ModularRootVector
          (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)))
        (f4ShortRootLieIdealBasis a) = f4ShortRootLieIdealBasis b := by
      -- `a` and `b` abbreviate the source and target weight-basis labels.
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
    have hbracket :
        ⁅f4ModularRootVector
            (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)),
          (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆ =
        (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) := by
      exact (coe_f4ShortRootAdjoint_apply _ _).symm.trans
        (congrArg Subtype.val hedge)
    have hsignedBracket := congrArg
      (fun δ => ⁅f4ModularRootVector δ,
        (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆) hsigned
    exact (coe_f4ShortRootSignedSimpleAdjoint_apply _ _).trans
      (hsignedBracket.trans hbracket)
  calc
    _ = f4ShortRootQuotientToIdealEquiv
        (f4ShortRootSubspace.mkQ (f4ModularRootVector γ)) :=
      congrArg f4ShortRootQuotientToIdealEquiv hquot
    _ = f4ShortRootLieIdealBasis b := hout
    _ = _ := hideal.symm

private theorem f4ShortRootIdealFirstColumn_eq_zero_of_no_short_edge
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 2)
    (hβ : f4Length β = 1)
    (hno : ∀ δ : Fin 48, f4Length δ = 1 →
      f4SimplyConnectedRootDatum.root δ ≠
        f4SimplyConnectedRootDatum.root β +
          f4SimplyConnectedRootDatum.root (f4SignedSimpleRootIndex k)) :
    f4ShortRootIdealFirstColumn k
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩)) = 0 := by
  let α := f4SignedSimpleRootIndex k
  let H := F4.cartanSubalgebra valid_F4
  have hopp : α ≠ f4OppositeRootIndex β := by
    intro heq
    have hlen := congrArg f4Length heq
    rw [hα, f4Length_opposite, hβ] at hlen
    omega
  have hsum := f4KillingRoot_add_ne_zero_of_ne_opposite α β hopp
  have hbot : rootSpace H
      ((f4KillingRoot α : H → ℚ) + (f4KillingRoot β : H → ℚ)) = ⊥ := by
    by_contra hne
    obtain ⟨δ, hδroot⟩ := exists_f4_root_eq_add_of_rootSpace_ne_bot α β hsum hne
    have hδshort : f4Length δ = 1 := by
      have hlen := f4Length_of_root_eq_add_zsmul α β δ 1
        (by simpa only [one_zsmul] using hδroot)
      rcases f4Length_eq_one_or_eq_two δ with hδ | hδ
      · exact hδ
      · -- Expand the coefficient `1` in the root-length identity.
        change f4Length δ = f4Length β + 1 * f4Length α *
          f4SimplyConnectedRootDatum.pairing β α + 1 ^ 2 * f4Length α at hlen
        rw [hα, hβ, hδ] at hlen
        norm_num at hlen
        omega
    exact hno δ hδshort hδroot
  unfold f4ShortRootIdealFirstColumn
  apply Subtype.ext
  calc
    ((f4ShortRootSignedSimpleAdjoint k
        (f4ShortRootLieIdealBasis
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩))) :
          f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) =
        ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
          (f4ShortRootLieIdealBasis
            (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩)) :
              f4ModularChevalleyLieAlgebra)⁆ :=
      coe_f4ShortRootSignedSimpleAdjoint_apply _ _
    _ = ⁅f4ModularRootVector α, f4ModularRootVector β⁆ := by
      rw [coe_f4ShortRootLieIdealBasis_symm_inl]
    _ = 0 := f4Modular_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot α β hbot
    _ = ((0 : f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl

/-- For a short signed-simple source, every root-coordinate quotient divided-square column is
the reversed long-source first-order column on the short-root ideal. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_rootColumn_of_short
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1)
    (i : F4ShortRootIndex) :
    let a := f4ShortRootWeightIndexEquiv.symm (Sum.inl i)
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k a) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) a := by
  dsimp only
  let β := f4SpecialIsogenyIndexEquiv i
  have hβ : f4Length β = 2 := by
    dsimp only [β]
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff i).2 i.property
  have hlift : f4ShortRootQuotientLift
      (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
        f4ModularRootVector β := by
    unfold f4ShortRootQuotientLift
    rw [f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
  have htargetSource : f4SignedSimpleRootIndex (isogenyReverse k) =
      f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k) :=
    (f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k).symm
  have htargetLong : f4Length (f4SignedSimpleRootIndex (isogenyReverse k)) = 2 := by
    rw [htargetSource]
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff
        (f4SignedSimpleRootIndex k)).2 hk
  by_cases hedge : ∃ δ : Fin 48, f4Length δ = 1 ∧
      f4SimplyConnectedRootDatum.root δ =
        f4SimplyConnectedRootDatum.root i +
          f4SimplyConnectedRootDatum.root
            (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))
  · obtain ⟨δ, hδ, hadd⟩ := hedge
    let γ := f4SpecialIsogenyIndexEquiv δ
    have hγ : f4Length γ = 2 := by
      dsimp only [γ]
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff δ).2 hδ
    have hmap : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
          f4SimplyConnectedRootDatum.root
            (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)) := by
      -- The local roots `γ` and `β` are images under the involutive permutation.
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
      f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_of_specialMap_add
        k β γ hk hβ hγ hmap
    dsimp only at hcomparison
    have hi : (⟨f4SpecialIsogenyIndexEquiv β, by
        exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff β).2 hβ⟩ : F4ShortRootIndex) = i := by
      apply Subtype.ext
      dsimp only [β]
      simp only [f4SpecialIsogenyIndexEquiv_apply]
      exact f4SpecialIsogenyIndex_involutive i
    simpa only [hi] using hcomparison
  · have hqzero : f4ShortRootQuotientDividedSquareColumn k
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) = 0 := by
      unfold f4ShortRootQuotientDividedSquareColumn
      rw [hlift]
      exact f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_no_specialMap_edge
        k β hk hβ (by
          intro δ hδ hδeq
          apply hedge
          refine ⟨δ, hδ, ?_⟩
          -- Unfold the local preimage `β` before applying involutivity.
          rw [show f4SpecialIsogenyIndexEquiv β = i by
            dsimp only [β]
            simp only [f4SpecialIsogenyIndexEquiv_apply]
            exact f4SpecialIsogenyIndex_involutive i] at hδeq
          exact hδeq)
    have hizero : f4ShortRootIdealFirstColumn (isogenyReverse k)
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) = 0 := by
      apply f4ShortRootIdealFirstColumn_eq_zero_of_no_short_edge
        (isogenyReverse k) i htargetLong i.property
      intro δ hδ hδeq
      apply hedge
      refine ⟨δ, hδ, ?_⟩
      simpa only [htargetSource] using hδeq
    calc
      _ = f4ShortRootQuotientToIdealEquiv 0 :=
        congrArg f4ShortRootQuotientToIdealEquiv hqzero
      _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv
      _ = _ := hizero.symm

private theorem f4ShortRootIdealFirstColumn_cartan_eq_zero_of_short
    (k : Fin 4 ⊕ Fin 4) (hk : f4Length (f4SignedSimpleRootIndex k) = 1)
    (j s : Fin 4) (a : Fin 26)
    (hj : f4Length (Fin.castAdd 44 j) = 2)
    (hs : f4SpecialIsogenyIndexEquiv (Fin.castAdd 44 j) = Fin.castAdd 44 s)
    (ha : (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm s)) :
    f4ShortRootIdealFirstColumn (isogenyReverse k) a = 0 := by
  let α := f4SignedSimpleRootIndex k
  let α' := f4SignedSimpleRootIndex (isogenyReverse k)
  have hα' : f4SpecialIsogenyIndexEquiv α = α' :=
    f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex k
  have hpair := f4Length_mul_pairing_f4SpecialIsogenyIndex α (Fin.castAdd 44 j)
  rw [hk, hj, hα', hs] at hpair
  norm_num at hpair
  have hpairzero :
      (f4SimplyConnectedRootDatum.pairing α' (Fin.castAdd 44 s) : ZMod 2) = 0 := by
    rw [f4SimplyConnectedRootDatum_pairing, f4Coroot_castAdd,
      dotProduct_single_one]
    rw [hpair]
    rw [Int.cast_mul]
    have htwo : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul]
  unfold f4ShortRootIdealFirstColumn
  apply Subtype.ext
  have hcast : Fin.cast rank_F4 (Fin.cast rank_F4.symm s) = s := by
    apply Fin.ext
    rfl
  calc
    ((f4ShortRootSignedSimpleAdjoint (isogenyReverse k)
        (f4ShortRootLieIdealBasis a) : f4ShortRootLieIdeal) :
          f4ModularChevalleyLieAlgebra) =
        ⁅f4ModularRootVector (f4SignedSimpleRootIndex (isogenyReverse k)),
          (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆ :=
      coe_f4ShortRootSignedSimpleAdjoint_apply _ _
    _ = ⁅f4ModularRootVector α',
          f4ModularSimpleCoroot (Fin.cast rank_F4.symm s)⁆ := by
      exact congrArg₂ (fun x y : f4ModularChevalleyLieAlgebra => ⁅x, y⁆)
        (congrArg f4ModularRootVector
          rfl) ha
    _ = -(f4SimplyConnectedRootDatum.pairing α' (Fin.castAdd 44 s) : ZMod 2) •
          f4ModularRootVector α' := by
      rw [← lie_skew, f4Modular_lie_simpleCoroot_rootVector, neg_smul, hcast]
    _ = 0 := by rw [hpairzero, neg_zero, zero_smul]
    _ = ((0 : f4ShortRootLieIdeal) : f4ModularChevalleyLieAlgebra) := rfl

/-- For a short source, the quadratic quotient column at coordinate `12` and the reversed
first-order ideal column both vanish. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_twelve_of_short
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k 12) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) 12 := by
  have hqzero : f4ShortRootQuotientDividedSquareColumn k 12 = 0 := by
    unfold f4ShortRootQuotientDividedSquareColumn f4ShortRootQuotientLift
    rw [f4ModularChevalleyBasis_longRootBasisCoordinate_twelve]
    rw [f4ModularDividedAdjointSquare_simpleCoroot_eq_zero, map_zero]
  have hizero : f4ShortRootIdealFirstColumn (isogenyReverse k) 12 = 0 := by
    apply f4ShortRootIdealFirstColumn_cartan_eq_zero_of_short
      k hk 1 2 12
    · rw [f4Length_castAdd, rootLength_F4]
      rfl
    · simp only [f4SpecialIsogenyIndexEquiv_apply, f4SpecialIsogenyIndex_castAdd,
        lengthPermF4_apply]
      rfl
    · exact coe_f4ShortRootLieIdealBasis_twelve
  calc
    _ = f4ShortRootQuotientToIdealEquiv 0 :=
      congrArg f4ShortRootQuotientToIdealEquiv hqzero
    _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv
    _ = _ := hizero.symm

/-- For a short source, the quadratic quotient column at coordinate `13` and the reversed
first-order ideal column both vanish. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_thirteen_of_short
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k 13) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) 13 := by
  have hqzero : f4ShortRootQuotientDividedSquareColumn k 13 = 0 := by
    unfold f4ShortRootQuotientDividedSquareColumn f4ShortRootQuotientLift
    rw [f4ModularChevalleyBasis_longRootBasisCoordinate_thirteen]
    rw [f4ModularDividedAdjointSquare_simpleCoroot_eq_zero, map_zero]
  have hizero : f4ShortRootIdealFirstColumn (isogenyReverse k) 13 = 0 := by
    apply f4ShortRootIdealFirstColumn_cartan_eq_zero_of_short
      k hk 0 3 13
    · rw [f4Length_castAdd, rootLength_F4]
      rfl
    · simp only [f4SpecialIsogenyIndexEquiv_apply, f4SpecialIsogenyIndex_castAdd,
        lengthPermF4_apply]
      rfl
    · exact coe_f4ShortRootLieIdealBasis_thirteen
  calc
    _ = f4ShortRootQuotientToIdealEquiv 0 :=
      congrArg f4ShortRootQuotientToIdealEquiv hqzero
    _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv
    _ = _ := hizero.symm

/-- Every short-source quotient divided-square column is the reversed long-source first-order
column on the short-root ideal. -/
theorem f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_of_short
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1)
    (a : Fin 26) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k a) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) a := by
  let P : Fin 26 → Prop := fun b ↦
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientDividedSquareColumn k b) =
      f4ShortRootIdealFirstColumn (isogenyReverse k) b
  have h : ∀ s, P (f4ShortRootWeightIndexEquiv.symm s) :=
    Sum.rec (fun i => f4ShortRootQuotientToIdealEquiv_dividedSquare_rootColumn_of_short k hk i)
    (fun j => by
      fin_cases j
      -- These two `Fin 2` cases are the central weight coordinates.
      · change P (f4ShortRootWeightIndexEquiv.symm (Sum.inr (0 : Fin 2)))
        rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_zero]
        exact f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_twelve_of_short k hk
      · change P (f4ShortRootWeightIndexEquiv.symm (Sum.inr (1 : Fin 2)))
        rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_one]
        exact f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_thirteen_of_short k hk)
  exact (congrArg P (f4ShortRootWeightIndexEquiv.symm_apply_apply a)).mp
    (h (f4ShortRootWeightIndexEquiv a))


end

end TauCeti.DynkinType
