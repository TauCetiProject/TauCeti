/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Deck
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover

/-!
# Deck groups of topological branched covers of the sphere

For `X : TopBranchedCover.{u} n`, restricting deck transformations to `X.restrict` over `ℂ ∖ {0, 1}`
and composing with `IsCoveringMap.deckMulEquivAutomorphismGroup` identifies `deck X.π` with the
automorphism group of the monodromy triple (`deckMulEquivAutomorphismGroup`) and matches regularity.
-/

public noncomputable section

open Equiv Equiv.Perm Set
open scoped OnePoint

namespace TauCeti

open ThricePuncturedSphere

universe u

namespace TopBranchedCover

variable {n : ℕ} (X : TopBranchedCover.{u} n)

/-- **The deck group of a branched cover is the deck group of its unbranched part.** A deck
transformation of `π` restricts to one of `TauCeti.TopBranchedCover.restrict`, and every deck
transformation of the unbranched cover extends uniquely across the marked fibres
(`TauCeti.TopBranchedCover.Iso.ofRestrict`). -/
def deckMulEquivDeckRestrict : deck X.π ≃* deck X.restrict where
  toFun φ := ⟨(⟨φ.1, congrFun φ.2⟩ : Iso X X).restrict,
    deck.mem_iff.2 (funext (Iso.restrict_restrict _))⟩
  invFun ψ := ⟨(Iso.ofRestrict ψ.1 fun z ↦ by
      simpa using congrArg toOnePoint (deck.proj_smul ψ z)).toHomeomorph,
    deck.mem_iff.2 (funext (Iso.π_apply _))⟩
  left_inv φ := Subtype.ext <| congrArg Iso.toHomeomorph
    (Iso.restrict_injective (Iso.restrict_ofRestrict _ _) :
      Iso.ofRestrict _ _ = (⟨φ.1, congrFun φ.2⟩ : Iso X X))
  right_inv ψ := Subtype.ext (Iso.restrict_ofRestrict _ _)
  map_mul' _ _ := Subtype.ext (Homeomorph.ext fun z ↦ Subtype.ext (by simp))

/-- On the unbranched part, the restriction of a deck transformation is the deck
transformation. -/
@[simp] theorem coe_deckMulEquivDeckRestrict_apply (φ : deck X.π) (z : X.π ⁻¹' range toOnePoint) :
    ((X.deckMulEquivDeckRestrict φ : X.π ⁻¹' range toOnePoint ≃ₜ X.π ⁻¹' range toOnePoint) z :
      X.Z) = (φ : X.Z ≃ₜ X.Z) z := Iso.coe_restrict_apply _ z

/-- On the unbranched part, the extension of a deck transformation of the unbranched cover is that
deck transformation. -/
@[simp] theorem coe_deckMulEquivDeckRestrict_symm_apply (ψ : deck X.restrict)
    (z : X.π ⁻¹' range toOnePoint) :
    (X.deckMulEquivDeckRestrict.symm ψ : X.Z ≃ₜ X.Z) z =
      ((ψ : X.π ⁻¹' range toOnePoint ≃ₜ X.π ⁻¹' range toOnePoint) z : X.Z) :=
  Iso.ofRestrict_toHomeomorph_apply_val _ _ z

/-- Deck transformations of `X.π` act on every fibre of `X.restrict` via
`deckMulEquivDeckRestrict`. -/
instance instMulActionDeckRestrictFiber (b : ThricePuncturedSphere) :
    MulAction (deck X.π) (X.restrict ⁻¹' {b}) :=
  MulAction.compHom _ X.deckMulEquivDeckRestrict.toMonoidHom

/-- On underlying points of `X.Z`, the action of `deck X.π` on a fibre of `X.restrict` is
evaluation of the deck transformation. -/
@[simp] theorem coe_deck_smul_restrictFiber (b : ThricePuncturedSphere) (φ : deck X.π)
    (z : X.restrict ⁻¹' {b}) :
    ((φ • z : X.restrict ⁻¹' {b}) : X.Z) = (φ : X.Z ≃ₜ X.Z) z :=
  (congrArg Subtype.val (deck.fiber_smul_coe (X.deckMulEquivDeckRestrict φ) z)).trans
    (X.coe_deckMulEquivDeckRestrict_apply φ z)

/-- Conjugation by an isomorphism of topological branched covers identifies their deck groups. -/
def Iso.deckMulEquiv {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y) : deck X.π ≃* deck Y.π :=
  Deck.conjMulEquiv ι.toHomeomorph ι.π_apply

/-- `ι.deckMulEquiv` acts by conjugating the underlying homeomorphism by `ι.toHomeomorph`. -/
@[simp] theorem Iso.coe_deckMulEquiv_apply {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y)
    (φ : deck X.π) (y : Y.Z) :
    (ι.deckMulEquiv φ : Y.Z ≃ₜ Y.Z) y =
      ι.toHomeomorph ((φ : X.Z ≃ₜ X.Z) (ι.toHomeomorph.symm y)) :=
  Deck.conjMulEquiv_apply_coe _ _ φ y

/-- The inverse of `Iso.deckMulEquiv` conjugates by `ι.toHomeomorph.symm`. -/
@[simp] theorem Iso.coe_deckMulEquiv_symm_apply {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y)
    (ψ : deck Y.π) (x : X.Z) :
    (ι.deckMulEquiv.symm ψ : X.Z ≃ₜ X.Z) x =
      ι.toHomeomorph.symm ((ψ : Y.Z ≃ₜ Y.Z) (ι.toHomeomorph x)) :=
  Deck.conjMulEquiv_symm_apply_coe _ _ ψ x

/-- Isomorphic topological branched covers have deck groups of the same cardinality. -/
theorem Iso.natCard_deck_eq {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y) :
    Nat.card (deck X.π) = Nat.card (deck Y.π) := Nat.card_congr ι.deckMulEquiv.toEquiv

/-- A degree-`n` topological branched cover is *regular* when its deck group has order `n`. -/
def IsRegular : Prop := Nat.card (deck X.π) = n

/-- Unfold `TopBranchedCover.IsRegular` to `Nat.card (deck X.π) = n`. -/
theorem isRegular_iff {X : TopBranchedCover.{u} n} :
    X.IsRegular ↔ Nat.card (deck X.π) = n := Iff.rfl

/-- Regularity of topological branched covers is invariant under isomorphism. -/
theorem Iso.isRegular_iff {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y) :
    X.IsRegular ↔ Y.IsRegular := by simp only [TopBranchedCover.isRegular_iff, ι.natCard_deck_eq]

/-- The order of the deck group of an isomorphism class of topological branched covers. -/
def IsoClass.natCardDeck : IsoClass.{u} n → ℕ :=
  IsoClass.lift (fun X ↦ Nat.card (deck X.π)) fun _ _ ⟨ι⟩ ↦ ι.natCard_deck_eq

/-- Evaluating `IsoClass.natCardDeck` on `.mk X` gives `Nat.card (deck X.π)`. -/
@[simp] theorem IsoClass.natCardDeck_mk (X : TopBranchedCover.{u} n) :
    (IsoClass.mk X).natCardDeck = Nat.card (deck X.π) := IsoClass.lift_mk _ _ X

/-- Regularity on isomorphism classes of topological branched covers. -/
def IsoClass.IsRegular : IsoClass.{u} n → Prop :=
  IsoClass.lift TopBranchedCover.IsRegular fun _ _ ⟨ι⟩ ↦ propext ι.isRegular_iff

/-- Evaluating `IsoClass.IsRegular` on `.mk X` recovers `X.IsRegular`. -/
@[simp] theorem IsoClass.isRegular_mk (X : TopBranchedCover.{u} n) :
    (IsoClass.mk X).IsRegular ↔ X.IsRegular := of_eq (IsoClass.lift_mk _ _ X)

section Monodromy

variable (ν : X.restrict ⁻¹' {basePt} ≃ Fin n)

/-- **The deck group of `X` is the automorphism group of its monodromy triple.** -/
def deckMulEquivAutomorphismGroup :
    deck X.π ≃* (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup :=
  X.deckMulEquivDeckRestrict.trans (X.isCoveringMap_restrict.deckMulEquivAutomorphismGroup ν)

/-- `deckMulEquivAutomorphismGroup` sends `φ` to the permutation it induces on the numbered fibre
over `1/2`. -/
@[simp] theorem coe_deckMulEquivAutomorphismGroup_apply (φ : deck X.π) (i : Fin n) :
    (X.deckMulEquivAutomorphismGroup ν φ : Perm (Fin n)) i = ν (φ • ν.symm i) := by
  refine (IsCoveringMap.coe_deckMulEquivAutomorphismGroup_apply _ ν
    (X.deckMulEquivDeckRestrict φ) i).trans (congrArg ν (Subtype.ext (Subtype.ext ?_)))
  simp [deck.fiber_smul_coe]

/-- The deck transformation attached to `τ` sends the sheet labelled `i` to that labelled `τ i`. -/
@[simp] theorem deckMulEquivAutomorphismGroup_symm_smul
    (τ : (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup) (i : Fin n) :
    (X.deckMulEquivAutomorphismGroup ν).symm τ • ν.symm i = ν.symm ((τ : Perm (Fin n)) i) := by
  rw [← ν.symm_apply_apply ((X.deckMulEquivAutomorphismGroup ν).symm τ • ν.symm i),
    ← coe_deckMulEquivAutomorphismGroup_apply, MulEquiv.apply_symm_apply]

/-- `X` is regular if and only if its monodromy triple is regular. -/
theorem isRegular_iff_monodromyTriple {X : TopBranchedCover.{u} n}
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    X.IsRegular ↔ (X.isCoveringMap_restrict.monodromyTriple ν).IsRegular := by
  rw [isRegular_iff, PermutationTriple.isRegular_iff_card_automorphismGroup,
    and_iff_right (X.isCoveringMap_restrict.isConnected_monodromyTriple ν),
    Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv]

end Monodromy

end TopBranchedCover

end TauCeti
