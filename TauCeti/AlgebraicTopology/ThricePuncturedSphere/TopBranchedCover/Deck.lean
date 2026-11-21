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

open Equiv Equiv.Perm

namespace TauCeti

open ThricePuncturedSphere

universe u

namespace TopBranchedCover

/-- **The deck group of `X` is the automorphism group of its monodromy triple.** -/
def deckMulEquivAutomorphismGroup {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    deck X.π ≃* (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup :=
  X.deckMulEquivDeckRestrict.trans (X.isCoveringMap_restrict.deckMulEquivAutomorphismGroup ν)

/-- `deckMulEquivAutomorphismGroup` sends `φ` to the permutation it induces on the numbered fibre
over `1/2`. -/
@[simp] theorem coe_deckMulEquivAutomorphismGroup_apply {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) (φ : deck X.π) (i : Fin n) :
    (X.deckMulEquivAutomorphismGroup ν φ : Perm (Fin n)) i = ν (φ • ν.symm i) := by
  refine (IsCoveringMap.coe_deckMulEquivAutomorphismGroup_apply _ ν
    (X.deckMulEquivDeckRestrict φ) i).trans (congrArg ν (Subtype.ext (Subtype.ext ?_)))
  exact (congrArg Subtype.val (deck.fiber_smul_coe _ (ν.symm i))).trans <|
    (X.coe_deckMulEquivDeckRestrict_apply φ _).trans
      (X.coe_deck_smul_restrictFiber basePt φ (ν.symm i)).symm

/-- The deck transformation attached to `τ` sends the sheet labelled `i` to that labelled `τ i`. -/
@[simp] theorem deckMulEquivAutomorphismGroup_symm_smul {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n)
    (τ : (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup) (i : Fin n) :
    (X.deckMulEquivAutomorphismGroup ν).symm τ • ν.symm i = ν.symm ((τ : Perm (Fin n)) i) := by
  rw [← ν.symm_apply_apply ((X.deckMulEquivAutomorphismGroup ν).symm τ • ν.symm i),
    ← coe_deckMulEquivAutomorphismGroup_apply, MulEquiv.apply_symm_apply]

/-- `X` is regular if and only if its monodromy triple is regular. -/
theorem isRegular_iff_monodromyTriple {n : ℕ} {X : TopBranchedCover.{u} n}
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    X.IsRegular ↔ (X.isCoveringMap_restrict.monodromyTriple ν).IsRegular := by
  rw [isRegular_iff, PermutationTriple.isRegular_iff_card_automorphismGroup,
    and_iff_right (X.isCoveringMap_restrict.isConnected_monodromyTriple ν),
    Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv]

end TopBranchedCover

end TauCeti
