/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.WedgeSum
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover

/-!
# Deck transformations of the universal cover of a wedge of circles

A wedge sum of locally path-connected spaces is locally path-connected, as a quotient of a disjoint
union of them (`TauCeti.WedgeSum.locallyPathConnectedSpace`). So a wedge of circles has a universal
cover, whose deck group is the opposite of its fundamental group, the free group on the circles
(`TauCeti.UniversalCover.deckFundamentalGroupEquiv`,
`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`):

`deck (proj) ≃* (FreeGroup ι)ᵐᵒᵖ`

(`TauCeti.WedgeSum.deckCircleMulEquiv`). Free groups are torsion-free
(`TauCeti.WedgeSum.isMulTorsionFree_circleFundamentalGroup`), so no deck transformation of the
universal cover of a wedge of circles other than the identity has finite order
(`TauCeti.UniversalCover.isMulTorsionFree_deck`). The generator `i` of the free group
corresponds to the deck transformation given by the inverse of the loop around the `i`-th circle
(`TauCeti.WedgeSum.deckCircleMulEquiv_symm_op_of`); more generally, the deck transformation of a
loop class `g` corresponds to the inverse of the word of `g`
(`TauCeti.WedgeSum.deckCircleMulEquiv_loopDeck`).
-/

public section

noncomputable section

namespace TauCeti.WedgeSum

universe u

variable (ι : Type u)

/-- The deck group of the universal cover of a wedge of circles is the opposite of the free group
on the circles. -/
def deckCircleMulEquiv :
    deck (UniversalCover.proj : UniversalCover (base fun _ : ι ↦ (1 : Circle)) → _) ≃*
      (FreeGroup ι)ᵐᵒᵖ :=
  (UniversalCover.deckFundamentalGroupEquiv _).trans (circleFundamentalGroupMulEquiv ι).op

variable {ι} in
/-- The deck transformation given by a loop class `g` corresponds to the inverse of the opposite of
the free-group word of `g`. -/
@[simp]
theorem deckCircleMulEquiv_loopDeck
    (g : FundamentalGroup (WedgeSum fun _ : ι ↦ (1 : Circle)) (base _)) :
    deckCircleMulEquiv ι (UniversalCover.loopDeck _ g) =
      (MulOpposite.op (circleFundamentalGroupMulEquiv ι g))⁻¹ := by
  simp [deckCircleMulEquiv]

variable {ι} in
/-- The generator `i` of the free group corresponds to the deck transformation given by the inverse
of the loop going once counterclockwise around the `i`-th circle. -/
@[simp]
theorem deckCircleMulEquiv_symm_op_of (i : ι) :
    (deckCircleMulEquiv ι).symm (MulOpposite.op (FreeGroup.of i)) =
      UniversalCover.loopDeck _
        (FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop)))⁻¹ := by
  simp [MulEquiv.symm_apply_eq]

end TauCeti.WedgeSum
