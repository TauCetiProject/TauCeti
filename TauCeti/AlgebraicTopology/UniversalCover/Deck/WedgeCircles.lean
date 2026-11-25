/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.WedgeSum
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Deck transformations of the universal cover of a wedge of circles

A wedge sum of locally path-connected spaces is locally path-connected, as a quotient of a disjoint
union of them (`TauCeti.WedgeSum.locallyPathConnectedSpace`). So a wedge of circles has a universal
cover, whose deck group is the opposite of its fundamental group, the free group on the circles
(`TauCeti.UniversalCover.deckFundamentalGroupEquiv`,
`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`):

`deck (proj) ≃* (FreeGroup ι)ᵐᵒᵖ`

(`TauCeti.WedgeSum.deckCircleMulEquiv`). Free groups are torsion-free, so no deck transformation
of the universal cover of a wedge of circles other than the identity has finite order
(`TauCeti.WedgeSum.isMulTorsionFree_deck_circle`). The generator `i` of the free group
corresponds to the deck transformation given by the inverse of the loop around the `i`-th circle
(`TauCeti.WedgeSum.deckCircleMulEquiv_symm_op_of`).
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
/-- The generator `i` of the free group corresponds to the deck transformation given by the inverse
of the loop going once counterclockwise around the `i`-th circle. -/
@[simp]
theorem deckCircleMulEquiv_symm_op_of (i : ι) :
    (deckCircleMulEquiv ι).symm (MulOpposite.op (FreeGroup.of i)) =
      UniversalCover.loopDeck _
        (FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop)))⁻¹ := by
  simp [deckCircleMulEquiv,
    (MulEquiv.symm_apply_eq _).2 (circleFundamentalGroupMulEquiv_expLoop i).symm]

/-- **The universal cover of a wedge of circles has no deck transformation of finite order** other
than the identity: its deck group is the opposite of a free group, which is torsion-free. -/
instance isMulTorsionFree_deck_circle :
    IsMulTorsionFree
      (deck (UniversalCover.proj : UniversalCover (base fun _ : ι ↦ (1 : Circle)) → _)) :=
  Function.Injective.isMulTorsionFree (deckCircleMulEquiv ι).toMonoidHom
    (deckCircleMulEquiv ι).injective

end TauCeti.WedgeSum
