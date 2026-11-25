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
(`TauCeti.WedgeSum.isMulTorsionFree_deck_circle`). For two circles this is the check of
TeichmullerGeometry §4.2 that a free-group deck transformation is never of finite order, the
torsion-freeness of the geometric group of a wedge of two circles, before any metric.
-/

public section

noncomputable section

namespace TauCeti.WedgeSum

universe u v

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)

/-- **A wedge sum of locally path-connected spaces is locally path-connected**, as a quotient of
the disjoint union of a point and the summands. -/
instance locallyPathConnectedSpace [∀ i, LocallyPathConnectedSpace (X i)] :
    LocallyPathConnectedSpace (WedgeSum x) :=
  (isQuotientMap_sumElim (x := x)).locallyPathConnectedSpace

variable (ι)

/-- The deck group of the universal cover of a wedge of circles is the opposite of the free group
on the circles. -/
def deckCircleMulEquiv :
    deck (UniversalCover.proj : UniversalCover (base fun _ : ι ↦ (1 : Circle)) → _) ≃*
      (FreeGroup ι)ᵐᵒᵖ :=
  (UniversalCover.deckFundamentalGroupEquiv _).trans (circleFundamentalGroupMulEquiv ι).op

/-- **The universal cover of a wedge of circles has no deck transformation of finite order** other
than the identity: its deck group is the opposite of a free group, which is torsion-free. -/
instance isMulTorsionFree_deck_circle :
    IsMulTorsionFree
      (deck (UniversalCover.proj : UniversalCover (base fun _ : ι ↦ (1 : Circle)) → _)) :=
  Function.Injective.isMulTorsionFree
    ((deckCircleMulEquiv ι).trans (MulEquiv.inv' (FreeGroup ι)).symm).toMonoidHom
    ((deckCircleMulEquiv ι).trans (MulEquiv.inv' (FreeGroup ι)).symm).injective

end TauCeti.WedgeSum
