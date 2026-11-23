/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Geometric
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.DeckGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover

/-!
# The deck dictionary for the geometric fundamental group

For a path-connected, locally path-connected, semilocally simply connected space, the geometric
fundamental group `TauCeti.GeometricFundamentalGroup X x₀ = (FundamentalGroup X x₀)ᵐᵒᵖ` is the
deck group of the based-path universal cover with no further opposite: the inverse
`(TauCeti.UniversalCover.deckFundamentalGroupEquiv x₀).symm` of the monodromy identification has
type `GeometricFundamentalGroup X x₀ ≃* deck proj`. It sends the class of a loop `p` to the deck
transformation taking the base lift `basepointLift x₀` to the endpoint of the lift of `p` from it
(`TauCeti.UniversalCover.deckFundamentalGroupEquiv_symm_mk_apply_basepointLift`). Since Tau Ceti's
universal cover is acted on by prepending the inverse loop, this deck transformation is
`UniversalCover.loopDeck x₀ p⁻¹` (`TauCeti.UniversalCover.deckFundamentalGroupEquiv_symm_op`).
Lifting `p.trans q` from the base lift ends at the image of the base lift under the deck
transformation of `q` followed by that of `p` (`TauCeti.UniversalCover.liftPath_trans_apply_one`),
which is the homomorphism law for first-traverse concatenation.

## Main definitions

* `TauCeti.UniversalCover.geometricDeckQuotientEquiv`: for a normal subgroup `N`, the quotient
  by `N` is the deck group of the cover attached to the image of `N` under inversion.

## Main results

* `TauCeti.UniversalCover.deckFundamentalGroupEquiv_symm_mk_apply_basepointLift`: the deck
  transformation of a loop sends the base lift to the endpoint of the lifted loop.
* `TauCeti.UniversalCover.liftPath_trans_apply_one`: the lift of `p.trans q` from the base lift
  ends at the image of the base lift under the deck transformation of `p` after that of `q`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 1.3,
  Proposition 1.39.
* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Chapter 8.
-/

public section
noncomputable section

open MulOpposite

namespace TauCeti

namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- **Endpoint formula.** The deck transformation of the class of a loop `p` sends the base lift
to the endpoint of the lift of `p` starting at the base lift. -/
theorem deckFundamentalGroupEquiv_symm_mk_apply_basepointLift (p : Path x₀ x₀) :
    ((deckFundamentalGroupEquiv x₀).symm (GeometricFundamentalGroup.mk p)).val
        (basepointLift x₀) =
      (isCoveringMap x₀).liftPath p (basepointLift x₀)
        (p.source.trans (basepointLift x₀).property.symm) 1 := by
  rw [deckFundamentalGroupEquiv_symm_op, loopDeck_apply, ← monodromy_basepointLift]
  exact (isCoveringMap x₀).coe_monodromy_mk p (basepointLift x₀)

/-- **The homomorphism law by path lifting.** The lift of `p.trans q` from the base lift ends at
the image of the base lift under the deck transformation of `q` followed by that of `p`. -/
theorem liftPath_trans_apply_one (p q : Path x₀ x₀) :
    (isCoveringMap x₀).liftPath (p.trans q) (basepointLift x₀)
        ((p.trans q).source.trans (basepointLift x₀).property.symm) 1 =
      ((deckFundamentalGroupEquiv x₀).symm (GeometricFundamentalGroup.mk p)).val
        (((deckFundamentalGroupEquiv x₀).symm (GeometricFundamentalGroup.mk q)).val
          (basepointLift x₀)) := by
  rw [← deckFundamentalGroupEquiv_symm_mk_apply_basepointLift, GeometricFundamentalGroup.mk_trans,
    map_mul, Subgroup.coe_mul, Homeomorph.mul_apply]

variable (N : Subgroup (GeometricFundamentalGroup X x₀)) [N.Normal]
/-- For a normal subgroup `N` of the geometric fundamental group, the quotient by `N` is the deck
group of the cover attached to the image of `N` under inversion `op g ↦ g⁻¹`, written as the
preimage of `N` under the inverse isomorphism `MulEquiv.inv'`, `g ↦ op g⁻¹`. -/
def geometricDeckQuotientEquiv :
    GeometricFundamentalGroup X x₀ ⧸ N ≃*
      deck (subgroupQuotientProj x₀
        (N.comap (MulEquiv.inv' (FundamentalGroup X x₀) : FundamentalGroup X x₀ →* _))) :=
  (QuotientGroup.congr N _ (MulEquiv.inv' _).symm
    (by rw [N.map_equiv_eq_comap_symm, MulEquiv.symm_symm])).trans
    (deckSubgroupQuotientProjEquivOfNormal x₀ _)

/-- The deck transformation of the class of `op g` is that of the class of `g⁻¹` for the cover
attached to the preimage of `N`. -/
theorem geometricDeckQuotientEquiv_mk_op (g : FundamentalGroup X x₀) :
    geometricDeckQuotientEquiv x₀ N (QuotientGroup.mk (op g)) =
      deckSubgroupQuotientProjEquivOfNormal x₀ _ (QuotientGroup.mk g⁻¹) := by
  rw [geometricDeckQuotientEquiv, MulEquiv.trans_apply, QuotientGroup.congr_mk,
    MulEquiv.inv'_symm_apply, Function.comp_apply, unop_op]

/-- The deck transformation of the class of `op g` sends the class of `e` to the class of
`g⁻¹ • e`, as `(deckFundamentalGroupEquiv x₀).symm (op g)` does on the universal cover. -/
@[simp]
theorem geometricDeckQuotientEquiv_mk_op_apply (g : FundamentalGroup X x₀)
    (e : UniversalCover x₀) :
    (geometricDeckQuotientEquiv x₀ N (QuotientGroup.mk (op g))).val (Quotient.mk'' e) =
      Quotient.mk'' (g⁻¹ • e) := by
  rw [geometricDeckQuotientEquiv_mk_op, deckSubgroupQuotientProjEquivOfNormal_mk_apply]

/-- The inverse of the deck transformation of the class of `op g` sends the class of `e` to the
class of `g • e`. -/
@[simp]
theorem geometricDeckQuotientEquiv_mk_op_symm_apply (g : FundamentalGroup X x₀)
    (e : UniversalCover x₀) :
    (geometricDeckQuotientEquiv x₀ N (QuotientGroup.mk (op g))).val.symm (Quotient.mk'' e) =
      Quotient.mk'' (g • e) := by
  rw [geometricDeckQuotientEquiv_mk_op, deckSubgroupQuotientProjEquivOfNormal_mk_symm_apply,
    inv_inv]

end UniversalCover

end TauCeti
