/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.DeckGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover
public import TauCeti.GroupTheory.Automorphism.Outer

/-!
# The geometric fundamental group and the deck dictionary

Mathlib's `FundamentalGroup X x₀` multiplies loop classes by `p * q = q.trans p`
(`FundamentalGroup.mul_def`): the right factor is traversed first. The **geometric fundamental
group** `TauCeti.GeometricFundamentalGroup X x₀ = (FundamentalGroup X x₀)ᵐᵒᵖ` reverses this, so
that the class of `p.trans q` is the product of the class of `p` and the class of `q`
(`TauCeti.GeometricFundamentalGroup.mk_trans`): multiplication is first-traverse concatenation.
Inversion `(MulEquiv.inv' (FundamentalGroup X x₀)).symm`, `op g ↦ g⁻¹`, identifies it with
`FundamentalGroup X x₀`. Through it the two groups have the same automorphisms
(`MulAut.congr_inv'`: `φ` corresponds to `MulEquiv.op φ`), inner automorphisms
(`MulAut.map_congr_range_conj`) and outer automorphisms (`TauCeti.OuterAut.congr` and
`TauCeti.OuterAut.congr_symm_inv'_mk_op`).

For a path-connected, locally path-connected, semilocally simply connected space, the geometric
fundamental group is the deck group of the based-path universal cover with no further opposite:
`TauCeti.UniversalCover.geometricDeckEquiv x₀` sends the class of a loop `p` to the deck
transformation taking the base lift `basepointLift x₀` to the endpoint of the lift of `p` from it
(`TauCeti.UniversalCover.geometricDeckEquiv_mk_apply_basepointLift`). Since Tau Ceti's universal
cover is acted on by prepending the inverse loop, this deck transformation is
`UniversalCover.loopDeck x₀ p⁻¹`. Lifting `p.trans q` from the base lift ends at the image of the
base lift under the deck transformation of `q` followed by that of `p`
(`TauCeti.UniversalCover.liftPath_trans_apply_one`), which is the homomorphism law for
first-traverse concatenation.

## Main definitions

* `TauCeti.GeometricFundamentalGroup X x₀`: the opposite of the fundamental group.
* `TauCeti.GeometricFundamentalGroup.mk`: the class of a loop.
* `TauCeti.UniversalCover.geometricDeckEquiv`: the geometric fundamental group is the deck group
  of the universal cover.
* `TauCeti.UniversalCover.geometricDeckQuotientEquiv`: for a normal subgroup `N`, the quotient
  by `N` is the deck group of the cover attached to the image of `N` under inversion.

## Main results

* `TauCeti.GeometricFundamentalGroup.mk_trans`: concatenation is multiplication.
* `TauCeti.UniversalCover.geometricDeckEquiv_mk_apply_basepointLift`: the deck transformation of
  a loop sends the base lift to the endpoint of the lifted loop.
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

/-- The **geometric fundamental group** `(π₁(X, x₀))ᵐᵒᵖ`, whose multiplication is
first-traverse concatenation of loops: the class of `p.trans q` is the class of `p` times the
class of `q`. -/
abbrev GeometricFundamentalGroup (X : Type*) [TopologicalSpace X] (x₀ : X) : Type _ :=
  (FundamentalGroup X x₀)ᵐᵒᵖ

namespace GeometricFundamentalGroup

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- The class of a loop in the geometric fundamental group. -/
abbrev mk (p : Path x₀ x₀) : GeometricFundamentalGroup X x₀ :=
  op (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))

/-- Multiplication in the geometric fundamental group is first-traverse concatenation. -/
theorem mk_trans (p q : Path x₀ x₀) : mk (p.trans q) = mk p * mk q :=
  (rfl)

/-- The constant loop represents the identity. -/
@[simp]
theorem mk_refl : mk (Path.refl x₀) = 1 :=
  (rfl)

end GeometricFundamentalGroup

namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- **The deck dictionary.** The geometric fundamental group is the deck group of the based-path
universal cover: the class of a loop `p` goes to the deck transformation sending the base lift to
the endpoint of the lift of `p` (`geometricDeckEquiv_mk_apply_basepointLift`). -/
def geometricDeckEquiv :
    GeometricFundamentalGroup X x₀ ≃* deck (proj : UniversalCover x₀ → X) :=
  (deckFundamentalGroupEquiv x₀).symm

/-- The deck transformation of `op g` is the action of the inverse loop class `g⁻¹`. -/
@[simp]
theorem geometricDeckEquiv_op (g : FundamentalGroup X x₀) :
    geometricDeckEquiv x₀ (op g) = loopDeck x₀ g⁻¹ :=
  deckFundamentalGroupEquiv_symm_op x₀ g

/-- The deck transformation of `op g` sends the base lift to the endpoint of the lift of `g` from
the base lift. -/
theorem geometricDeckEquiv_op_apply_basepointLift (g : FundamentalGroup X x₀) :
    (geometricDeckEquiv x₀ (op g)).val (basepointLift x₀) =
      ((isCoveringMap x₀).monodromy g.toPath (basepointLift x₀) : UniversalCover x₀) := by
  rw [geometricDeckEquiv_op, loopDeck_apply, monodromy_basepointLift]

/-- **Endpoint formula.** The deck transformation of the class of a loop `p` sends the base lift
to the endpoint of the lift of `p` starting at the base lift. -/
theorem geometricDeckEquiv_mk_apply_basepointLift (p : Path x₀ x₀) :
    (geometricDeckEquiv x₀ (GeometricFundamentalGroup.mk p)).val (basepointLift x₀) =
      (isCoveringMap x₀).liftPath p (basepointLift x₀)
        (p.source.trans (basepointLift x₀).property.symm) 1 :=
  (geometricDeckEquiv_op_apply_basepointLift x₀ _).trans
    ((isCoveringMap x₀).coe_monodromy_mk p (basepointLift x₀))

/-- **The homomorphism law by path lifting.** The lift of `p.trans q` from the base lift ends at
the image of the base lift under the deck transformation of `q` followed by that of `p`. -/
theorem liftPath_trans_apply_one (p q : Path x₀ x₀) :
    (isCoveringMap x₀).liftPath (p.trans q) (basepointLift x₀)
        ((p.trans q).source.trans (basepointLift x₀).property.symm) 1 =
      (geometricDeckEquiv x₀ (GeometricFundamentalGroup.mk p)).val
        ((geometricDeckEquiv x₀ (GeometricFundamentalGroup.mk q)).val (basepointLift x₀)) := by
  rw [← geometricDeckEquiv_mk_apply_basepointLift, GeometricFundamentalGroup.mk_trans, map_mul]
  rfl

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

/-- The deck transformation of the class of `op g` sends the class of `e` to the class of
`g⁻¹ • e`, as `geometricDeckEquiv` does on the universal cover. -/
@[simp]
theorem geometricDeckQuotientEquiv_mk_op_apply (g : FundamentalGroup X x₀)
    (e : UniversalCover x₀) :
    (geometricDeckQuotientEquiv x₀ N (QuotientGroup.mk (op g))).val (Quotient.mk'' e) =
      Quotient.mk'' (g⁻¹ • e) := by
  rw [geometricDeckQuotientEquiv, MulEquiv.trans_apply]
  exact deckSubgroupQuotientProjEquivOfNormal_mk_apply x₀ _ g⁻¹ e

end UniversalCover

end TauCeti
