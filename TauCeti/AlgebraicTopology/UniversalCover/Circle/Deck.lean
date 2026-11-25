/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.AddCircle
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover
public import TauCeti.Topology.Instances.AddCircle.LocallyPathConnected

/-!
# The deck transformations of the universal cover of a circle

For a real period `p`, the covering `(↑) : ℝ → AddCircle p` has a simply connected,
locally path-connected total space, and `AddCircle p` is locally path-connected and semilocally
simply connected (`AddCircle.instLocallyPathConnectedSpaceReal`,
`AddCircle.instSemilocallySimplyConnectedSpaceReal`). So Tau Ceti's based-path universal cover
`TauCeti.UniversalCover (0 : AddCircle p)` exists, and by the classification of pointed covers
(`IsCoveringMap.totalSpaceHomeomorphOfRangeEq`, both recovered subgroups being trivial by
`TauCeti.FundamentalGroup.mapOfEq_range_eq_of_subsingleton`) it is identified with `ℝ` over the
circle, the base lift going to `0` (`AddCircle.universalCoverHomeomorph`).

Under this identification the deck dictionary
`η = (TauCeti.UniversalCover.deckFundamentalGroupEquiv 0).symm` of the geometric fundamental group
sends the class of the loop `t ↦ t p` (`AddCircle.periodLoop`, defined with the fundamental group
of the circle) to translation by `p`
(`AddCircle.universalCoverHomeomorph_deck_periodLoop`): the deck transformation of the class of a
loop sends the base lift to the endpoint of the lift of the loop
(`TauCeti.UniversalCover.deckFundamentalGroupEquiv_symm_mk_apply_basepointLift`), the lift of
`t ↦ t p` to `ℝ` from `0` ends at `p`, and a deck transformation of `ℝ → AddCircle p` is
determined by its value at `0` (`deck.addCircleCoe_eq_add_apply_zero`). The fundamental-group
action convention, `TauCeti.UniversalCover.loopDeck`, gives the inverse translation by `-p`
(`AddCircle.universalCoverHomeomorph_loopDeck_periodLoop`).

For `p ≠ 0` the class of `AddCircle.periodLoop` is the generator `1` of
`π₁(AddCircle p, 0) ≃* Multiplicative ℤ`
(`AddCircle.fundamentalGroupMulEquivZero_fromPath_periodLoop`).
So for `p = 1` the deck transformation of the generator is the unit translation of `ℝ` in the
direction of the loop, and the opposite convention gives the inverse translation.
-/

public section

noncomputable section

open TauCeti TauCeti.UniversalCover unitInterval

namespace AddCircle

variable (p : ℝ)

/-- **The universal cover of a circle is `ℝ`.** The homeomorphism over `AddCircle p` from Tau Ceti's
based-path universal cover at `0` to `ℝ` sending the base lift to `0`: the comparison
homeomorphism `IsCoveringMap.totalSpaceHomeomorphOfRangeEq` of these two simply connected covers. -/
def universalCoverHomeomorph : UniversalCover (0 : AddCircle p) ≃ₜ ℝ :=
  IsCoveringMap.totalSpaceHomeomorphOfRangeEq (UniversalCover.isCoveringMap 0)
    (isCoveringMap_coe p) (proj_basepointLift 0) (QuotientAddGroup.mk_zero _)
    (FundamentalGroup.mapOfEq_range_eq_of_subsingleton ..)

/-- `AddCircle.universalCoverHomeomorph` sends the base lift to `0`. -/
-- Not a `simp` lemma: `simp` unfolds `basepointLift`, so the left-hand side is not in simp-normal
-- form.
theorem universalCoverHomeomorph_basepointLift :
    universalCoverHomeomorph p (basepointLift (0 : AddCircle p)) = 0 :=
  IsCoveringMap.totalSpaceHomeomorphOfRangeEq_apply_basepoint ..

/-- `AddCircle.universalCoverHomeomorph` sends the class of the constant path to `0`. -/
@[simp]
theorem universalCoverHomeomorph_mk_refl :
    universalCoverHomeomorph p (UniversalCover.mk 0 (Path.Homotopic.Quotient.refl 0)) = 0 := by
  rw [← basepointLift_coe]
  exact universalCoverHomeomorph_basepointLift p

/-- The inverse of `AddCircle.universalCoverHomeomorph` sends `0` to the class of the constant
path. -/
@[simp]
theorem universalCoverHomeomorph_symm_zero :
    (universalCoverHomeomorph p).symm 0 = UniversalCover.mk 0 (Path.Homotopic.Quotient.refl 0) :=
  (Homeomorph.symm_apply_eq _).2 (universalCoverHomeomorph_mk_refl p).symm

/-- `AddCircle.universalCoverHomeomorph` lies over the circle. -/
@[simp]
theorem coe_universalCoverHomeomorph (u : UniversalCover (0 : AddCircle p)) :
    (universalCoverHomeomorph p u : AddCircle p) = proj u :=
  IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq_apply ..

/-- The inverse of `AddCircle.universalCoverHomeomorph` lies over the circle. -/
@[simp]
theorem proj_universalCoverHomeomorph_symm (r : ℝ) :
    proj ((universalCoverHomeomorph p).symm r) = (r : AddCircle p) :=
  IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq_symm_apply ..

/-- **The deck transformation of the period loop is translation by the period.** Read on `ℝ`
through `AddCircle.universalCoverHomeomorph`, the deck transformation attached by
`(deckFundamentalGroupEquiv 0).symm` to the class of `t ↦ t p` in the geometric fundamental group
is `r ↦ r + p`. -/
theorem universalCoverHomeomorph_deck_periodLoop (u : UniversalCover (0 : AddCircle p)) :
    universalCoverHomeomorph p
        (((deckFundamentalGroupEquiv (0 : AddCircle p)).symm
          (GeometricFundamentalGroup.mk (periodLoop p))).val u) =
      universalCoverHomeomorph p u + p := by
  set e := universalCoverHomeomorph p
  set η := (deckFundamentalGroupEquiv (0 : AddCircle p)).symm
    (GeometricFundamentalGroup.mk (periodLoop p))
  let ψ := IsCoveringMap.deckMulEquivOfRangeEq (UniversalCover.isCoveringMap 0)
    (isCoveringMap_coe p) (proj_basepointLift 0) (QuotientAddGroup.mk_zero _)
    (FundamentalGroup.mapOfEq_range_eq_of_subsingleton ..) η
  have hψ (r : ℝ) : ψ.val r = e (η.val (e.symm r)) :=
    IsCoveringMap.deckMulEquivOfRangeEq_apply_coe ..
  -- The lift of the loop from the base lift, carried to `ℝ`, is `t ↦ t p`.
  have hlift : e ∘ (UniversalCover.isCoveringMap (0 : AddCircle p)).liftPath (periodLoop p)
      (basepointLift (0 : AddCircle p))
      ((periodLoop p).source.trans (basepointLift (0 : AddCircle p)).property.symm) =
      fun t : I ↦ (t : ℝ) * p := by
    refine (isCoveringMap_coe p).eq_of_comp_eq
      (e.continuous.comp (ContinuousMap.continuous _)) (by fun_prop) ?_ 0 ?_
    · funext t
      simpa [e] using congrFun ((UniversalCover.isCoveringMap (0 : AddCircle p)).liftPath_lifts
        (periodLoop p) (basepointLift (0 : AddCircle p)).val
        ((periodLoop p).source.trans (basepointLift (0 : AddCircle p)).property.symm)) t
    · rw [Function.comp_apply, IsCoveringMap.liftPath_zero, Set.Icc.coe_zero, zero_mul]
      exact universalCoverHomeomorph_basepointLift p
  have h0 : ψ.val 0 = p := by
    rw [hψ, ← universalCoverHomeomorph_basepointLift p, Homeomorph.symm_apply_apply,
      deckFundamentalGroupEquiv_symm_mk_apply_basepointLift]
    simpa using congrFun hlift 1
  have := deck.addCircleCoe_eq_add_apply_zero ψ (e u)
  rw [h0, hψ, Homeomorph.symm_apply_apply] at this
  exact this

/-- **The opposite convention gives the inverse translation.** The deck transformation
`TauCeti.UniversalCover.loopDeck` of the class of `t ↦ t p`, acting through the fundamental-group
action, is `r ↦ r - p` on `ℝ`. -/
theorem universalCoverHomeomorph_loopDeck_periodLoop (u : UniversalCover (0 : AddCircle p)) :
    universalCoverHomeomorph p ((loopDeck (0 : AddCircle p)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (periodLoop p)))).val u) =
      universalCoverHomeomorph p u - p := by
  set g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (periodLoop p))
  set η := (deckFundamentalGroupEquiv (0 : AddCircle p)).symm
    (GeometricFundamentalGroup.mk (periodLoop p))
  have h : loopDeck (0 : AddCircle p) g = η⁻¹ := by
    rw [← inv_inv g, ← deckFundamentalGroupEquiv_symm_op, MulOpposite.op_inv, map_inv]
  have hη : η.val ((η⁻¹ : deck _).val u) = u := by
    simp
  have := universalCoverHomeomorph_deck_periodLoop p ((η⁻¹ : deck _).val u)
  rw [hη] at this
  rw [h]
  linarith

end AddCircle
