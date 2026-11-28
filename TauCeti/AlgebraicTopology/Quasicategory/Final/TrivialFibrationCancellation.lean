/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Final
import TauCeti.AlgebraicTopology.SimplicialSet.Coslice.RelativeTrivialFibration
import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.TrivialFibration

/-!
# Cancellation of trivial fibrations in finality

`SSet.isFinal_precomp_iff_of_rlp_monomorphisms` and
`SSet.isFinal_postcomp_iff_of_rlp_monomorphisms` show that precomposition and
postcomposition by a trivial fibration preserve and reflect finality. Both
compare the pullbacks of coslices by trivial fibrations, using Mathlib's
`MorphismProperty.rlp_isStableUnderBaseChange` and
`SSet.coslice.rlp_monomorphisms_lift`.

See Lurie's *Higher Topos Theory*, Theorem 4.1.3.1, for the coslice criterion for finality.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty Simplicial

namespace SSet

variable {X Y Z : SSet.{u}}

/-- Precomposition by a trivial fibration preserves and reflects finality. -/
lemma isFinal_precomp_iff_of_rlp_monomorphisms {p : X ⟶ Y}
    {f : Y ⟶ Z} (hp : (monomorphisms SSet.{u}).rlp p) :
    IsFinal (p ≫ f) ↔ IsFinal f := by
  rw [isFinal_iff, isFinal_iff]
  refine forall_congr' fun z ↦ ?_
  let q := coslice.π (const z : Δ[0] ⟶ Z)
  have sq := (IsPullback.of_hasPullback (p ≫ f) q).of_bot' (IsPullback.of_hasPullback f q)
  have hr := ((monomorphisms SSet.{u}).rlp).of_isPullback sq hp
  exact @isWeaklyContractible_iff_of_isWeakHomotopyEquivalence _ _ _
    (isWeakHomotopyEquivalence_of_rlp_monomorphisms hr)

/-- Postcomposition by a trivial fibration preserves and reflects finality. -/
lemma isFinal_postcomp_iff_of_rlp_monomorphisms {f : X ⟶ Y} {p : Y ⟶ Z}
    (hp : (monomorphisms SSet.{u}).rlp p) :
    IsFinal (f ≫ p) ↔ IsFinal f := by
  rw [isFinal_iff, isFinal_iff]
  have := isSplitEpi_of_rlp_monomorphisms hp
  have hs : Function.Surjective (p.app (Opposite.op ⦋0⦌)) := by
    intro z
    exact ⟨(section_ p).app _ z, ConcreteCategory.congr_hom
      (NatTrans.congr_app (IsSplitEpi.id p) _) z⟩
  refine hs.forall.trans (forall_congr' fun y ↦ ?_)
  rw [← const_comp]
  let a : Δ[0] ⟶ Y := const y
  let q := coslice.π (a ≫ p)
  let c := pullback.lift (coslice.π a)
    (coslice.map (q := a ≫ p) (𝟙 _) p (Category.id_comp _)) (coslice.map_π _ _ _).symm
  -- Both comma objects can be formed over `Y`, with `c` relating their coslice factors.
  have hright := (IsPullback.of_hasPullback (f ≫ p) q).of_bot' (IsPullback.of_hasPullback p q)
  have houter : IsPullback (pullback.fst f (coslice.π a)) (pullback.snd f (coslice.π a))
      f (c ≫ pullback.fst p q) := by
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  have h := houter.of_right' hright
  have hr := ((monomorphisms SSet.{u}).rlp).of_isPullback h.flip
    (coslice.rlp_monomorphisms_lift hp a)
  exact (@isWeaklyContractible_iff_of_isWeakHomotopyEquivalence _ _ _
    (isWeakHomotopyEquivalence_of_rlp_monomorphisms hr)).symm

end SSet
