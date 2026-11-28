/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Slice

/-!
# Relative coslices of trivial fibrations

`SSet.coslice.rlp_monomorphisms_lift` shows that postcomposition along a trivial fibration
induces a trivial fibration on coslices relative to the projection to the ambient simplicial set.
It uses the union-join lifting criterion
`SSet.coslice.hasLiftingProperty_restrictionMap_of_unionJoin` and identifies the coslice of
an empty diagram with the ambient simplicial set.

The join description of coslices is from Lurie's *Higher Topos Theory*, §1.2.9.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace SSet.coslice

/-- For a trivial fibration `p : X ⟶ Y`, the relative coslice map
`X_{a/} ⟶ X ×_Y Y_{(a ≫ p)/}` is a trivial fibration. It lifts a cocone in `Y` with
its apex diagram already prescribed in `X`. -/
lemma rlp_monomorphisms_lift {K X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : (monomorphisms SSet.{u}).rlp p) (a : K ⟶ X) :
    (monomorphisms SSet.{u}).rlp
      (pullback.lift (π a) (map (q := a ≫ p) (𝟙 K) p (Category.id_comp _)) (map_π _ _ _).symm) := by
  let j := (⊥ : K.Subcomplex).ι
  let m := map (p := j ≫ a) (q := j ≫ a ≫ p) (𝟙 _) p (Category.id_comp _)
  let r := map (p := a ≫ p) (q := j ≫ a ≫ p) j (𝟙 Y) (by simp)
  have := isIso_π (p := j ≫ a) Subcomplex.not_nonempty_bot
  have := isIso_π (p := j ≫ a ≫ p) Subcomplex.not_nonempty_bot
  have hs : IsPullback (pullback.fst m r ≫ π (j ≫ a)) (pullback.snd m r) p (π (a ≫ p)) := by
    rw [← Category.comp_id (π (a ≫ p)), ← map_π j (𝟙 Y) (q := j ≫ a ≫ p) (by simp)]
    exact (IsPullback.of_hasPullback m r).paste_horiz (.of_horiz_isIso ⟨(map_π _ _ _).symm⟩)
  have heq : restrictionMap j p a ≫ hs.isoPullback.hom =
      pullback.lift (π a) (map (q := a ≫ p) (𝟙 K) p (Category.id_comp _))
        (map_π _ _ _).symm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      calc
        _ = restrictionMap j p a ≫ pullback.fst m r ≫ π (j ≫ a) := by
          rw [Category.assoc, hs.isoPullback_hom_fst]
        _ = _ := (restrictionMap_fst_assoc j p a _).trans
          ((map_π _ _ _).trans (Category.comp_id _))
    · rw [Category.assoc, hs.isoPullback_hom_snd, pullback.lift_snd]
      exact restrictionMap_snd j p a
  rw [← heq]
  exact ((monomorphisms SSet.{u}).rlp).comp_mem _ _ (fun _ _ i hi ↦
    letI : Mono i := hi
    hasLiftingProperty_restrictionMap_of_unionJoin _ p
      (fun n ↦ hp _ (monomorphisms.infer_property _)) a i) (rlp_of_isIso _ _)

end SSet.coslice
