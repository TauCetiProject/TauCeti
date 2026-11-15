/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Ind

import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Composition of ind-morphisms

Let `P` be a property of morphisms that is stable under composition and cobase change, implies
finite presentability, and spreads out of filtered colimits (`MorphismProperty.PreIndSpreads`).
This file shows that `MorphismProperty.ind P` is then stable under composition.

Mathlib's `MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads` proves the same
conclusion under the assumption that every under category of the ambient category is finitely
accessible. The argument here replaces that assumption with local smallness, through
`MorphismProperty.ind_ind`, so it applies for instance to commutative rings without first
establishing that their under categories are finitely accessible. The proof of `ind_comp_mem`
reuses the diagram of pushouts from the proof of that Mathlib lemma, by Christian Merten.

## Main results

* `CategoryTheory.MorphismProperty.ind_comp_mem`: the composite of an `ind P`-morphism with a
  `P`-morphism satisfies `ind P`.
* `CategoryTheory.MorphismProperty.isStableUnderComposition_ind`: `ind P` is stable under
  composition.

## References

* [Stacks Project, Tag 0BSI](https://stacks.math.columbia.edu/tag/0BSI), for the
  special case of ind-étale ring maps.
-/

public section

universe w v u

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}

-- The argument has two steps. First, if `f : X ⟶ Y` is a filtered colimit of `P`-morphisms
-- `X ⟶ Yᵢ` and `g : Y ⟶ Z` satisfies `P`, then `g` descends to a `P`-morphism `Yⱼ ⟶ Z'` at some
-- stage, and `Z` is the filtered colimit of the pushouts of `Yⱼ ⟶ Z'` along the transition maps
-- `Yⱼ ⟶ Yₖ`; so `f ≫ g` satisfies `ind P` (`ind_comp_mem`). Second, for `g` itself in `ind P`,
-- this exhibits `f ≫ g` as a filtered colimit of `ind P`-morphisms, and `ind (ind P) = ind P`
-- because `P` implies finite presentability (`isStableUnderComposition_ind`).

/-- If `P` spreads out of filtered colimits and is stable under composition and cobase change,
then the composite of a morphism satisfying `ind P` with a morphism satisfying `P` satisfies
`ind P`. -/
lemma ind_comp_mem [HasPushouts C] [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange]
    [PreIndSpreads.{w} P] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : ind.{w} P f) (hg : P g) :
    ind.{w} P (f ≫ g) := by
  obtain ⟨J, _, _, D, s, t, ht, h⟩ := hf
  obtain ⟨j, W, g', w, hw, hg'⟩ := P.exists_isPushout_of_isFiltered ht g hg
  -- Over the stage `j`, the pushouts of `g'` along the transition maps form a filtered diagram
  -- with colimit `Z`.
  let D' : Under j ⥤ C := (Under.post D ⋙ Under.pushout g') ⋙ CategoryTheory.Under.forget _
  let c' : Cocone D' :=
    (Under.pushout g' ⋙ CategoryTheory.Under.forget _).mapCocone
      ((Cocone.mk _ t).underPost j) |>.extend hw.isoPushout.inv
  let hc' : IsColimit c' :=
    -- The instance `IsIso hw.isoPushout.inv` is not found through the unfolded cocone point.
    @IsColimit.extendIso _ _ _ _ _ _ _ _ (Iso.isIso_inv hw.isoPushout) <|
      isColimitOfPreserves _ (ht.underPost j)
  let s' : (Functor.const (Under j)).obj X ⟶ D' :=
    { app k := s.app k.right ≫ pushout.inl _ _
      naturality k l a := by
        have h2 := s.naturality a.right
        have ha : k.hom ≫ a.right = l.hom := CategoryTheory.Under.w a
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h2
        -- The structure maps of `Under.post D` are `D.map k.hom` only up to unfolding, so the
        -- simp lemmas of `Under.pushout` do not apply; restate the transition map of `D'`
        -- as the `pushout.desc` it is by definition.
        change 𝟙 X ≫ s.app l.right ≫ pushout.inl (D.map l.hom) g' =
          (s.app k.right ≫ pushout.inl (D.map k.hom) g') ≫
            pushout.desc (D.map a.right ≫ pushout.inl (D.map l.hom) g') (pushout.inr _ _)
              (by rw [← D.map_comp_assoc, ha, pushout.condition])
        rw [Category.id_comp, h2, Category.assoc, Category.assoc, pushout.inl_desc] }
  refine ⟨Under j, inferInstance, inferInstance, D', s', c'.ι, hc', fun k ↦ ⟨?_, ?_⟩⟩
  · exact P.comp_mem _ _ (h _).1 (P.pushout_inl _ _ hg')
  · -- As above, restate the leg of `c'` as the `pushout.desc` it is by definition.
    change (s.app k.right ≫ pushout.inl (D.map k.hom) g') ≫
        pushout.desc (t.app k.right ≫ pushout.inl (t.app j) g') (pushout.inr _ _)
          (by simp [← pushout.condition]) ≫ hw.isoPushout.inv = f ≫ g
    rw [Category.assoc, pushout.inl_desc_assoc, Category.assoc, hw.inl_isoPushout_inv,
      reassoc_of% (h k.right).2]

/-- If `P` implies finite presentability, spreads out of filtered colimits and is stable under
composition and cobase change, then `ind P` is stable under composition. Unlike Mathlib's
`MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads`, no accessibility of the under
categories is assumed. -/
lemma isStableUnderComposition_ind [LocallySmall.{w} C] [HasPushouts C]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [PreIndSpreads.{w} P]
    (H : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    rw [← ind_ind H]
    obtain ⟨J, _, _, D, s, t, ht, h⟩ := hg
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map f ≫ s, t, ht, fun j ↦ ⟨?_, ?_⟩⟩
    · exact ind_comp_mem hf (h j).1
    · simp [(h j).2]

end CategoryTheory.MorphismProperty
