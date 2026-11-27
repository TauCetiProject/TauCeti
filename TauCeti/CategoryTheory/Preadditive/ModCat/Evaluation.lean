/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Evaluation of modules over a preadditive category

Evaluation at an object followed by forgetting the abelian group structure preserves filtered
colimits. By the preadditive Yoneda lemma, two maps from a representable into the same stage of a
filtered diagram that agree in the colimit already agree at some later stage.
-/

public section

universe w v u

open CategoryTheory Category Limits Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Evaluate a module at an object and take the underlying type. -/
abbrev forgetEval (X : C) : ModCat.{w} C ⥤ Type w :=
  ((additiveFunctor Cᵒᵖ AddCommGrpCat.{w}).ι ⋙ (evaluation _ _).obj (op X)) ⋙
    forget AddCommGrpCat

/-- Evaluation sends a module map to its component at the evaluation object. -/
@[simp]
theorem forgetEval_map_apply (X : C) {M N : ModCat.{w} C}
    (m : M ⟶ N) (x : (forgetEval X).obj M) :
    (forgetEval X).map m x = m.hom.app (op X) x := (rfl)

/-- Evaluation into types preserves filtered colimits of shapes small in the value universe. -/
instance (X : C) {J : Type*} [Category* J] [IsFiltered J] [Small.{w} J] [LocallySmall.{w} J] :
    PreservesColimitsOfShape J (forgetEval.{w} X) := by
  have : Small.{w} (ShrinkHoms J) := ‹Small.{w} J›
  let e := ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w} _)).symm
  have := IsFiltered.of_equivalence e.symm
  exact preservesColimitsOfShape_of_equiv e (forgetEval X)

/-- Maps from a representable module agree if their evaluations agree on the identity. -/
theorem yoneda_hom_ext_of_forgetEval {X : C} {M : ModCat.{v} C}
    {a b : (yoneda C).obj X ⟶ M}
    (h : (forgetEval X).map a (𝟙 X) = (forgetEval X).map b (𝟙 X)) : a = b := by
  exact ObjectProperty.hom_ext _ (preadditiveYoneda_obj_hom_ext
    ((forgetEval_map_apply X a (𝟙 X)).symm.trans (h.trans (forgetEval_map_apply X b (𝟙 X)))))

/-- If two maps from a representable into a stage of a filtered diagram agree after composition
with the colimit leg, they agree after composition with a transition out of that stage. -/
theorem exists_comp_map_eq_of_comp_colimit_ι_eq {J : Type*} [Category* J] [IsFiltered J]
    [Small.{v} J] [LocallySmall.{v} J] {F : J ⥤ ModCat.{v} C} {X : C} {j : J}
    {a b : (yoneda C).obj X ⟶ F.obj j} (h : a ≫ colimit.ι F j = b ≫ colimit.ι F j) :
    ∃ (k : J) (g : j ⟶ k), a ≫ F.map g = b ≫ F.map g := by
  let E := forgetEval X
  have hh := congrArg (fun m : (yoneda C).obj X ⟶ colimit F ↦ E.map m (𝟙 X)) h
  simp only [Functor.map_comp] at hh
  obtain ⟨k, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves E (colimit.isColimit F)) (E.map a (𝟙 X)) (E.map b (𝟙 X))).mp hh
  have he : E.map (a ≫ F.map g) (𝟙 X) = E.map (b ≫ F.map g) (𝟙 X) := by
    simp only [Functor.map_comp]
    exact hg
  exact ⟨k, g, yoneda_hom_ext_of_forgetEval he⟩

end TauCeti.ModCat
