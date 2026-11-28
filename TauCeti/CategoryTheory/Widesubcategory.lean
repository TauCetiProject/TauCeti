/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Inclusions between wide subcategories

Given a category `C` and multiplicative morphism properties `P ≤ Q` on `C`, every morphism in
`WideSubcategory P` lies in `WideSubcategory Q`, giving a faithful inclusion functor
`CategoryTheory.wideSubcategoryInclusionOfLE h : WideSubcategory P ⥤ WideSubcategory Q` whose
composite with `wideSubcategoryInclusion Q` is `wideSubcategoryInclusion P`.
-/

public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {P Q : MorphismProperty C}
  [P.IsMultiplicative] [Q.IsMultiplicative]

/-- The faithful inclusion `WideSubcategory P ⥤ WideSubcategory Q` induced by `P ≤ Q`. -/
@[expose]
def wideSubcategoryInclusionOfLE (h : P ≤ Q) :
    WideSubcategory P ⥤ WideSubcategory Q where
  obj x := ⟨x.obj⟩
  map f := ⟨f.hom, h _ f.property⟩

instance (h : P ≤ Q) : (wideSubcategoryInclusionOfLE h).Faithful where
  map_injective eq := WideSubcategory.hom_ext _ (congrArg (fun g ↦ g.hom) eq)

/-- Object map of `wideSubcategoryInclusionOfLE`. -/
@[simp]
lemma wideSubcategoryInclusionOfLE_obj (h : P ≤ Q) (x : WideSubcategory P) :
    (wideSubcategoryInclusionOfLE h).obj x = ⟨x.obj⟩ := (rfl)

/-- Morphism projection of `wideSubcategoryInclusionOfLE`. -/
@[simp]
lemma wideSubcategoryInclusionOfLE_map_hom (h : P ≤ Q) {x y : WideSubcategory P}
    (f : x ⟶ y) :
    ((wideSubcategoryInclusionOfLE h).map f).hom = f.hom := (rfl)

/-- Composing `wideSubcategoryInclusionOfLE h` with the inclusion of `WideSubcategory Q` into `C`
recovers the inclusion of `WideSubcategory P`. -/
@[simp]
lemma wideSubcategoryInclusionOfLE_comp_inclusion (h : P ≤ Q) :
    wideSubcategoryInclusionOfLE h ⋙ wideSubcategoryInclusion Q = wideSubcategoryInclusion P :=
  (rfl)

end CategoryTheory
