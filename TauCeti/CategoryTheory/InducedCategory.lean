/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.InducedCategory

/-!
# Retracting a category onto an induced category

Let `F : S → C` be a map to the objects of a category `C`, and suppose that every object `x` of
`C` comes with an isomorphism `e x : x ≅ F (r x)` to an object in the image of `F`. Conjugating
by these isomorphisms defines the functor `TauCeti.InducedCategory.retraction F r e` from `C` to
the induced category `InducedCategory C F`, sending `x` to `r x`. When the chosen isomorphisms
are identities on the image of `F`, it is a strict retraction of the inclusion
`inducedFunctor F`.

Under the same hypothesis the inclusion `inducedFunctor F` is an equivalence, but an inverse
chosen by the equivalence machinery is not under control. Choosing the isomorphisms by hand
allows retractions of several categories to commute strictly with given functors between them,
which is what strict colimit arguments in the category of groupoids require. This is how a
fundamental groupoid is retracted onto its full subgroupoid on a set of basepoints,
compatibly with the fundamental groupoids of subspaces.

## Main declarations

* `TauCeti.InducedCategory.retraction`: the functor `C ⥤ InducedCategory C F` given by
  conjugation by the chosen isomorphisms.
* `TauCeti.InducedCategory.inducedFunctor_comp_retraction`: it is a retraction of the inclusion
  when the chosen isomorphisms are identities on the image of `F`.

## References

* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
-/

public section

open CategoryTheory

namespace TauCeti.InducedCategory

variable {C : Type*} [Category C] {S : Type*} (F : S → C) (r : C → S) (e : ∀ x, x ≅ F (r x))

/-- Conjugation by chosen isomorphisms `e x : x ≅ F (r x)`, as a functor from `C` to the induced
category on `F`: it sends `x` to `r x` and `f : x ⟶ y` to `(e x).inv ≫ f ≫ (e y).hom`. -/
@[expose]
def retraction : C ⥤ InducedCategory C F where
  obj := r
  map {x y} f := InducedCategory.homMk ((e x).inv ≫ f ≫ (e y).hom)
  map_id x := by ext; simp
  map_comp f g := by ext; simp

@[simp]
theorem retraction_obj (x : C) : (retraction F r e).obj x = r x :=
  (rfl)

@[simp]
theorem retraction_map_hom {x y : C} (f : x ⟶ y) :
    ((retraction F r e).map f).hom = (e x).inv ≫ f ≫ (e y).hom :=
  (rfl)

/-- If the chosen isomorphisms are identities on the image of `F`, the retraction restricts to
the identity of the induced category. -/
theorem inducedFunctor_comp_retraction (hr : ∀ s, r (F s) = s)
    (he : ∀ s, (e (F s)).hom = eqToHom (congrArg F (hr s)).symm) :
    inducedFunctor F ⋙ retraction F r e = 𝟭 _ := by
  have hinv (s : S) : (e (F s)).inv = eqToHom (congrArg F (hr s)) := by
    rw [← cancel_mono (e (F s)).hom, Iso.inv_hom_id, he, eqToHom_trans, eqToHom_refl]
  -- `hr` restated as an equality of objects of the induced category, not of `S`.
  have hobj (s : InducedCategory C F) : (inducedFunctor F ⋙ retraction F r e).obj s = s := hr s
  refine Functor.ext hobj fun s t f ↦ ?_
  ext
  simp only [Functor.comp_map, inducedFunctor_map, retraction_map_hom, Functor.id_map,
    InducedCategory.comp_hom, InducedCategory.eqToHom_hom, inducedFunctor_obj, hinv, he]
  -- The two sides differ only in how the endpoints of the `eqToHom`s are written.
  rfl

end TauCeti.InducedCategory
