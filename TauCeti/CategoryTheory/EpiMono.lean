/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Isomorphisms from isomorphic composites

If `f ≫ g` and `g ≫ h` are isomorphisms, then `g` is an isomorphism: the second composite makes
`g` a split monomorphism and the first makes it a split epimorphism. This is the core of the
two-out-of-six property of isomorphisms, and is how a homotopy equivalence is shown to induce
isomorphisms on a homotopy-invariant functor (`IsIso.of_isIso_comp_of_isIso_comp`).

`Functor.isSplitEpi_of_map_comp_eq_id` reflects a section equation using injectivity
on the endomorphisms of the target and the functor's composition and identity laws.
-/

public section

namespace CategoryTheory.IsIso

variable {C : Type*} [Category* C] {W X Y Z : C}

/-- If `f ≫ g` and `g ≫ h` are isomorphisms, then so is `g`. -/
theorem of_isIso_comp_of_isIso_comp {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z} (_ : IsIso (f ≫ g))
    (_ : IsIso (g ≫ h)) : IsIso g :=
  have : IsSplitMono g := .mk' ⟨h ≫ inv (g ≫ h), by rw [← Category.assoc, hom_inv_id]⟩
  have : IsSplitEpi g := .mk' ⟨inv (f ≫ g) ≫ f, by rw [Category.assoc, inv_hom_id]⟩
  isIso_of_mono_of_isSplitEpi g

end CategoryTheory.IsIso

namespace CategoryTheory.Functor

/-- If `F` is injective on endomorphisms of `Y` and sends `g` to a section of `F.map f`,
then `f : X ⟶ Y` is a split epimorphism. -/
theorem isSplitEpi_of_map_comp_eq_id {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X}
    (hinj : Function.Injective (F.map : (Y ⟶ Y) → _))
    (h : F.map g ≫ F.map f = 𝟙 (F.obj Y)) : IsSplitEpi f := by
  refine IsSplitEpi.mk' ⟨g, hinj ?_⟩
  simpa only [F.map_comp, F.map_id] using h

end CategoryTheory.Functor
