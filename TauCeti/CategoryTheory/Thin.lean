/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.InducedCategory

/-!
# Thin categories: induced categories and naturality

A category is thin (`Quiver.IsThin`) when there is at most one morphism between any two objects.
Mathlib records that functor categories into a thin category are thin, that the opposite of a thin
category is thin, and that every functor out of a thin category is faithful. This file records one
further closure property: a category induced along a map into a thin category is thin. It also
records a naturality computation for a natural transformation `η : F ⟶ G ⋙ H` where `G` lands in a
thin category, in which thinness makes the two morphisms of that category that arise equal.

The motivating instance is the category of members of a family `B` of opens of a topological
space, `InducedCategory (Opens X) (Subtype.val : B → Opens X)`, which indexes the limits describing
a presheaf adapted to `B`. Thinness makes the functor laws of functors between such index
categories instances of `Subsingleton.elim`, and it makes their faithfulness automatic. It does
not by itself make such a functor full: a preimage must still be constructed, although thinness
then discharges the equation the preimage has to satisfy.

## Main results

* `TauCeti.CategoryTheory.instIsThinInducedCategory`: a category induced along a map into a thin
  category is thin.
* `CategoryTheory.NatTrans.map_comp_app_comp_map_comp_map`: moving `η : F ⟶ G ⋙ H` past a map
  `F.map a`, when `G` lands in a thin category.
-/

public section

namespace TauCeti

namespace CategoryTheory

open _root_.CategoryTheory

/-- A category induced along a map into a thin category is thin. -/
instance instIsThinInducedCategory {C D : Type*} [Category* D] [Quiver.IsThin D] (F : C → D) :
    Quiver.IsThin (InducedCategory D F) :=
  fun _ _ ↦ InducedCategory.homEquiv.subsingleton

end CategoryTheory

end TauCeti

namespace CategoryTheory.NatTrans

/-- **Moving a natural transformation past a map, when the target is thin.** For functors
`F : 𝒟 ⥤ 𝒞`, `G : 𝒟 ⥤ ℰ` and `H : ℰ ⥤ 𝒞` with `ℰ` thin, and `η : F ⟶ G ⋙ H`, the map `F.map a`
followed by `η.app B'` and the image under `H` of a morphism out of `G.obj B'` is `η.app W` followed
by the image of the unique morphism. The equalities `h₁ : B = B'` and `h₂ : Z₁ = Z₁'` allow the
objects to be identified along the way; applied with `rfl`, they absorb casts `eqToHom` between
objects that are only definitionally equal. -/
theorem map_comp_app_comp_map_comp_map {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]
    [Quiver.IsThin ℰ] {F : 𝒟 ⥤ 𝒞} {G : 𝒟 ⥤ ℰ} {H : ℰ ⥤ 𝒞} (η : F ⟶ G ⋙ H) {W B B' : 𝒟}
    {Z₁ Z₁' Z₂ : ℰ} (a : W ⟶ B) (h₁ : B = B') (k₁ : G.obj B' ⟶ Z₁) (h₂ : Z₁ = Z₁')
    (k₂ : Z₁' ⟶ Z₂) (l : G.obj W ⟶ Z₂) :
    (F.map a ≫ eqToHom (congrArg F.obj h₁) ≫ η.app B' ≫ H.map k₁ ≫
      eqToHom (congrArg H.obj h₂)) ≫ H.map k₂ = η.app W ≫ H.map l := by
  subst h₁ h₂
  simp [Subsingleton.elim l (G.map a ≫ k₁ ≫ k₂)]

end CategoryTheory.NatTrans

end
