/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Quiv

/-!
# The path category of an explicit quiver, on the original objects

Mathlib's free category `Paths.categoryPaths` on a quiver `Q` is a category structure on the
type synonym `Paths O`. When several quivers on the same objects `O` are in play at once, for
instance the horizontal and the vertical generating quivers of an implicit double category, it
is convenient to read the free category as a category structure on `O` itself, supplied
explicitly rather than found by instance search. `TauCeti.pathCategory O Q` is this category
structure; its identities are empty paths and its composition is concatenation of paths.

## Main declarations

* `TauCeti.pathCategory`: the free category on an explicitly supplied quiver, on its objects.
* `Quiver.pathCategory_id` and `Quiver.pathCategory_comp`: its identities and composition, as
  operations on `Quiver.Path`.
* `CategoryTheory.Functor.map_eq_mapPath`: singleton preservation determines the action on paths.
-/

public section

universe u h u₁ u₂ h₁ h₂

namespace TauCeti

open CategoryTheory

/-- The free category on an explicitly supplied quiver `Q` on `O`: its morphisms are the paths
of `Q`, composed by concatenation. It is Mathlib's path category `Paths.categoryPaths`, read as a
category structure on `O` itself, and it is not installed as an instance. -/
abbrev pathCategory (O : Type u) (Q : Quiver.{h} O) : Category.{max u h} O :=
  @Paths.categoryPaths O Q

end TauCeti

namespace Quiver

open CategoryTheory TauCeti

variable {O : Type u}

/-- The identity morphism of the path category is the empty path. -/
@[simp]
theorem pathCategory_id (Q : Quiver.{h} O) (a : O) :
    CategoryStruct.id (self := (pathCategory O Q).toCategoryStruct) a = @Path.nil O Q a :=
  rfl

/-- Composition in the path category is concatenation of paths. -/
@[simp]
theorem pathCategory_comp (Q : Quiver.{h} O) {a b c : O} (p : @Path O Q a b)
    (q : @Path O Q b c) :
    CategoryStruct.comp (self := (pathCategory O Q).toCategoryStruct) p q = p.comp q :=
  rfl

end Quiver

namespace CategoryTheory.Functor

/-- A functor between path categories that preserves singleton paths acts on every path
by extending its map on generators. The generator map shares the functor's object map. -/
theorem map_eq_mapPath {O₁ : Type u₁} [Q₁ : Quiver.{h₁} O₁]
    {O₂ : Type u₂} [Q₂ : Quiver.{h₂} O₂]
    (F : Paths O₁ ⥤ Paths O₂)
    (map : ∀ {a b : O₁}, @Quiver.Hom O₁ Q₁ a b →
      @Quiver.Hom O₂ Q₂ (F.obj a) (F.obj b))
    (hmap : ∀ {a b : O₁} (f : @Quiver.Hom O₁ Q₁ a b),
      F.map (@Quiver.Hom.toPath O₁ Q₁ a b f) = @Quiver.Hom.toPath O₂ Q₂ _ _ (map f))
    {a b : O₁} (p : @Quiver.Path O₁ Q₁ a b) :
    F.map p = @Prefunctor.mapPath O₁ Q₁ O₂ Q₂ ⟨F.obj, map⟩ a b p := by
  let φ : @Prefunctor O₁ Q₁ O₂ Q₂ := ⟨F.obj, map⟩
  have h : F = Cat.freeMap φ := by
    apply Paths.ext_functor (F := F) (G := Cat.freeMap φ) rfl
    intro a b f
    convert! hmap f using 1
  exact eq_of_heq (Functor.hcongr_hom h p)

end CategoryTheory.Functor
