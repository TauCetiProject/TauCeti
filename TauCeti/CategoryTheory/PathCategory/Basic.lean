/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic

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
-/

public section

universe u h

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
