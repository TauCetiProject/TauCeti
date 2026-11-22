/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Path categories of explicitly supplied quivers

Mathlib's path category `CategoryTheory.Paths.categoryPaths` and paths of length one
`Quiver.Hom.toPath` take the quiver structure as an instance argument. When one type carries
several quivers, as the objects of an implicit double category carry a horizontal and a vertical
generating quiver, the quiver has to be named explicitly. This file supplies those two
constructions with the quiver as an explicit argument.

## Main declarations

* `Quiver.pathCategory`: the category of paths of an explicitly supplied quiver.
* `Quiver.Hom.toPathOf`: the path of length one on a generator of an explicitly supplied quiver.
-/

@[expose] public section

universe u h

open CategoryTheory

/-- The category of paths of an explicitly supplied quiver `Q` on `O`. Its morphisms are the
paths `Quiver.Path`, its composition is concatenation and its identities are the empty paths. -/
abbrev Quiver.pathCategory (O : Type u) (Q : Quiver.{h} O) : Category.{max u h} O :=
  @Paths.categoryPaths O Q

/-- The path of length one on a generator `f` of an explicitly supplied quiver `Q`: this is
`Quiver.Hom.toPath` with the quiver given explicitly. -/
abbrev Quiver.Hom.toPathOf {O : Type u} (Q : Quiver.{h} O) {a b : O} (f : @Quiver.Hom O Q a b) :
    @Quiver.Path O Q a b :=
  @Quiver.Hom.toPath O Q a b f
