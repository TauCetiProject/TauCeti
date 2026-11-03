/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Common refinements of covering families

Given two families of objects `X₁` and `X₂` that cover the terminal object of a site, this file
constructs a third covering family each of whose members maps to a member of `X₁` and to a member
of `X₂`. Such common refinements are used to compare two local trivializations of a sheaf.

## Main definitions

* `CategoryTheory.GrothendieckTopology.CoversTop.CommonRefinement`: a covering family together
  with arrows from each of its members to a member of each of two given families.
* `CategoryTheory.GrothendieckTopology.CoversTop.commonRefinement`: a common refinement of two
  families covering the terminal object.
-/

public section

open CategoryTheory

universe w u v

namespace CategoryTheory.GrothendieckTopology.CoversTop

variable {C : Type u} [Category.{v} C]

/-- A common refinement of two covering families.

Each object in the refined family admits arrows to one member of each original family. -/
structure CommonRefinement (J : GrothendieckTopology C) {I₁ I₂ : Type*}
    (X₁ : I₁ → C) (X₂ : I₂ → C) where
  /-- The indexing type of the common refinement. -/
  I : Type w
  /-- The objects in the common refinement. -/
  X : I → C
  /-- The member of the first covering family above each refined object. -/
  leftIndex : I → I₁
  /-- The arrow from each refined object to its member of the first covering family. -/
  left : ∀ i, X i ⟶ X₁ (leftIndex i)
  /-- The member of the second covering family above each refined object. -/
  rightIndex : I → I₂
  /-- The arrow from each refined object to its member of the second covering family. -/
  right : ∀ i, X i ⟶ X₂ (rightIndex i)
  /-- The refined family covers the top. -/
  coversTop : J.CoversTop X

/-- A common refinement of two families covering the terminal object.

The refined family consists of all objects admitting an arrow to a member of each original
family, so it is indexed by a type in the universe of the objects of `C`. -/
noncomputable def commonRefinement {I₁ I₂ : Type*} {X₁ : I₁ → C} {X₂ : I₂ → C}
    {J : GrothendieckTopology C} (h₁ : J.CoversTop X₁) (h₂ : J.CoversTop X₂) :
    CommonRefinement.{u} J X₁ X₂ where
  I := {W : C // (∃ i, Nonempty (W ⟶ X₁ i)) ∧ ∃ j, Nonempty (W ⟶ X₂ j)}
  X := Subtype.val
  leftIndex w := w.2.1.choose
  left w := w.2.1.choose_spec.some
  rightIndex w := w.2.2.choose
  right w := w.2.2.choose_spec.some
  coversTop A := J.superset_covering (fun Z _ hZ ↦ ⟨⟨Z, hZ⟩, ⟨𝟙 Z⟩⟩)
    (J.intersection_covering (h₁ A) (h₂ A))

end CategoryTheory.GrothendieckTopology.CoversTop
