/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Families of elements on opens

A family of elements indexed by arrows between opens depends only on the domain, since there is
at most one arrow between two opens.

Use `TauCeti.CategoryTheory.Presieve.FamilyOfElements.congr x f g hf hg` to compare these values.
-/

public section

open CategoryTheory _root_.TopologicalSpace

universe u w

namespace TauCeti.CategoryTheory.Presieve.FamilyOfElements

variable {X : Type u} [_root_.TopologicalSpace X] {F : (Opens X)ᵒᵖ ⥤ Type w}

/-- Two values of a family of elements at arrows with the same domain are equal, since arrows
between opens are subsingletons. -/
theorem congr {W V : Opens X} {R : Presieve W}
    (x : _root_.CategoryTheory.Presieve.FamilyOfElements F R) (f g : V ⟶ W)
    (hf : R f) (hg : R g) :
    x f hf = x g hg := by
  obtain rfl : f = g := Subsingleton.elim _ _
  rfl

end TauCeti.CategoryTheory.Presieve.FamilyOfElements
