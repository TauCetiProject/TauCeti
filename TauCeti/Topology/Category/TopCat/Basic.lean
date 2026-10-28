/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Functors from topological spaces

Functorial composition can be checked pointwise on the underlying continuous maps, even when
the morphisms have different presentations.
-/

public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Functor

/-- A functor from topological spaces maps pointwise-equal composites to equal morphisms. -/
lemma map_comp_eq_of_topCat_apply_eq {D : Type u} [Category.{v} D]
    (F : TopCat.{w} ⥤ D) {A B E : TopCat.{w}}
    (f : A ⟶ B) (g : B ⟶ E) (h : A ⟶ E) (hfg : ∀ x, g (f x) = h x) :
    F.map f ≫ F.map g = F.map h := by
  rw [← F.map_comp]
  exact congrArg F.map (TopCat.ext hfg)

end CategoryTheory.Functor
