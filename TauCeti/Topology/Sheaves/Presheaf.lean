/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Restriction maps of presheaves

Restricting sections of a presheaf on a topological space to a smaller open and back again is the
identity, since the opens of a space form a thin category.

## Main results

* `TopCat.Presheaf.comp_map_comp_map_eq_self`: restricting sections to a smaller open and back
  again is the identity.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Presheaf

universe w v u

variable {C : Type u} [Category.{v} C] {T : TopCat.{w}}

/-- Restricting sections of a presheaf to a smaller open and back again, along any two maps of
opens, is the identity: the opens of a space form a thin category. The sections are given by a
morphism `a` into `F.obj (op V)`, so that the lemma applies by `exact` even when the intermediate
open is only definitionally equal to the one in the composite. -/
theorem comp_map_comp_map_eq_self {F : T.Presheaf C} {A : C} {V V' : Opens T}
    (a : A ⟶ F.obj (op V)) (i : op V ⟶ op V') (j : op V' ⟶ op V) :
    (a ≫ F.map i) ≫ F.map j = a := by
  rw [Category.assoc, ← F.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _), F.map_id, Category.comp_id]

end TopCat.Presheaf
