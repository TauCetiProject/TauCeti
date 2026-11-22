/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Basic lemmas on subobjects

This file records supplementary lemmas on inclusions `Subobject.ofLE` of subobjects.

## Main results

* `CategoryTheory.Subobject.ofLE_self_comp`: composing with a self-inclusion `Subobject.ofLE S S h`
  does nothing, even when the source and target agree only definitionally.
-/

public section

open CategoryTheory

namespace CategoryTheory.Subobject

universe v u

variable {C : Type u} [Category.{v} C]

/-- Composing with the inclusion of a subobject into itself does nothing. The hypothesis `S ≤ S`
is stated for a single `S`, so this applies wherever the source and target of `ofLE` agree only
after unfolding a definition. -/
@[reassoc]
lemma ofLE_self_comp {A X : C} {S : Subobject A} (h : S ≤ S) (f : (S : C) ⟶ X) :
    ofLE S S h ≫ f = f := by
  rw [ofLE_refl, Category.id_comp]

end CategoryTheory.Subobject
