/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Simplices of colimits of simplicial sets

Colimits of simplicial sets are computed degreewise, since evaluation at each degree is a left
adjoint. This file records the resulting descriptions of the simplices of a colimit cocone: every
simplex of the cocone point comes from some stage of the diagram, and for a filtered diagram two
simplices of the same stage become equal in the colimit exactly when they become equal at a later
stage. No colimit-existence hypothesis is needed, and the diagram may have any size.

## Main results

* `SSet.exists_ι_app_eq_of_isColimit`: every simplex of a colimit comes from some stage.
* `SSet.ι_app_eq_ι_app_iff_of_isColimit`: in a filtered colimit, two simplices of a stage have the
  same image exactly when they agree at a later stage.
* `SSet.ι_app_map_app`: the image of a simplex in the cocone point does not change when the
  simplex is first pushed to a later stage.
-/

public section

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

variable {J : Type*} [Category* J] {F : J ⥤ SSet.{u}} {c : Cocone F}

/-- The image of a simplex of `F.obj j` in the cocone point does not change when the simplex is
first pushed to `F.obj k` along `f : j ⟶ k`. -/
@[simp]
lemma ι_app_map_app {j k : J} (f : j ⟶ k) {m : ℕ} (x : (F.obj j) _⦋m⦌) :
    dsimp% (c.ι.app k).app _ ((F.map f).app _ x) = (c.ι.app j).app _ x := by
  rw [← c.w f]
  rfl

variable (hc : IsColimit c)

include hc in
/-- Every simplex of a colimit of simplicial sets comes from some stage of the diagram. -/
lemma exists_ι_app_eq_of_isColimit {m : ℕ} (x : c.pt _⦋m⦌) :
    ∃ j y, (c.ι.app j).app _ y = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋m⦌)) hc) x

include hc in
/-- In a filtered colimit of simplicial sets, two simplices of the same stage have the same image
exactly when they agree at some later stage. -/
lemma ι_app_eq_ι_app_iff_of_isColimit [IsFilteredOrEmpty J] {m : ℕ} {j : J}
    (x y : (F.obj j) _⦋m⦌) :
    (c.ι.app j).app _ x = (c.ι.app j).app _ y ↔
      ∃ (k : J) (f : j ⟶ k), (F.map f).app _ x = (F.map f).app _ y :=
  Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋m⦌)) hc) x y

end SSet
