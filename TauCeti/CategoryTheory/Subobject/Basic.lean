/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Additional basic lemmas for `Subobject.map`

Because `Subobject.map f` carries a dependent `[Mono f]` argument, rewriting `f` directly inside
`Subobject.map` fails with a motive error. This file records congruence and `ofLE`-factorisation
lemmas that bypass that obstruction:

* `CategoryTheory.Subobject.map_congr`: `Subobject.map` depends only on the morphism up to
  equality.
* `CategoryTheory.Subobject.map_mk_ofLE`: mapping `Subobject.mk (Subobject.ofLE B Z h)` along
  `Z.arrow` recovers `B`.
* `CategoryTheory.Subobject.map_arrow_eq_map_ofLE`: mapping along `S.arrow` factors as mapping
  along `Subobject.ofLE S T h` followed by mapping along `T.arrow`.
-/

public section

open CategoryTheory

namespace CategoryTheory.Subobject

universe v u

variable {C : Type u} [Category.{v} C]

/-- `Subobject.map` depends only on the morphism up to equality. -/
theorem map_congr {X Y : C} {f g : X ⟶ Y} [Mono f] [Mono g] (h : f = g) (S : Subobject X) :
    (Subobject.map f).obj S = (Subobject.map g).obj S := by
  subst h
  rfl

/-- Mapping `Subobject.mk (Subobject.ofLE B Z h)` along `Z.arrow` recovers `B`. -/
@[simp]
theorem map_mk_ofLE {A : C} {B Z : Subobject A} (h : B ≤ Z) :
    (Subobject.map Z.arrow).obj (Subobject.mk (Subobject.ofLE B Z h)) = B := by
  rw [Subobject.map_mk]
  exact Subobject.mk_eq_of_comm _ (Iso.refl _) (by simp)

/-- Mapping along `S.arrow` factors as mapping along `Subobject.ofLE S T h` followed by mapping
along `T.arrow`. -/
theorem map_arrow_eq_map_ofLE {A : C} {S T : Subobject A} (h : S ≤ T) (U : Subobject (S : C)) :
    (Subobject.map S.arrow).obj U =
      (Subobject.map T.arrow).obj ((Subobject.map (Subobject.ofLE S T h)).obj U) := by
  rw [← Subobject.map_comp]
  exact map_congr (Subobject.ofLE_arrow h).symm U

end CategoryTheory.Subobject
