/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# The cartesian monoidal structure on type-valued functors, elementwise

For functors `F G : J ⥤ Type v`, the product functor `F ⊗ G` takes the value `F.obj j × G.obj j`
at `j`. This file records how its action on morphisms, the whiskering `F ◁ g` and the projections
`fst F G` and `snd F G` act on elements. Mathlib's `Functor.Monoidal.tensorObj_map` and
`tensor_apply` do not compose to give these, as the types of the two sides of the former differ
syntactically.
-/

public section

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory CartesianMonoidalCategory

universe v

variable {J : Type*} [Category* J] {F G : J ⥤ Type v}

theorem tensorObj_map_apply {j j' : J} (f : j ⟶ j') (x : (F ⊗ G).obj j) :
    (F ⊗ G).map f x = (F.map f x.1, G.map f x.2) :=
  (rfl)

theorem tensorObj_map_apply_fst {j j' : J} (f : j ⟶ j') (x : (F ⊗ G).obj j) :
    ((F ⊗ G).map f x).1 = F.map f x.1 :=
  (rfl)

theorem tensorObj_map_apply_snd {j j' : J} (f : j ⟶ j') (x : (F ⊗ G).obj j) :
    ((F ⊗ G).map f x).2 = G.map f x.2 :=
  (rfl)

theorem whiskerLeft_app_apply_fst {G' : J ⥤ Type v} (g : G ⟶ G') {j : J} (x : (F ⊗ G).obj j) :
    ((F ◁ g).app j x).1 = x.1 :=
  (rfl)

theorem whiskerLeft_app_apply_snd {G' : J ⥤ Type v} (g : G ⟶ G') {j : J} (x : (F ⊗ G).obj j) :
    ((F ◁ g).app j x).2 = g.app j x.2 :=
  (rfl)

theorem fst_app_apply {j : J} (x : (F ⊗ G).obj j) : (fst F G).app j x = x.1 :=
  (rfl)

theorem snd_app_apply {j : J} (x : (F ⊗ G).obj j) : (snd F G).app j x = x.2 :=
  (rfl)

end CategoryTheory.Functor.Monoidal
