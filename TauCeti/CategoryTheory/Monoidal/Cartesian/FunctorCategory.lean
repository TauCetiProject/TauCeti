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
`fst F G` and `snd F G` act on elements, together with the pointwise braiding and associator.
Mathlib's `Functor.Monoidal.tensorObj_map` and `tensor_apply` do not compose to give the
elementwise map equation, as the types of the two sides of the former differ syntactically.
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

namespace TauCeti

open CategoryTheory MonoidalCategory

universe v

variable {J : Type*} [Category* J] {F G H : J ⥤ Type v} {j : J}

/-- The pointwise braiding interchanges the two components of a pair. -/
theorem braiding_hom_app_apply {x : (F ⊗ G).obj j} :
    (β_ F G).hom.app j x = (x.2, x.1) :=
  (rfl)

/-- The pointwise associator regroups a left-associated triple. -/
theorem associator_hom_app_apply {x : ((F ⊗ G) ⊗ H).obj j} :
    (α_ F G H).hom.app j x = (x.1.1, (x.1.2, x.2)) :=
  (rfl)

/-- The inverse pointwise associator regroups a right-associated triple. -/
theorem associator_inv_app_apply {x : (F ⊗ (G ⊗ H)).obj j} :
    (α_ F G H).inv.app j x = ((x.1, x.2.1), x.2.2) :=
  (rfl)

/-- Left whiskering keeps the first component and applies the natural transformation to the
second component. -/
theorem whiskerLeft_app_apply {G' : J ⥤ Type v} {g : G ⟶ G'} {x : (F ⊗ G).obj j} :
    (F ◁ g).app j x = (x.1, g.app j x.2) :=
  (rfl)

end TauCeti
