/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Based topological spaces

A `TauCeti.BasedTopologicalSpace` is a topological space together with a basepoint. It is the
carrier for constructions that need a distinguished point of the space itself, such as loop spaces
and based mapping spaces. `TauCeti.BasedTopologicalSpace.Hom` is the type of
continuous maps preserving the basepoint.

## Main declarations

* `TauCeti.BasedTopologicalSpace`: a topological space with a basepoint.
* `TauCeti.BasedTopologicalSpace.Hom`: basepoint-preserving continuous maps, with `Hom.id` and
  `Hom.comp`, forming a category.
-/

public section

universe u

open CategoryTheory

namespace TauCeti

/-- A topological space with a basepoint. -/
structure BasedTopologicalSpace where
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  /-- The basepoint. -/
  basepoint : carrier

attribute [instance] BasedTopologicalSpace.topologicalSpace

namespace BasedTopologicalSpace

/-- A morphism of based topological spaces: a continuous map preserving the basepoint. -/
@[ext]
structure Hom (X Y : BasedTopologicalSpace.{u}) where
  /-- The underlying continuous map. -/
  toContinuousMap : C(X.carrier, Y.carrier)
  /-- The map sends the basepoint to the basepoint. -/
  map_basepoint : toContinuousMap X.basepoint = Y.basepoint

namespace Hom

variable {X Y Z : BasedTopologicalSpace.{u}}

instance : FunLike (Hom X Y) X.carrier Y.carrier where
  coe f := f.toContinuousMap
  coe_injective _ _ h := Hom.ext (DFunLike.coe_injective h)

instance : ContinuousMapClass (Hom X Y) X.carrier Y.carrier where
  map_continuous f := f.toContinuousMap.continuous

/-- A morphism sends the basepoint to the basepoint. -/
@[simp]
theorem map_basepoint_apply (f : Hom X Y) : f X.basepoint = Y.basepoint :=
  f.map_basepoint

@[simp]
theorem coe_toContinuousMap (f : Hom X Y) : ⇑f.toContinuousMap = ⇑f :=
  rfl

/-- The identity morphism. -/
def id (X : BasedTopologicalSpace.{u}) : Hom X X := ⟨ContinuousMap.id _, rfl⟩

/-- The composite of two morphisms. -/
def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z :=
  ⟨g.toContinuousMap.comp f.toContinuousMap, by
    rw [ContinuousMap.comp_apply, f.map_basepoint, g.map_basepoint]⟩

@[simp]
theorem coe_id : ⇑(Hom.id X) = _root_.id := by
  rw [Hom.id]; rfl

@[simp]
theorem id_apply (x : X.carrier) : Hom.id X x = x := by
  rw [Hom.id]; rfl

@[simp]
theorem coe_comp (g : Hom Y Z) (f : Hom X Y) : ⇑(g.comp f) = g ∘ f := by
  rw [Hom.comp]; rfl

@[simp]
theorem comp_apply (g : Hom Y Z) (f : Hom X Y) (x : X.carrier) : g.comp f x = g (f x) := by
  rw [Hom.comp]; rfl

@[simp]
theorem coe_mk (f : C(X.carrier, Y.carrier)) (h : f X.basepoint = Y.basepoint) :
    ⇑(Hom.mk f h) = f :=
  rfl

@[simp]
theorem toContinuousMap_id (X : BasedTopologicalSpace.{u}) :
    (Hom.id X).toContinuousMap = ContinuousMap.id X.carrier := by
  rw [Hom.id]

@[simp]
theorem toContinuousMap_comp (g : Hom Y Z) (f : Hom X Y) :
    (g.comp f).toContinuousMap = g.toContinuousMap.comp f.toContinuousMap := by
  rw [Hom.comp]

@[simp]
theorem id_comp (f : Hom X Y) : (Hom.id Y).comp f = f :=
  DFunLike.ext _ _ fun x => by rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : Hom X Y) : f.comp (Hom.id X) = f :=
  DFunLike.ext _ _ fun x => by rw [comp_apply, id_apply]

theorem comp_assoc {W : BasedTopologicalSpace.{u}} (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  DFunLike.ext _ _ fun x => by simp only [comp_apply]

end Hom

instance : Category BasedTopologicalSpace.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := Hom.comp_id
  comp_id := Hom.id_comp
  assoc f g h := (Hom.comp_assoc h g f).symm

/-- The identity of the category of based spaces is `Hom.id`. -/
@[simp]
theorem id_eq_hom_id (X : BasedTopologicalSpace.{u}) : (𝟙 X : X ⟶ X) = Hom.id X :=
  rfl

/-- Composition in the category of based spaces is `Hom.comp`, in the opposite order. -/
@[simp]
theorem comp_eq_hom_comp {X Y Z : BasedTopologicalSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = Hom.comp g f :=
  rfl

end BasedTopologicalSpace

end TauCeti
