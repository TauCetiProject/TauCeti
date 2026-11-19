/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Based topological spaces

A `TauCeti.BasedTopologicalSpace` is a topological space together with a basepoint. It is the
carrier for constructions that need a distinguished point of the space itself, such as loop spaces
and based mapping spaces. `TauCeti.BasedTopologicalSpace.Hom` is the type of
continuous maps preserving the basepoint.

A based space `X` gives the topological pair `(X, *)` whose subspace is the one-point space
mapped to the basepoint (`TauCeti.BasedTopologicalSpace.toTopPair`). Relative invariants of this
pair, such as the relative groups of a homology theory, are the reduced invariants of `X`.
Adding a disjoint basepoint to a space `X` gives the based space `X₊ = * ⊔ X`
(`TauCeti.BasedTopologicalSpace.addBasepoint`), the coproduct of the point and `X`
(`TauCeti.BasedTopologicalSpace.addBasepointIsColimit`).

## Main declarations

* `TauCeti.BasedTopologicalSpace`: a topological space with a basepoint.
* `TauCeti.BasedTopologicalSpace.Hom`: basepoint-preserving continuous maps, with `Hom.id` and
  `Hom.comp`, forming a category.
* `TauCeti.BasedTopologicalSpace.toTopPair`: the functor `X ↦ (X, *)` to topological pairs.
* `TauCeti.BasedTopologicalSpace.addBasepoint`: the functor `X ↦ X₊` adding a disjoint basepoint.
* `TauCeti.BasedTopologicalSpace.addBasepointInr` and `addBasepointIsColimit`: the inclusion
  `X ⟶ X₊`, which with the basepoint exhibits `X₊` as the coproduct `* ⊔ X`.
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

/-- The topological pair `(X, *)` of a based space: the one-point space, embedded at the
basepoint, as a subspace of `X`. A based map is a map of pairs which is the identity on the
point. -/
@[expose, implicit_reducible, simps obj_left obj_right obj_hom map_left map_right]
def toTopPair : BasedTopologicalSpace.{u} ⥤ TopPair.{u} where
  obj X :=
    { left := TopCat.of PUnit.{u + 1}
      right := TopCat.of X.carrier
      hom := TopCat.ofHom (ContinuousMap.const _ X.basepoint)
      prop := Topology.IsEmbedding.of_subsingleton (X := PUnit.{u + 1}) _ }
  map f :=
    { left := 𝟙 (TopCat.of PUnit.{u + 1})
      right := TopCat.ofHom f.toContinuousMap
      w := by ext; exact f.map_basepoint.symm
      prop_hom_left := trivial
      prop_hom_right := trivial }

/-- The space `X₊ = * ⊔ X` obtained by adding a disjoint basepoint to a space `X`. -/
@[expose, implicit_reducible, simps]
def addBasepoint : TopCat.{u} ⥤ BasedTopologicalSpace.{u} where
  obj X := ⟨PUnit.{u + 1} ⊕ X, Sum.inl PUnit.unit⟩
  map f := ⟨⟨Sum.map id f, by fun_prop⟩, rfl⟩
  map_id _ := Hom.ext <| ContinuousMap.ext fun x ↦ by cases x <;> rfl
  map_comp _ _ := Hom.ext <| ContinuousMap.ext fun x ↦ by cases x <;> rfl

/-- The inclusion `X ⟶ X₊` of a space into the space with a disjoint basepoint added. -/
def addBasepointInr (X : TopCat.{u}) : X ⟶ TopCat.of (PUnit.{u + 1} ⊕ X) :=
  TopCat.ofHom ⟨Sum.inr, continuous_inr⟩

/-- The inclusion `X ⟶ X₊` sends a point `x` to `Sum.inr x`. -/
@[simp]
lemma addBasepointInr_apply (X : TopCat.{u}) (x : X) : addBasepointInr X x = Sum.inr x :=
  (rfl)

/-- The space `X₊` is the coproduct `* ⊔ X`, with inclusions the basepoint of the pair `(X₊, *)`
and `addBasepointInr`. -/
def addBasepointIsColimit (X : TopCat.{u}) :
    Limits.IsColimit
      (Limits.BinaryCofan.mk (toTopPair.obj (addBasepoint.obj X)).hom (addBasepointInr X)) :=
  (TopCat.binaryCofanIsColimit (TopCat.of PUnit.{u + 1}) X).ofIsoColimit <|
    -- Both cocone points are `PUnit ⊕ X`. On the unique point of `PUnit`, `Sum.inl` and the
    -- constant map at the basepoint `Sum.inl PUnit.unit` agree, and on `X` both maps are `Sum.inr`.
    Limits.BinaryCofan.ext (Iso.refl _) (by ext ⟨⟩; rfl) (by ext; rfl)

/-- The inclusion `X ⟶ X₊` is natural in `X`. -/
@[reassoc]
lemma addBasepointInr_comp_addBasepoint_map {X Y : TopCat.{u}} (f : X ⟶ Y) :
    addBasepointInr X ≫ TopCat.ofHom (addBasepoint.map f).toContinuousMap =
      f ≫ addBasepointInr Y := by
  ext
  -- `Sum.map id f (Sum.inr x) = Sum.inr (f x)` holds by the definition of `Sum.map`.
  rfl

end BasedTopologicalSpace

end TauCeti
