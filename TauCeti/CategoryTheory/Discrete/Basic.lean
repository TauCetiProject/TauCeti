/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Discrete categories

Basic facts about the class `CategoryTheory.IsDiscrete` of categories with at most one morphism
between two objects, which then are equal.

## Main declarations

* `CategoryTheory.IsDiscrete.nonempty_hom_iff`: in a discrete category there is a morphism
  between two objects if and only if they are equal.
* `CategoryTheory.IsDiscrete.naturality`, `CategoryTheory.IsDiscrete.natIso`: every family of
  morphisms between two functors out of a discrete category is natural, so a family of
  isomorphisms is a natural isomorphism.
* `CategoryTheory.isDiscrete_ulift`: lifting the objects of a discrete category to a larger
  universe gives a discrete category.
-/

public section

universe w' w v

namespace CategoryTheory

/-- In a discrete category there is a morphism between two objects if and only if they are
equal. -/
@[simp]
lemma IsDiscrete.nonempty_hom_iff {D : Type*} [Category* D] [IsDiscrete D] {x y : D} :
    Nonempty (x ⟶ y) ↔ x = y :=
  ⟨fun ⟨f⟩ ↦ IsDiscrete.eq_of_hom f, fun h ↦ ⟨eqToHom h⟩⟩

/-- Every family of morphisms between two functors out of a discrete category is natural. -/
lemma IsDiscrete.naturality {D E : Type*} [Category* D] [Category* E] [IsDiscrete D]
    {G H : D ⥤ E} (app : ∀ a, G.obj a ⟶ H.obj a) {a b : D} (φ : a ⟶ b) :
    G.map φ ≫ app b = app a ≫ H.map φ := by
  obtain rfl := IsDiscrete.eq_of_hom φ
  obtain rfl := Subsingleton.elim φ (𝟙 a)
  simp

/-- The natural isomorphism between two functors out of a discrete category given by a family of
isomorphisms; naturality is automatic by `IsDiscrete.naturality`. -/
@[expose] def IsDiscrete.natIso {D E : Type*} [Category* D] [Category* E] [IsDiscrete D]
    {G H : D ⥤ E} (app : ∀ a, G.obj a ≅ H.obj a) : G ≅ H :=
  NatIso.ofComponents app fun φ ↦ IsDiscrete.naturality (fun a ↦ (app a).hom) φ

@[simp]
lemma IsDiscrete.natIso_hom_app {D E : Type*} [Category* D] [Category* E] [IsDiscrete D]
    {G H : D ⥤ E} (app : ∀ a, G.obj a ≅ H.obj a) (a : D) :
    (IsDiscrete.natIso app).hom.app a = (app a).hom := by
  simp [IsDiscrete.natIso]

@[simp]
lemma IsDiscrete.natIso_inv_app {D E : Type*} [Category* D] [Category* E] [IsDiscrete D]
    {G H : D ⥤ E} (app : ∀ a, G.obj a ≅ H.obj a) (a : D) :
    (IsDiscrete.natIso app).inv.app a = (app a).inv := by
  simp [IsDiscrete.natIso]

attribute [local instance] uliftCategory

/-- Lifting the objects of a discrete category to a larger universe gives a discrete
category. -/
instance isDiscrete_ulift (D : Type w) [Category.{v} D] [IsDiscrete D] :
    IsDiscrete (ULift.{w'} D) where
  subsingleton X Y := inferInstanceAs (Subsingleton (X.down ⟶ Y.down))
  eq_of_hom f := ULift.ext (IsDiscrete.eq_of_hom (C := D) f)

end CategoryTheory
