/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Isomorphisms of points of a site and of their fiber functors

Given two points `Φ₁` and `Φ₂` of a site `(C, J)`, this file provides:
* `CategoryTheory.GrothendieckTopology.Point.isoMk`: constructor for isomorphisms `Φ₁ ≅ Φ₂` in
  `Point.{w} J` from a natural isomorphism `Φ₂.fiber ≅ Φ₁.fiber` of fiber functors;
* `CategoryTheory.GrothendieckTopology.Point.presheafFiberIsoOfFiberIso` and
  `CategoryTheory.GrothendieckTopology.Point.sheafFiberIsoOfFiberIso`: natural isomorphisms between
  presheaf and sheaf fiber functors induced by a natural isomorphism `Φ₁.fiber ≅ Φ₂.fiber`.
-/

public section

universe w v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Constructor for isomorphisms in `Point.{w} J` from a natural isomorphism of fiber functors in
the contravariant direction. -/
def isoMk {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) : Φ₁ ≅ Φ₂ where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩

@[simp]
lemma isoMk_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).hom = ⟨e.hom⟩ :=
  (rfl)

@[simp]
lemma isoMk_inv {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).inv = ⟨e.inv⟩ :=
  (rfl)

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- Natural isomorphism between presheaf fiber functors induced by a natural isomorphism between
the fiber functors of two points. -/
noncomputable def presheafFiberIsoOfFiberIso {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) :
    Φ₁.presheafFiber (A := A) ≅ Φ₂.presheafFiber where
  hom := (Hom.mk e.hom).presheafFiber
  inv := (Hom.mk e.inv).presheafFiber
  hom_inv_id := by
    rw [← Hom.presheafFiber_comp (Hom.mk e.inv) (Hom.mk e.hom), ← Hom.presheafFiber_id]
    congr 1
    ext : 1
    exact e.hom_inv_id
  inv_hom_id := by
    rw [← Hom.presheafFiber_comp (Hom.mk e.hom) (Hom.mk e.inv), ← Hom.presheafFiber_id]
    congr 1
    ext : 1
    exact e.inv_hom_id

@[simp]
lemma presheafFiberIsoOfFiberIso_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁.fiber ≅ Φ₂.fiber) :
    (presheafFiberIsoOfFiberIso (A := A) e).hom = (Hom.mk e.hom).presheafFiber :=
  (rfl)

@[simp]
lemma presheafFiberIsoOfFiberIso_inv {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁.fiber ≅ Φ₂.fiber) :
    (presheafFiberIsoOfFiberIso (A := A) e).inv = (Hom.mk e.inv).presheafFiber :=
  (rfl)

@[reassoc]
lemma toPresheafFiber_presheafFiberIsoOfFiberIso_hom_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (X : C) (x : Φ₁.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ₁.toPresheafFiber X x P ≫ (presheafFiberIsoOfFiberIso (A := A) e).hom.app P =
      Φ₂.toPresheafFiber X (e.hom.app X x) P := by
  simp

@[reassoc]
lemma toPresheafFiber_presheafFiberIsoOfFiberIso_inv_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (X : C) (x : Φ₂.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ₂.toPresheafFiber X x P ≫ (presheafFiberIsoOfFiberIso (A := A) e).inv.app P =
      Φ₁.toPresheafFiber X (e.inv.app X x) P := by
  simp

/-- Natural isomorphism between sheaf fiber functors induced by a natural isomorphism between the
fiber functors of two points. -/
noncomputable def sheafFiberIsoOfFiberIso {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) :
    Φ₁.sheafFiber (A := A) ≅ Φ₂.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafFiberIsoOfFiberIso e)

@[simp]
lemma sheafFiberIsoOfFiberIso_hom_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (F : Sheaf J A) :
    (sheafFiberIsoOfFiberIso (A := A) e).hom.app F =
      (presheafFiberIsoOfFiberIso (A := A) e).hom.app F.obj :=
  (rfl)

@[simp]
lemma sheafFiberIsoOfFiberIso_inv_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (F : Sheaf J A) :
    (sheafFiberIsoOfFiberIso (A := A) e).inv.app F =
      (presheafFiberIsoOfFiberIso (A := A) e).inv.app F.obj :=
  (rfl)

end CategoryTheory.GrothendieckTopology.Point
