/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Isomorphisms of points of a site

A morphism `f : Φ₁ ⟶ Φ₂` of points of a site is a natural transformation `Φ₂.fiber ⟶ Φ₁.fiber`
in the opposite direction (Mathlib's `CategoryTheory.GrothendieckTopology.Point.Hom`). It is an
isomorphism exactly when this natural transformation is one, and an isomorphism of points induces
isomorphisms of the fibre functors on presheaves and on sheaves, since these fibre functors are
contravariantly functorial in the point.

For points `Φ₁, Φ₂` of a site `(C, J)`, a natural isomorphism `Φ₂.fiber ≅ Φ₁.fiber` of their fibre
functors gives an isomorphism `Φ₁ ≅ Φ₂` in `Point J` (`Point.isoMk`), which induces natural
isomorphisms of presheaf and sheaf fibre functors (`Point.presheafFiberIso`, `Point.sheafFiberIso`).

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.isIso_iff_isIso_hom`: a morphism of points is an
  isomorphism if and only if its natural transformation of fibre functors is.
* `CategoryTheory.GrothendieckTopology.Point.Hom.isIso_presheafFiber`,
  `CategoryTheory.GrothendieckTopology.Point.Hom.isIso_sheafFiber`: an isomorphism of points
  induces isomorphisms of fibres of presheaves and of sheaves.

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §3.2.
-/

public section

universe w v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism of points is an isomorphism if and only if the underlying natural transformation
of fibre functors is an isomorphism. -/
theorem isIso_iff_isIso_hom {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) : IsIso f ↔ IsIso f.hom := by
  refine ⟨fun _ ↦ ⟨(inv f).hom, ?_, ?_⟩, fun _ ↦ ⟨⟨inv f.hom⟩, ?_, ?_⟩⟩
  · rw [← comp_hom, IsIso.inv_hom_id, id_hom]
  · rw [← comp_hom, IsIso.hom_inv_id, id_hom]
  · ext1; simp
  · ext1; simp

section Iso

variable {Φ₁ Φ₂ : Point.{w} J}

/-- Construct an isomorphism `Φ₁ ≅ Φ₂` of points of `J` from a natural isomorphism
`Φ₂.fiber ≅ Φ₁.fiber` of their fibre functors. -/
def isoMk (e : Φ₂.fiber ≅ Φ₁.fiber) : Φ₁ ≅ Φ₂ where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩

@[simp]
lemma isoMk_hom_hom (e : Φ₂.fiber ≅ Φ₁.fiber) : (isoMk e).hom.hom = e.hom := (rfl)

@[simp]
lemma isoMk_inv_hom (e : Φ₂.fiber ≅ Φ₁.fiber) : (isoMk e).inv.hom = e.inv := (rfl)

/-- An isomorphism `Φ₁ ≅ Φ₂` of points induces a natural isomorphism of presheaf fibre functors. -/
noncomputable def presheafFiberIso (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A]
    [HasColimitsOfSize.{w, w} A] :
    Φ₁.presheafFiber (A := A) ≅ Φ₂.presheafFiber where
  hom := e.inv.presheafFiber
  inv := e.hom.presheafFiber
  hom_inv_id := by rw [← Hom.presheafFiber_comp, e.hom_inv_id, Hom.presheafFiber_id]
  inv_hom_id := by rw [← Hom.presheafFiber_comp, e.inv_hom_id, Hom.presheafFiber_id]

@[simp]
lemma presheafFiberIso_hom (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (presheafFiberIso e A).hom = e.inv.presheafFiber := (rfl)

@[simp]
lemma presheafFiberIso_inv (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (presheafFiberIso e A).inv = e.hom.presheafFiber := (rfl)

/-- An isomorphism `Φ₁ ≅ Φ₂` of points induces a natural isomorphism of sheaf fibre functors. -/
noncomputable def sheafFiberIso (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A]
    [HasColimitsOfSize.{w, w} A] :
    Φ₁.sheafFiber (A := A) ≅ Φ₂.sheafFiber :=
  Functor.isoWhiskerLeft _ (presheafFiberIso e A)

@[simp]
lemma sheafFiberIso_hom (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (sheafFiberIso e A).hom = Functor.whiskerLeft _ e.inv.presheafFiber := (rfl)

@[simp]
lemma sheafFiberIso_inv (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (sheafFiberIso e A).inv = Functor.whiskerLeft _ e.hom.presheafFiber := (rfl)

end Iso

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

namespace Hom

variable {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) [IsIso f]

/-- An isomorphism of points induces an isomorphism of the fibre functors on presheaves. -/
instance isIso_presheafFiber : IsIso (f.presheafFiber (A := A)) :=
  ⟨(inv f).presheafFiber, by rw [← presheafFiber_comp, IsIso.inv_hom_id, presheafFiber_id],
    by rw [← presheafFiber_comp, IsIso.hom_inv_id, presheafFiber_id]⟩

/-- An isomorphism of points induces an isomorphism of the fibre functors on sheaves. -/
instance isIso_sheafFiber : IsIso (f.sheafFiber (A := A)) :=
  Functor.isIso_whiskerLeft _ (f.presheafFiber (A := A))

end Hom

end CategoryTheory.GrothendieckTopology.Point
