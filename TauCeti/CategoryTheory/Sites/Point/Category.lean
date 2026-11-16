/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Isomorphisms of points of a site

In the category `CategoryTheory.GrothendieckTopology.Point J` of points of a site `(C, J)`, a
morphism `f : Φ₁ ⟶ Φ₂` is a natural transformation `f.hom : Φ₂.fiber ⟶ Φ₁.fiber` in the opposite
direction. This file records that `f` is an isomorphism if and only if `f.hom` is an isomorphism of
fibre functors (`isIso_iff_isIso_hom`), and that an isomorphism of points induces natural
isomorphisms of presheaf and sheaf fibre functors (`Iso.presheafFiber`, `Iso.sheafFiber`), as well
as `IsIso` instances on `f.presheafFiber` and `f.sheafFiber` whenever `IsIso f`.

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.isoMk`: build an isomorphism of points from an
  isomorphism of fibre functors.
* `CategoryTheory.GrothendieckTopology.Point.isIso_iff_isIso_hom`: a morphism of points is an
  isomorphism if and only if its underlying natural transformation of fibre functors is.
* `CategoryTheory.GrothendieckTopology.Point.Iso.presheafFiber`,
  `CategoryTheory.GrothendieckTopology.Point.Iso.sheafFiber`: the natural isomorphisms of presheaf
  and sheaf fibre functors induced by an isomorphism of points.
* `CategoryTheory.GrothendieckTopology.Point.Hom.isIso_presheafFiber`,
  `CategoryTheory.GrothendieckTopology.Point.Hom.isIso_sheafFiber`: an isomorphism of points
  induces isomorphisms of presheaf and sheaf fibre functors.

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §6.
-/

public section

universe w v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Construct an isomorphism of points `Φ₁ ≅ Φ₂` from an isomorphism `Φ₂.fiber ≅ Φ₁.fiber` of
their fibre functors. -/
def isoMk {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) : Φ₁ ≅ Φ₂ where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-- The underlying morphism of fibre functors of `isoMk e` is `e.hom`. -/
@[simp]
theorem isoMk_hom_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).hom.hom = e.hom :=
  (rfl)

/-- The underlying morphism of fibre functors of `(isoMk e).inv` is `e.inv`. -/
@[simp]
theorem isoMk_inv_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).inv.hom = e.inv :=
  (rfl)

/-- An isomorphism of points has an isomorphism of fibre functors underneath. -/
instance isIso_hom {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) [IsIso f] : IsIso f.hom :=
  ⟨(inv f).hom, by rw [← comp_hom, IsIso.inv_hom_id, id_hom],
    by rw [← comp_hom, IsIso.hom_inv_id, id_hom]⟩

/-- A morphism of points whose underlying natural transformation of fibre functors is an
isomorphism is itself an isomorphism. -/
theorem isIso_of_isIso_hom {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) [IsIso f.hom] : IsIso f :=
  ⟨⟨inv f.hom⟩, by ext; simp, by ext; simp⟩

/-- A morphism of points is an isomorphism if and only if its underlying natural transformation of
fibre functors is an isomorphism. -/
theorem isIso_iff_isIso_hom {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) : IsIso f ↔ IsIso f.hom :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isIso_of_isIso_hom f⟩

/-- The inverse of an isomorphism of points has underlying morphism `inv f.hom`. -/
@[simp]
theorem inv_hom {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) [IsIso f] : (inv f).hom = inv f.hom :=
  IsIso.eq_inv_of_hom_inv_id (by rw [← comp_hom, IsIso.inv_hom_id, id_hom])

section Fiber

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- On germs, the morphism `f.presheafFiber` induced by a morphism of points `f : Φ₁ ⟶ Φ₂` sends
the germ at `(X, x)` to the germ at `(X, f.hom.app X x)`. -/
@[reassoc, elementwise]
theorem Hom.toPresheafFiber_presheafFiber_app {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂)
    (X : C) (x : Φ₂.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ₂.toPresheafFiber X x P ≫ f.presheafFiber.app P =
      Φ₁.toPresheafFiber X (f.hom.app X x) P := by
  simp

/-- An isomorphism of points induces an isomorphism of presheaf fibre functors. -/
instance Hom.isIso_presheafFiber {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) [IsIso f] :
    IsIso (f.presheafFiber (A := A)) :=
  ⟨(inv f).presheafFiber,
    by rw [← presheafFiber_comp, IsIso.inv_hom_id, presheafFiber_id],
    by rw [← presheafFiber_comp, IsIso.hom_inv_id, presheafFiber_id]⟩

/-- An isomorphism of points induces an isomorphism of sheaf fibre functors. -/
instance Hom.isIso_sheafFiber {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) [IsIso f] :
    IsIso (f.sheafFiber (A := A)) :=
  ⟨(inv f).sheafFiber,
    by rw [← sheafFiber_comp, IsIso.inv_hom_id, sheafFiber_id],
    by rw [← sheafFiber_comp, IsIso.hom_inv_id, sheafFiber_id]⟩

/-- The natural isomorphism of presheaf fibre functors induced by an isomorphism of points. -/
noncomputable def Iso.presheafFiber {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    Φ₂.presheafFiber (A := A) ≅ Φ₁.presheafFiber where
  hom := e.hom.presheafFiber
  inv := e.inv.presheafFiber
  hom_inv_id := by rw [← Hom.presheafFiber_comp, e.inv_hom_id, Hom.presheafFiber_id]
  inv_hom_id := by rw [← Hom.presheafFiber_comp, e.hom_inv_id, Hom.presheafFiber_id]

/-- The forward direction of `Iso.presheafFiber e` is `e.hom.presheafFiber`. -/
@[simp]
theorem Iso.presheafFiber_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    (Iso.presheafFiber e (A := A)).hom = e.hom.presheafFiber :=
  (rfl)

/-- The inverse direction of `Iso.presheafFiber e` is `e.inv.presheafFiber`. -/
@[simp]
theorem Iso.presheafFiber_inv {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    (Iso.presheafFiber e (A := A)).inv = e.inv.presheafFiber :=
  (rfl)

/-- The natural isomorphism of sheaf fibre functors induced by an isomorphism of points. -/
noncomputable def Iso.sheafFiber {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    Φ₂.sheafFiber (A := A) ≅ Φ₁.sheafFiber where
  hom := e.hom.sheafFiber
  inv := e.inv.sheafFiber
  hom_inv_id := by rw [← Hom.sheafFiber_comp, e.inv_hom_id, Hom.sheafFiber_id]
  inv_hom_id := by rw [← Hom.sheafFiber_comp, e.hom_inv_id, Hom.sheafFiber_id]

/-- The forward direction of `Iso.sheafFiber e` is `e.hom.sheafFiber`. -/
@[simp]
theorem Iso.sheafFiber_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    (Iso.sheafFiber e (A := A)).hom = e.hom.sheafFiber :=
  (rfl)

/-- The inverse direction of `Iso.sheafFiber e` is `e.inv.sheafFiber`. -/
@[simp]
theorem Iso.sheafFiber_inv {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    (Iso.sheafFiber e (A := A)).inv = e.inv.sheafFiber :=
  (rfl)

/-- `Iso.sheafFiber` sends the identity isomorphism to the identity isomorphism. -/
@[simp]
theorem Iso.sheafFiber_refl (Φ : Point.{w} J) :
    Iso.sheafFiber (Iso.refl Φ) (A := A) = Iso.refl _ :=
  CategoryTheory.Iso.ext (Hom.sheafFiber_id Φ)

/-- `Iso.sheafFiber` reverses composition of isomorphisms of points. -/
@[simp]
theorem Iso.sheafFiber_trans {Φ₁ Φ₂ Φ₃ : Point.{w} J} (e₁ : Φ₁ ≅ Φ₂) (e₂ : Φ₂ ≅ Φ₃) :
    Iso.sheafFiber (e₁ ≪≫ e₂) (A := A) =
      Iso.sheafFiber e₂ ≪≫ Iso.sheafFiber e₁ :=
  CategoryTheory.Iso.ext (Hom.sheafFiber_comp e₁.hom e₂.hom)

/-- `Iso.sheafFiber` commutes with inversion of isomorphisms of points. -/
@[simp]
theorem Iso.sheafFiber_symm {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    Iso.sheafFiber e.symm (A := A) = (Iso.sheafFiber e).symm :=
  CategoryTheory.Iso.ext rfl

end Fiber

end CategoryTheory.GrothendieckTopology.Point
