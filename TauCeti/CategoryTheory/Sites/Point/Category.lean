/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Isomorphisms in the category of points of a site

For points `Φ₁, Φ₂` of a site `(C, J)`, a natural isomorphism `Φ₂.fiber ≅ Φ₁.fiber` of their fibre
functors gives an isomorphism `Φ₁ ≅ Φ₂` in `Point J` (`Point.isoMk`), which induces natural
isomorphisms of presheaf and sheaf fibre functors (`Point.presheafFiberIso`, `Point.sheafFiberIso`).

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §3.2.
-/

public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Φ₁ Φ₂ : Point.{w} J}

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

end CategoryTheory.GrothendieckTopology.Point
