/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Limits.Shapes.Multispan.Subdivision.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Coefficient transformations on a subdivided incidence diagram

A coefficient transformation pulls back along the subdivision projection. The
canonical diagram comparisons identify its components with the original face
and chamber maps, including the chamber maps on inserted identity faces.

Adapted from `Mei/CategoryTheory/Limits/Multispan/Subdivision/Morphism.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
The original source credits Codex and carries the notice
Copyright (c) 2026 Mei contributors. All rights reserved.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.MultispanShape.Subdivision

universe u v

variable {J : MultispanShape} (D : Subdivision J) {C : Type u} [Category.{v} C]
  {I I' : MultispanIndex J C}

/-- Pull a coefficient transformation back through the canonical subdivision
comparisons. Inserted identity faces use the corresponding chamber map. -/
def mapNatTrans (η : I.multispan ⟶ I'.multispan) :
    (D.index I).multispan ⟶ (D.index I').multispan :=
  (D.multispanIso I).hom ≫ Functor.whiskerLeft D.projection η ≫ (D.multispanIso I').inv

/-- The refined coefficient map factors through the projection and diagram comparisons. -/
theorem mapNatTrans_def (η : I.multispan ⟶ I'.multispan) :
    D.mapNatTrans η = (D.multispanIso I).hom ≫
      Functor.whiskerLeft D.projection η ≫ (D.multispanIso I').inv := (rfl)

instance (η : I.multispan ⟶ I'.multispan) [IsIso η] : IsIso (D.mapNatTrans η) := by
  rw [mapNatTrans_def]
  infer_instance

/-- Subdivision preserves the identity coefficient transformation. -/
@[simp]
theorem mapNatTrans_id (I : MultispanIndex J C) :
    D.mapNatTrans (𝟙 I.multispan) = 𝟙 (D.index I).multispan := by
  simp only [mapNatTrans, Functor.whiskerLeft_id', Category.id_comp, Iso.hom_inv_id]

/-- Subdivision preserves composition of coefficient transformations. -/
@[simp]
theorem mapNatTrans_comp {I'' : MultispanIndex J C}
    (η : I.multispan ⟶ I'.multispan) (θ : I'.multispan ⟶ I''.multispan) :
    D.mapNatTrans (η ≫ θ) = D.mapNatTrans η ≫ D.mapNatTrans θ := by
  simp only [mapNatTrans, Functor.whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- Subdivision transports the inverse of a coefficient isomorphism to the inverse. -/
@[simp]
theorem inv_mapNatTrans (η : I.multispan ⟶ I'.multispan) [IsIso η] :
    inv (D.mapNatTrans η) = D.mapNatTrans (inv η) := by
  symm
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← mapNatTrans_comp, IsIso.hom_inv_id, mapNatTrans_id]

/-- A copied original face carries its original coefficient transformation. -/
@[simp]
theorem mapNatTrans_app_left_inl (η : I.multispan ⟶ I'.multispan)
    (b : J.L) (a : D.faces b) :
    (D.mapNatTrans η).app (.left (.inl ⟨b, a⟩)) = η.app (.left b) := by
  simp only [mapNatTrans, NatTrans.comp_app, multispanIso_hom_app,
    multispanIso_inv_app, Functor.whiskerLeft_app]
  -- The copied coefficient objects are definitionally the original face objects.
  change 𝟙 _ ≫ η.app (.left b) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- An inserted identity face carries the old chamber transformation. -/
@[simp]
theorem mapNatTrans_app_left_inr (η : I.multispan ⟶ I'.multispan)
    (j : J.R) (e : D.edges j) :
    (D.mapNatTrans η).app (.left (.inr ⟨j, e⟩)) = η.app (.right j) := by
  simp only [mapNatTrans, NatTrans.comp_app, multispanIso_hom_app,
    multispanIso_inv_app, Functor.whiskerLeft_app]
  -- An identity face has the same coefficient object as its original chamber.
  change 𝟙 _ ≫ η.app (.right j) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- Each chamber copy carries the old chamber transformation. -/
@[simp]
theorem mapNatTrans_app_right (η : I.multispan ⟶ I'.multispan)
    (j : J.R) (a : D.chambers j) :
    (D.mapNatTrans η).app (.right ⟨j, a⟩) = η.app (.right j) := by
  simp only [mapNatTrans, NatTrans.comp_app, multispanIso_hom_app,
    multispanIso_inv_app, Functor.whiskerLeft_app]
  -- Evaluation at a chamber copy retains the original chamber object.
  change 𝟙 _ ≫ η.app (.right j) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

end CategoryTheory.Limits.MultispanShape.Subdivision
