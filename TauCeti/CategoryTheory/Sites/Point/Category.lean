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

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.isIso_iff_isIso_hom`: a morphism of points is an
  isomorphism if and only if its natural transformation of fibre functors is.
* `CategoryTheory.GrothendieckTopology.Point.Hom.isIso_presheafFiber`,
  `CategoryTheory.GrothendieckTopology.Point.Hom.isIso_sheafFiber`: an isomorphism of points
  induces isomorphisms of fibres of presheaves and of sheaves.
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
