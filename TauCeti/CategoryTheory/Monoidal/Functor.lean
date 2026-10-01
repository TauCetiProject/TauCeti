/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Lax monoidal functors: tensorator squares and transport

The tensorator of a lax monoidal functor is natural in its right argument, giving a
square between left tensoring and the functor.

A lax monoidal structure transports along a natural isomorphism of functors
(`CategoryTheory.Functor.LaxMonoidal.transport`), in the same way as Mathlib's
`CategoryTheory.Functor.Monoidal.transport` transports a monoidal structure. This is how a
functor isomorphic to a composite of lax monoidal functors inherits a lax monoidal structure.
-/

public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The natural tensorator square for left tensoring by `A` under a lax monoidal functor. -/
def laxCommTensorLeft (F : C ⥤ D) [F.LaxMonoidal] (A : C) :
    TwoSquare F (MonoidalCategory.tensorLeft A)
      (MonoidalCategory.tensorLeft (F.obj A)) F :=
  .mk _ _ _ _ { app := fun B => Functor.LaxMonoidal.μ F A B
                naturality := fun _ _ f => Functor.LaxMonoidal.μ_natural_right F A f }

/-- The component of the tensorator square is the tensorator. -/
@[simp]
theorem laxCommTensorLeft_app (F : C ⥤ D) [F.LaxMonoidal] (A B : C) :
    (laxCommTensorLeft F A).app B = Functor.LaxMonoidal.μ F A B := by
  unfold laxCommTensorLeft
  rfl

namespace LaxMonoidal

open MonoidalCategory

/-- Transport a lax monoidal structure along a natural isomorphism of functors. This is the lax
analogue of Mathlib's `CategoryTheory.Functor.Monoidal.transport`. -/
@[instance_reducible]
def transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : G.LaxMonoidal :=
  ofTensorHom (ε F ≫ i.hom.app (𝟙_ C))
    (fun X Y ↦ (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y))
    (fun f g ↦ by
      rw [tensorHom_comp_tensorHom_assoc, i.inv.naturality, i.inv.naturality,
        ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, i.hom.naturality, Category.assoc,
        Category.assoc])
    (fun X Y Z ↦ by
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp, ← i.hom.naturality]
      have hl : ((i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y) ⊗ₘ i.inv.app Z =
          ((i.inv.app X ⊗ₘ i.inv.app Y) ⊗ₘ i.inv.app Z) ≫ (μ F X Y ▷ F.obj Z) := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      have hr : i.inv.app X ⊗ₘ ((i.inv.app Y ⊗ₘ i.inv.app Z) ≫ μ F Y Z) =
          (i.inv.app X ⊗ₘ (i.inv.app Y ⊗ₘ i.inv.app Z)) ≫ (F.obj X ◁ μ F Y Z) := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      rw [hl, hr, Category.assoc, Category.assoc, LaxMonoidal.associativity_assoc,
        associator_naturality_assoc])
    (fun X ↦ by
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp, ← i.hom.naturality]
      have h : ε F ⊗ₘ i.inv.app X = (𝟙_ D ◁ i.inv.app X) ≫ (ε F ▷ F.obj X) := by
        rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
          Category.id_comp]
      rw [h, Category.assoc, ← LaxMonoidal.left_unitality_assoc, leftUnitor_naturality_assoc,
        Iso.inv_hom_id_app, Category.comp_id])
    (fun X ↦ by
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp, ← i.hom.naturality]
      have h : i.inv.app X ⊗ₘ ε F = (i.inv.app X ▷ 𝟙_ D) ≫ (F.obj X ◁ ε F) := by
        rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
          Category.id_comp]
      rw [h, Category.assoc, ← LaxMonoidal.right_unitality_assoc, rightUnitor_naturality_assoc,
        Iso.inv_hom_id_app, Category.comp_id])

/-- The unit of the transported lax monoidal structure. -/
@[reassoc]
lemma transport_ε {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : letI := transport i
    ε G = ε F ≫ i.hom.app (𝟙_ C) :=
  (rfl)

/-- The tensorator of the transported lax monoidal structure. -/
@[reassoc]
lemma transport_μ {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y) :=
  (rfl)

end LaxMonoidal

end CategoryTheory.Functor
