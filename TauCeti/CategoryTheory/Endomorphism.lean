/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Units of the endomorphism monoid of a functor

A unit `z` of the monoid `End F` of natural endomorphisms of a functor `F : C ⥤ D` acts on every
object `X` by an isomorphism: its component `z.val.asHom.app X` has inverse
`z⁻¹.val.asHom.app X`. For `F = 𝟭 C` these are the units of the centre `CatCenter C`.
Evaluation at `X` is a group homomorphism `(End F)ˣ →* Aut (F.obj X)`
(`CategoryTheory.NatTrans.unitsEndEval`).

The action `Functor.mapAut` of a composite functor on automorphisms is the composite of the
actions (`CategoryTheory.Functor.comp_mapAut`).
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}

/-- The component of `z⁻¹` at `X` is a left inverse of that of `z`. -/
@[reassoc (attr := simp)]
lemma inv_app_comp_app (z : (End F)ˣ) (X : C) :
    z⁻¹.val.asHom.app X ≫ z.val.asHom.app X = 𝟙 (F.obj X) := by
  rw [← NatTrans.comp_app, ← End.mul_asHom, z.mul_inv, End.one_asHom, NatTrans.id_app]

/-- The component of `z⁻¹` at `X` is a right inverse of that of `z`. -/
@[reassoc (attr := simp)]
lemma app_comp_inv_app (z : (End F)ˣ) (X : C) :
    z.val.asHom.app X ≫ z⁻¹.val.asHom.app X = 𝟙 (F.obj X) := by
  rw [← NatTrans.comp_app, ← End.mul_asHom, z.inv_mul, End.one_asHom, NatTrans.id_app]

/-- The component of a unit of `End F` at every object is an isomorphism. -/
instance isIso_app (z : (End F)ˣ) (X : C) : IsIso (z.val.asHom.app X) :=
  ⟨⟨_, app_comp_inv_app z X, inv_app_comp_app z X⟩⟩

/-- The component of the inverse of a unit of `End F` is the inverse of its component. -/
lemma inv_val_app (z : (End F)ˣ) (X : C) : z⁻¹.val.asHom.app X = inv (z.val.asHom.app X) :=
  (IsIso.inv_eq_of_hom_inv_id (app_comp_inv_app z X)).symm

variable (F) in
/-- **Evaluation of a unit of `End F` at `X`**, as a group homomorphism `(End F)ˣ →* Aut (F.obj X)`:
Mathlib's `Aut.unitsEndEquivAut` at `F`, followed by the component at `X` of a natural
automorphism. -/
def unitsEndEval (X : C) : (End F)ˣ →* Aut (F.obj X) :=
  (((evaluation C D).obj X).mapAut F).comp (Aut.unitsEndEquivAut F).toMonoidHom

/-- The automorphism of `F.obj X` given by a unit `z` of `End F` is the component of `z`. -/
@[simp]
lemma unitsEndEval_asIso_hom (X : C) (z : (End F)ˣ) :
    (unitsEndEval F X z).asIso.hom = z.val.asHom.app X :=
  (rfl)

/-- The inverse of the automorphism given by `z` is the component of `z⁻¹`. -/
@[simp]
lemma unitsEndEval_asIso_inv (X : C) (z : (End F)ˣ) :
    (unitsEndEval F X z).asIso.inv = z⁻¹.val.asHom.app X :=
  (rfl)

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type*} [Category* E]

/-- The action of a composite functor on automorphisms is the composite of the actions. -/
theorem comp_mapAut (G : C ⥤ D) (H : D ⥤ E) (y : C) (b : Aut y) :
    (G ⋙ H).mapAut y b = H.mapAut (G.obj y) (G.mapAut y b) :=
  Aut.ext (Iso.ext (by simp))

end CategoryTheory.Functor
