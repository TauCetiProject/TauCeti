/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Monoid objects, monoidal functors and internal Homs in a monoidal full subcategory

If `P` is a monoidal property of objects of a monoidal category `C`, a monoid object in the full
monoidal subcategory of `P` is the same as a monoid object of `C` whose underlying object satisfies
`P` (`CategoryTheory.ObjectProperty.monFullSubcategoryEquivalence`).

If `P` is a monoidal property of objects of a closed monoidal category `C` that is closed under
internal Homs, Mathlib makes the full subcategory of `P` closed monoidal
(`CategoryTheory.ObjectProperty.fullMonoidalClosedSubcategory`), with internal Homs computed in
`C` (`CategoryTheory.ObjectProperty.ihom_obj`, `CategoryTheory.ObjectProperty.ihom_map_hom`).
This file records that its evaluation, coevaluation and precomposition maps are also those of
`C`, so that computations with internal Homs in the subcategory reduce to computations in `C`.

A strong (resp. braided) monoidal functor `F : D ⥤ C` whose values satisfy `P` lifts to a strong
(resp. braided) monoidal functor `P.lift F hF` into the full monoidal subcategory, with the
comparison isomorphisms of `F` (`CategoryTheory.ObjectProperty.monoidalLift`,
`CategoryTheory.ObjectProperty.braidedLift`).

## Main declarations

* `CategoryTheory.ObjectProperty.monFullSubcategoryEquivalence`: monoid objects in the full
  monoidal subcategory of `P` are monoid objects of `C` whose underlying object satisfies `P`;
* `CategoryTheory.ObjectProperty.monoidalLift` and `CategoryTheory.ObjectProperty.braidedLift`:
  lifts of monoidal and braided functors into the full monoidal subcategory;
* `CategoryTheory.ObjectProperty.ihom_ev_app_hom` and
  `CategoryTheory.ObjectProperty.ihom_coev_app_hom`: evaluation and coevaluation;
* `CategoryTheory.ObjectProperty.pre_app_hom`: precomposition with a morphism of the
  subcategory.
-/

public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory MonoidalClosed
open scoped MonObj

universe v u

section Mon

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]

/-- Monoid objects in the full monoidal subcategory of `P` are the monoid objects of `C` whose
underlying object satisfies `P`. Both functors keep the underlying objects, units,
multiplications and morphisms.

The body is exposed so that the functors reduce on objects in the types of the characteristic
equations of constructions built from them. -/
@[expose]
def monFullSubcategoryEquivalence :
    Mon P.FullSubcategory ≌ (P.inverseImage (Mon.forget C)).FullSubcategory where
  functor :=
    { obj A := by
        letI : MonObj A.X.obj := {
          one := η[A.X].hom
          mul := μ[A.X].hom
          one_mul := congrArg (fun f ↦ f.hom) (MonObj.one_mul A.X)
          mul_one := congrArg (fun f ↦ f.hom) (MonObj.mul_one A.X)
          mul_assoc := congrArg (fun f ↦ f.hom) (MonObj.mul_assoc A.X) }
        exact ⟨Mon.mk A.X.obj, A.X.property⟩
      map f := by
        refine ObjectProperty.homMk (Mon.Hom.mk' f.hom.hom ?_ ?_)
        · exact congrArg (fun g ↦ g.hom) (IsMonHom.one_hom f.hom)
        · exact congrArg (fun g ↦ g.hom) (IsMonHom.mul_hom f.hom)
      map_id A := by
        apply ObjectProperty.hom_ext
        apply Mon.Hom.ext
        exact congrArg (fun f ↦ f.hom) (Mon.id_hom A)
      map_comp f g := by
        apply ObjectProperty.hom_ext
        apply Mon.Hom.ext
        exact congrArg (fun h ↦ h.hom) (Mon.comp_hom f g) }
  inverse :=
    { obj A := by
        let E : P.FullSubcategory := ⟨A.obj.X, A.property⟩
        letI : MonObj E := {
          one := ObjectProperty.homMk η[A.obj.X]
          mul := ObjectProperty.homMk μ[A.obj.X]
          one_mul := by
            apply ObjectProperty.hom_ext
            exact MonObj.one_mul A.obj.X
          mul_one := by
            apply ObjectProperty.hom_ext
            exact MonObj.mul_one A.obj.X
          mul_assoc := by
            apply ObjectProperty.hom_ext
            exact MonObj.mul_assoc A.obj.X }
        exact Mon.mk E
      map f := by
        refine Mon.Hom.mk' (ObjectProperty.homMk f.hom.hom) ?_ ?_
        · apply ObjectProperty.hom_ext
          exact IsMonHom.one_hom f.hom.hom
        · apply ObjectProperty.hom_ext
          exact IsMonHom.mul_hom f.hom.hom
      map_id A := by
        apply Mon.Hom.ext
        apply ObjectProperty.hom_ext
        exact Mon.id_hom A.obj
      map_comp f g := by
        apply Mon.Hom.ext
        apply ObjectProperty.hom_ext
        exact Mon.comp_hom f.hom g.hom }
  unitIso := NatIso.ofComponents (fun (A : Mon P.FullSubcategory) ↦ Mon.mkIso (Iso.refl _))
    fun _ ↦ Mon.Hom.ext (by cat_disch)
  counitIso := NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (Mon.mkIso (Iso.refl _)))
    fun _ ↦ ObjectProperty.hom_ext _ (Mon.Hom.ext (by cat_disch))
  functor_unitIso_comp _ := ObjectProperty.hom_ext _ (Mon.Hom.ext (by simp))

variable {P}

/-- The functor of `monFullSubcategoryEquivalence` keeps the underlying object. -/
@[simp]
theorem monFullSubcategoryEquivalence_functor_obj_obj_X (A : Mon P.FullSubcategory) :
    (P.monFullSubcategoryEquivalence.functor.obj A).obj.X = A.X.obj :=
  (rfl)

/-- The functor of `monFullSubcategoryEquivalence` keeps the unit. -/
@[simp]
theorem monFullSubcategoryEquivalence_functor_obj_obj_one (A : Mon P.FullSubcategory) :
    η[(P.monFullSubcategoryEquivalence.functor.obj A).obj.X] = η[A.X].hom :=
  (rfl)

/-- The functor of `monFullSubcategoryEquivalence` keeps the multiplication. -/
@[simp]
theorem monFullSubcategoryEquivalence_functor_obj_obj_mul (A : Mon P.FullSubcategory) :
    μ[(P.monFullSubcategoryEquivalence.functor.obj A).obj.X] = μ[A.X].hom :=
  (rfl)

/-- The functor of `monFullSubcategoryEquivalence` keeps the underlying morphism. -/
@[simp]
theorem monFullSubcategoryEquivalence_functor_map_hom_hom {A B : Mon P.FullSubcategory}
    (f : A ⟶ B) : (P.monFullSubcategoryEquivalence.functor.map f).hom.hom = f.hom.hom :=
  (rfl)

/-- The inverse of `monFullSubcategoryEquivalence` keeps the underlying object. -/
@[simp]
theorem monFullSubcategoryEquivalence_inverse_obj_X_obj
    (A : (P.inverseImage (Mon.forget C)).FullSubcategory) :
    (P.monFullSubcategoryEquivalence.inverse.obj A).X.obj = A.obj.X :=
  (rfl)

/-- The inverse of `monFullSubcategoryEquivalence` keeps the unit. -/
@[simp]
theorem monFullSubcategoryEquivalence_inverse_obj_one_hom
    (A : (P.inverseImage (Mon.forget C)).FullSubcategory) :
    η[(P.monFullSubcategoryEquivalence.inverse.obj A).X].hom = η[A.obj.X] :=
  (rfl)

/-- The inverse of `monFullSubcategoryEquivalence` keeps the multiplication. -/
@[simp]
theorem monFullSubcategoryEquivalence_inverse_obj_mul_hom
    (A : (P.inverseImage (Mon.forget C)).FullSubcategory) :
    μ[(P.monFullSubcategoryEquivalence.inverse.obj A).X].hom = μ[A.obj.X] :=
  (rfl)

/-- The inverse of `monFullSubcategoryEquivalence` keeps the underlying morphism. -/
@[simp]
theorem monFullSubcategoryEquivalence_inverse_map_hom_hom
    {A B : (P.inverseImage (Mon.forget C)).FullSubcategory} (f : A ⟶ B) :
    (P.monFullSubcategoryEquivalence.inverse.map f).hom.hom = f.hom.hom :=
  (rfl)

/-- The components of the unit of `monFullSubcategoryEquivalence` are identities. -/
@[simp]
theorem monFullSubcategoryEquivalence_unitIso_hom_app (A : Mon P.FullSubcategory) :
    P.monFullSubcategoryEquivalence.unitIso.hom.app A = 𝟙 _ :=
  Mon.Hom.ext (rfl)

/-- The components of the inverse unit of `monFullSubcategoryEquivalence` are identities. -/
@[simp]
theorem monFullSubcategoryEquivalence_unitIso_inv_app (A : Mon P.FullSubcategory) :
    P.monFullSubcategoryEquivalence.unitIso.inv.app A = 𝟙 _ :=
  Mon.Hom.ext (rfl)

/-- The components of the counit of `monFullSubcategoryEquivalence` are identities. -/
@[simp]
theorem monFullSubcategoryEquivalence_counitIso_hom_app
    (A : (P.inverseImage (Mon.forget C)).FullSubcategory) :
    P.monFullSubcategoryEquivalence.counitIso.hom.app A = 𝟙 _ :=
  ObjectProperty.hom_ext _ (Mon.Hom.ext (rfl))

/-- The components of the inverse counit of `monFullSubcategoryEquivalence` are identities. -/
@[simp]
theorem monFullSubcategoryEquivalence_counitIso_inv_app
    (A : (P.inverseImage (Mon.forget C)).FullSubcategory) :
    P.monFullSubcategoryEquivalence.counitIso.inv.app A = 𝟙 _ :=
  ObjectProperty.hom_ext _ (Mon.Hom.ext (rfl))

end Mon

section lift

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]
  {D : Type*} [Category* D] [MonoidalCategory D] (F : D ⥤ C) (hF : ∀ X, P (F.obj X))

/-- The lift through the monoidal full subcategory of `P` of a strong monoidal functor `F` whose
values satisfy `P` is strong monoidal, with the comparison isomorphisms of `F`. -/
instance monoidalLift [F.Monoidal] : (P.lift F hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := P.isoMk (Functor.Monoidal.εIso F)
      μIso X Y := P.isoMk (Functor.Monoidal.μIso F X Y)
      μIso_hom_natural_left f X := P.hom_ext (Functor.LaxMonoidal.μ_natural_left F f X)
      μIso_hom_natural_right X f := P.hom_ext (Functor.LaxMonoidal.μ_natural_right F X f)
      associativity X Y Z := P.hom_ext (Functor.LaxMonoidal.associativity F X Y Z)
      left_unitality X := P.hom_ext (Functor.LaxMonoidal.left_unitality F X)
      right_unitality X := P.hom_ext (Functor.LaxMonoidal.right_unitality F X) }

/-- The lift through the braided monoidal full subcategory of `P` of a braided functor whose
values satisfy `P` is braided, with the comparison isomorphisms of `F`. -/
instance braidedLift [BraidedCategory C] [BraidedCategory D] [F.Braided] :
    (P.lift F hF).Braided where
  braided X Y := P.hom_ext (Functor.LaxBraided.braided (F := F) X Y)

variable [F.Monoidal]

/-- The unit comparison of the lift of `F` is that of `F`. -/
@[simp]
lemma lift_ε_hom : (Functor.LaxMonoidal.ε (P.lift F hF)).hom = Functor.LaxMonoidal.ε F :=
  (rfl)

/-- The inverse unit comparison of the lift of `F` is that of `F`. -/
@[simp]
lemma lift_η_hom : (Functor.OplaxMonoidal.η (P.lift F hF)).hom = Functor.OplaxMonoidal.η F :=
  (rfl)

/-- The tensor comparison of the lift of `F` is that of `F`. -/
@[simp]
lemma lift_μ_hom (X Y : D) :
    (Functor.LaxMonoidal.μ (P.lift F hF) X Y).hom = Functor.LaxMonoidal.μ F X Y :=
  (rfl)

/-- The inverse tensor comparison of the lift of `F` is that of `F`. -/
@[simp]
lemma lift_δ_hom (X Y : D) :
    (Functor.OplaxMonoidal.δ (P.lift F hF) X Y).hom = Functor.OplaxMonoidal.δ F X Y :=
  (rfl)

end lift

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (P : ObjectProperty C) [P.IsMonoidal] [P.IsMonoidalClosed]

/-- Evaluation in the closed monoidal full subcategory is evaluation in the ambient category. -/
@[simp]
theorem ihom_ev_app_hom (X Y : P.FullSubcategory) :
    ((ihom.ev X).app Y).hom = (ihom.ev X.obj).app Y.obj :=
  (rfl)

/-- Coevaluation in the closed monoidal full subcategory is coevaluation in the ambient
category. -/
@[simp]
theorem ihom_coev_app_hom (X Y : P.FullSubcategory) :
    ((ihom.coev X).app Y).hom = (ihom.coev X.obj).app Y.obj :=
  (rfl)

variable {P}

/-- Precomposition of internal Homs in the closed monoidal full subcategory is precomposition in
the ambient category. -/
@[simp]
theorem pre_app_hom {X X' : P.FullSubcategory} (f : X ⟶ X') (Y : P.FullSubcategory) :
    ((pre f).app Y).hom = (pre f.hom).app Y.obj := by
  -- Both maps are the transpose of `f ▷ _` followed by evaluation in `C`.
  refine ((eq_curry_iff (A := X.obj) _ _).mpr ?_).trans
    ((curry_eq_iff _ _).mpr (uncurry_pre f.hom Y.obj).symm)
  exact congrArg InducedCategory.Hom.hom (id_tensor_pre_app_comp_ev f Y)

end CategoryTheory.ObjectProperty
