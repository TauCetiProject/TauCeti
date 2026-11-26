/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Fibres of presheaves of types at a point of a site

Let `Φ` be a point of a site `(C, J)`. Two points of the fibre functor `Φ.fiber` come from a single
one, because its category of elements is cofiltered
(`CategoryTheory.GrothendieckTopology.Point.exists_fiber_map_eq_fiber_map_eq`). The fibre of the
product `U ↦ F₁(U) × F₂(U)` of two presheaves of types (Mathlib's
`CategoryTheory.FunctorToTypes.prod`) is the product of their fibres
(`CategoryTheory.GrothendieckTopology.Point.presheafFiberProdEquiv`), because taking fibres
preserves finite limits.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)

/-- Two points of the fibre functor of `Φ` both come from a single one. -/
theorem exists_fiber_map_eq_fiber_map_eq {X Y : C} (x : Φ.fiber.obj X) (y : Φ.fiber.obj Y) :
    ∃ (Z : C) (z : Φ.fiber.obj Z) (f : Z ⟶ X) (g : Z ⟶ Y),
      Φ.fiber.map f z = x ∧ Φ.fiber.map g z = y := by
  let a := Φ.fiber.elementsMk X x
  let b := Φ.fiber.elementsMk Y y
  exact ⟨(IsCofiltered.min a b).obj, (IsCofiltered.min a b).val, (IsCofiltered.minToLeft a b).hom,
    (IsCofiltered.minToRight a b).hom, (IsCofiltered.minToLeft a b).map_val,
    (IsCofiltered.minToRight a b).map_val⟩

variable [LocallySmall.{w} C] (F₁ F₂ : Cᵒᵖ ⥤ Type w)

/-- **The fibre of a product of presheaves of types is the product of the fibres**, because
taking fibres preserves finite limits. -/
noncomputable def presheafFiberProdEquiv :
    Φ.presheafFiber.obj (FunctorToTypes.prod F₁ F₂) ≃
      Φ.presheafFiber.obj F₁ × Φ.presheafFiber.obj F₂ :=
  (IsLimit.conePointUniqueUpToIso
    (mapIsLimitOfPreservesOfIsLimit Φ.presheafFiber _ _ (FunctorToTypes.binaryProductLimit _ _))
    (Types.binaryProductLimit _ _)).toEquiv

/-- The components of `presheafFiberProdEquiv` are the maps of fibres induced by the two
projections. -/
theorem presheafFiberProdEquiv_apply (p : Φ.presheafFiber.obj (FunctorToTypes.prod F₁ F₂)) :
    Φ.presheafFiberProdEquiv F₁ F₂ p =
      (Φ.presheafFiber.map FunctorToTypes.prod.fst p,
        Φ.presheafFiber.map FunctorToTypes.prod.snd p) := by
  have h := fun j ↦ ConcreteCategory.congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp
    (mapIsLimitOfPreservesOfIsLimit Φ.presheafFiber _ _ (FunctorToTypes.binaryProductLimit F₁ F₂))
    (Types.binaryProductLimit (Φ.presheafFiber.obj F₁) (Φ.presheafFiber.obj F₂)) j) p
  exact Prod.ext (h ⟨.left⟩) (h ⟨.right⟩)

/-- On germs, `presheafFiberProdEquiv` takes the germs of the two components. -/
@[simp]
theorem presheafFiberProdEquiv_toPresheafFiber (X : C) (x : Φ.fiber.obj X)
    (a : (FunctorToTypes.prod F₁ F₂).obj (op X)) :
    Φ.presheafFiberProdEquiv F₁ F₂ (Φ.toPresheafFiber X x (FunctorToTypes.prod F₁ F₂) a) =
      (Φ.toPresheafFiber X x F₁ a.1, Φ.toPresheafFiber X x F₂ a.2) := by
  rw [presheafFiberProdEquiv_apply, toPresheafFiber_naturality_apply,
    toPresheafFiber_naturality_apply, FunctorToTypes.prod.fst_app, FunctorToTypes.prod.snd_app,
    TypeCat.ofHom_apply, TypeCat.ofHom_apply]

end CategoryTheory.GrothendieckTopology.Point
