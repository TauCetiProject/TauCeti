/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import TauCeti.CategoryTheory.Monoidal.Pivotal.SquaredNorm

/-!
# The pivotalization of a rigid category

Let `C` be a right rigid monoidal category and `e : 𝟭 C ≅ doubleRightDualFunctor C ⋙
doubleRightDualFunctor C` a monoidal natural isomorphism from the identity to the fourth right
dual functor `X ↦ Xᘁᘁᘁᘁ`. The *pivotalization* `TauCeti.Pivotalization e` is the category of
square roots of `e`: its objects are pairs `(X, a)` of an object `X` of `C` and an isomorphism
`a : X ≅ Xᘁᘁ` whose square `a ≫ aᘁᘁ` is the component `e_X`, and its morphisms
`(X, a) ⟶ (Y, b)` are the morphisms `f : X ⟶ Y` with `f ≫ b = a ≫ fᘁᘁ`. Equivalently, it is the
full subcategory of Mathlib's `Endofunctor.Coalgebra (doubleRightDualFunctor C)` on the coalgebras
whose structure morphism is invertible with square `e`; it is defined directly, because the
monoidal structure below uses the tensor comparison of the double right dual functor, and Mathlib
has no monoidal structure on coalgebras of a lax monoidal endofunctor.

The pivotalization is a monoidal category: `(X, a) ⊗ (Y, b)` is `X ⊗ Y` with `a ⊗ b` followed by
the tensor comparison of the double right dual functor, and the unit is `𝟙_ C` with the unit
comparison; that the square of `a ⊗ b` is `e_{X ⊗ Y}` is the monoidality of `e`. It is right
rigid: the right dual of `(X, a)` is `(Xᘁ, (a⁻¹)ᘁ)`, with the evaluation and coevaluation of `C`.
Here the square of `(a⁻¹)ᘁ` is `(e_X⁻¹)ᘁ`, which is `e_{Xᘁ}` by the Freyd–Yetter identity
`CategoryTheory.Iso.hom_app_rightDual` for the monoidal isomorphism `e`. Finally the components
`a` form a monoidal natural isomorphism from the identity to the double right dual functor of the
pivotalization: this is its tautological pivotal structure, which also makes it rigid. The
forgetful functor to `C` is faithful and strict monoidal, and it computes the traces of morphisms
`X ⟶ Xᘁᘁ`, hence the dimensions and squared norms of the pivotalization.

For a fusion category, the Radford isomorphism of Etingof, Nikshych and Ostrik is a monoidal
isomorphism `e` of this kind. In characteristic other than two the pivotalization along it is a
spherical fusion category ([EGNO], Corollary 7.21.10), and since its forgetful functor preserves
squared norms, statements about the global dimension of pivotal fusion categories transfer through
it to fusion categories with no pivotal structure. This file builds the pivotalization along an
arbitrary monoidal `e`, and proves nothing specific to the Radford isomorphism.

## Main declarations

* `CategoryTheory.Iso.hom_app_rightDual`: a monoidal natural isomorphism `e` from the identity to
  the fourth right dual functor satisfies `e_{Xᘁ} = (e_X⁻¹)ᘁ`;
* `TauCeti.Pivotalization`: the pivotalization of `C` along `e`, with its faithful forgetful
  functor `TauCeti.Pivotalization.forget` and the constructor `TauCeti.Pivotalization.isoMk` for
  isomorphisms;
* the instances `MonoidalCategory (Pivotalization e)`, `(Pivotalization.forget e).Monoidal`,
  `RightRigidCategory (Pivotalization e)`, `RigidCategory (Pivotalization e)` and
  `PivotalCategory (Pivotalization e)`, whose structure is computed in `C` by the `simp` lemmas
  of this file;
* `TauCeti.Pivotalization.pivotalIso`: the tautological pivotal structure, with components
  `TauCeti.Pivotalization.pivotalIsoApp_hom_hom`;
* `TauCeti.Pivotalization.rightDim_hom`, `TauCeti.Pivotalization.leftDim_hom`,
  `TauCeti.Pivotalization.squaredNorm_hom` and `TauCeti.Pivotalization.squaredNorm_iso`: the
  dimensions and squared norms of the pivotalization are computed in `C`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *An analogue of Radford's S⁴ formula for finite tensor
  categories*, Int. Math. Res. Not. 2004, no. 54,
  [arXiv:math/0404504](https://arxiv.org/abs/math/0404504), §7
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], Definition 7.21.9
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The fourth right dual functor carries the evaluation of `(Y, Yᘁ)` to the evaluation of
`(Yᘁᘁᘁᘁ, Yᘁᘁᘁᘁᘁ)`, up to its tensor and unit comparisons. -/
theorem fourthRightDual_μ_comp_map_evaluation (Y : C) :
    μ (doubleRightDualFunctor C ⋙ doubleRightDualFunctor C) Yᘁ Y ≫
        (doubleRightDualFunctor C ⋙ doubleRightDualFunctor C).map (ε_ Y Yᘁ) =
      ε_ ((doubleRightDualFunctor C ⋙ doubleRightDualFunctor C).obj Y)
          ((doubleRightDualFunctor C ⋙ doubleRightDualFunctor C).obj Y)ᘁ ≫
        ε (doubleRightDualFunctor C ⋙ doubleRightDualFunctor C) := by
  have h₁ := doubleRightDualFunctor_μ_comp_map_evaluation Y
  have h₂ := doubleRightDualFunctor_μ_comp_map_evaluation ((doubleRightDualFunctor C).obj Y)
  simp only [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
    Category.assoc]
  -- The objects `(Yᘁᘁ)ᘁ` and `(Yᘁ)ᘁᘁ` agree only up to unfolding, so the steps are chained by
  -- `Eq.trans` rather than by rewriting.
  exact (congrArg (_ ≫ ·) ((doubleRightDualFunctor C).map_comp _ _).symm).trans
    ((congrArg (fun t => _ ≫ (doubleRightDualFunctor C).map t) h₁).trans
      ((congrArg (_ ≫ ·) ((doubleRightDualFunctor C).map_comp _ _)).trans
        (((Category.assoc _ _ _).symm.trans (h₂ =≫ _)).trans (Category.assoc _ _ _))))

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

variable (e : 𝟭 C ≅ doubleRightDualFunctor C ⋙ doubleRightDualFunctor C) [NatTrans.IsMonoidal e.hom]

/-- A monoidal natural isomorphism `e` from the identity to the fourth right dual functor carries
the evaluation of `(X, Xᘁ)` to the evaluation of `(Xᘁᘁᘁᘁ, Xᘁᘁᘁᘁᘁ)`. -/
theorem tensorHom_hom_app_comp_evaluation (X : C) :
    (e.hom.app Xᘁ ⊗ₘ e.hom.app X) ≫
        ε_ ((doubleRightDualFunctor C ⋙ doubleRightDualFunctor C).obj X)
          ((doubleRightDualFunctor C ⋙ doubleRightDualFunctor C).obj X)ᘁ = ε_ X Xᘁ := by
  rw [← cancel_mono (ε (doubleRightDualFunctor C ⋙ doubleRightDualFunctor C))]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (fourthRightDual_μ_comp_map_evaluation X).symm).trans ?_
  have hT := NatTrans.IsMonoidal.tensor (τ := e.hom) Xᘁ X
  have hU := NatTrans.IsMonoidal.unit (τ := e.hom)
  simp only [Functor.LaxMonoidal.id_μ, Functor.LaxMonoidal.id_ε, Category.id_comp] at hT hU
  exact (Category.assoc _ _ _).symm.trans
    ((hT.symm =≫ _).trans ((e.hom.naturality (ε_ X Xᘁ)).symm.trans (_ ≫= hU)))

/-- **The Freyd–Yetter identity for the fourth dual**: a monoidal natural isomorphism `e` from the
identity to the fourth right dual functor satisfies `e_{Xᘁ} = (e_X⁻¹)ᘁ`. -/
theorem hom_app_rightDual (X : C) : e.hom.app Xᘁ = (e.inv.app X)ᘁ := by
  refine ExactPairing.rightHom_ext
    (X := (doubleRightDualFunctor C ⋙ doubleRightDualFunctor C).obj X)
    (Y := ((doubleRightDualFunctor C ⋙ doubleRightDualFunctor C).obj X)ᘁ) ?_
  rw [rightAdjointMate_comp_evaluation, ← cancel_epi (Xᘁ ◁ e.hom.app X)]
  -- After cancelling `Xᘁ ◁ e_X`, the left side is `(e_{Xᘁ} ⊗ e_X) ≫ ε`; the objects
  -- `(Xᘁᘁᘁᘁ)ᘁ` and `(Xᘁ)ᘁᘁᘁᘁ` agree only up to unfolding, hence the `Eq.trans` chain.
  refine ((whisker_exchange_assoc _ _ _).trans ((tensorHom_def_assoc _ _ _).symm.trans
    (e.tensorHom_hom_app_comp_evaluation X))).trans ?_
  simp [← MonoidalCategory.whiskerLeft_comp_assoc]

end CategoryTheory.Iso

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The **pivotalization** of a right rigid monoidal category `C` along a natural isomorphism
`e : 𝟭 C ≅ doubleRightDualFunctor C ⋙ doubleRightDualFunctor C` from the identity to the fourth
right dual functor. An object is an object `X` of `C` with an isomorphism `a : X ≅ Xᘁᘁ` whose
square `a ≫ aᘁᘁ : X ⟶ Xᘁᘁᘁᘁ` is the component of `e` at `X`. -/
structure Pivotalization (e : 𝟭 C ≅ doubleRightDualFunctor C ⋙ doubleRightDualFunctor C) where
  /-- The underlying object. -/
  obj : C
  /-- The isomorphism of the underlying object with its double right dual. -/
  iso : obj ≅ (doubleRightDualFunctor C).obj obj
  /-- The square `iso ≫ isoᘁᘁ` of `iso` is the component of `e`. -/
  iso_hom_comp_map_iso_hom : iso.hom ≫ (doubleRightDualFunctor C).map iso.hom = e.hom.app obj


namespace Pivotalization

variable {e : 𝟭 C ≅ doubleRightDualFunctor C ⋙ doubleRightDualFunctor C}

attribute [reassoc] iso_hom_comp_map_iso_hom

/-- A morphism of the pivotalization is a morphism of underlying objects intertwining the
isomorphisms with the double right duals. -/
@[ext]
structure Hom (X Y : Pivotalization e) where
  /-- The underlying morphism. -/
  hom : X.obj ⟶ Y.obj
  /-- The underlying morphism intertwines `X.iso` with `Y.iso`. -/
  comm : hom ≫ Y.iso.hom = X.iso.hom ≫ (doubleRightDualFunctor C).map hom

attribute [reassoc] Hom.comm

/-- The category structure of the pivotalization, with composition and identities computed in
`C`. -/
instance : Category (Pivotalization e) where
  Hom := Hom
  id X := ⟨𝟙 X.obj, by rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, f.comm_assoc, CategoryTheory.Functor.map_comp]⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

/-- Morphisms of the pivotalization are determined by their underlying morphisms. -/
@[ext]
theorem hom_ext {X Y : Pivotalization e} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- The identity of the pivotalization is the identity of the underlying object. -/
@[simp]
theorem id_hom (X : Pivotalization e) : Hom.hom (𝟙 X) = 𝟙 X.obj :=
  (rfl)

/-- Composition in the pivotalization is composition of underlying morphisms. -/
@[simp]
theorem comp_hom {X Y Z : Pivotalization e} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  (rfl)

variable (e) in
/-- The forgetful functor from the pivotalization to `C`. -/
@[simps]
abbrev forget : Pivotalization e ⥤ C where
  obj X := X.obj
  map f := f.hom

/-- The forgetful functor from the pivotalization is faithful. -/
instance : (forget e).Faithful where
  map_injective h := hom_ext h

/-- An isomorphism of underlying objects intertwining the isomorphisms with the double right
duals is an isomorphism of the pivotalization. -/
@[simps]
def isoMk {X Y : Pivotalization e} (i : X.obj ≅ Y.obj)
    (h : i.hom ≫ Y.iso.hom = X.iso.hom ≫ (doubleRightDualFunctor C).map i.hom) : X ≅ Y where
  hom := ⟨i.hom, h⟩
  inv := ⟨i.inv, by
    rw [← cancel_epi i.hom, i.hom_inv_id_assoc, reassoc_of% h, ← CategoryTheory.Functor.map_comp,
      i.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]⟩
  hom_inv_id := hom_ext i.hom_inv_id
  inv_hom_id := hom_ext i.inv_hom_id

section Monoidal

/-- The isomorphism of `X ⊗ Y` with its double right dual: the tensor product of those of `X` and
`Y`, followed by the tensor comparison of the double right dual functor. -/
noncomputable abbrev tensorIso (X Y : Pivotalization e) :
    X.obj ⊗ Y.obj ≅ (doubleRightDualFunctor C).obj (X.obj ⊗ Y.obj) :=
  (X.iso ⊗ᵢ Y.iso) ≪≫ Functor.Monoidal.μIso (doubleRightDualFunctor C) X.obj Y.obj

/-- The tensor product of two morphisms of the pivotalization intertwines the isomorphisms of the
tensor products with their double right duals. -/
theorem tensorHom_comp_tensorIso_hom {X₁ Y₁ X₂ Y₂ : Pivotalization e} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (f.hom ⊗ₘ g.hom) ≫ (tensorIso Y₁ Y₂).hom =
      (tensorIso X₁ X₂).hom ≫ (doubleRightDualFunctor C).map (f.hom ⊗ₘ g.hom) := by
  simp only [Iso.trans_hom, tensorIso_hom, Functor.Monoidal.μIso_hom]
  rw [tensorHom_comp_tensorHom_assoc, f.comm, g.comm, ← tensorHom_comp_tensorHom_assoc,
    μ_natural, Category.assoc]

variable [NatTrans.IsMonoidal e.hom]

/-- The tensor product of objects of the pivotalization: `(X, a) ⊗ (Y, b)` is `X ⊗ Y` with the
isomorphism `tensorIso`. -/
noncomputable abbrev tensorObj (X Y : Pivotalization e) : Pivotalization e where
  obj := X.obj ⊗ Y.obj
  iso := tensorIso X Y
  iso_hom_comp_map_iso_hom := by
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) X.obj Y.obj
    simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Functor.LaxMonoidal.comp_μ] at h
    rw [h, Iso.trans_hom, tensorIso_hom, Functor.Monoidal.μIso_hom,
      CategoryTheory.Functor.map_comp, Category.assoc, ← μ_natural_assoc,
      tensorHom_comp_tensorHom_assoc, X.iso_hom_comp_map_iso_hom, Y.iso_hom_comp_map_iso_hom]

/-- The unit object of the pivotalization: `𝟙_ C` with the unit comparison of the double right
dual functor. -/
noncomputable abbrev tensorUnit : Pivotalization e where
  obj := 𝟙_ C
  iso := Functor.Monoidal.εIso (doubleRightDualFunctor C)
  iso_hom_comp_map_iso_hom := by
    simpa using (NatTrans.IsMonoidal.unit (τ := e.hom)).symm

/-- The associator of `C` intertwines the isomorphisms of the two bracketings of a triple tensor
product of objects of the pivotalization with their double right duals. -/
theorem associator_hom_comp_iso_hom (X Y Z : Pivotalization e) :
    (α_ X.obj Y.obj Z.obj).hom ≫ (tensorObj X (tensorObj Y Z)).iso.hom =
      (tensorObj (tensorObj X Y) Z).iso.hom ≫
        (doubleRightDualFunctor C).map (α_ X.obj Y.obj Z.obj).hom := by
  simp only [tensorObj, Iso.trans_hom, tensorIso_hom, Functor.Monoidal.μIso_hom]
  have h₁ : ((X.iso.hom ⊗ₘ Y.iso.hom) ≫ μ (doubleRightDualFunctor C) X.obj Y.obj) ⊗ₘ Z.iso.hom =
      ((X.iso.hom ⊗ₘ Y.iso.hom) ⊗ₘ Z.iso.hom) ≫ μ (doubleRightDualFunctor C) X.obj Y.obj ▷ _ := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have h₂ : X.iso.hom ⊗ₘ ((Y.iso.hom ⊗ₘ Z.iso.hom) ≫ μ (doubleRightDualFunctor C) Y.obj Z.obj) =
      (X.iso.hom ⊗ₘ (Y.iso.hom ⊗ₘ Z.iso.hom)) ≫ _ ◁ μ (doubleRightDualFunctor C) Y.obj Z.obj := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [h₁, h₂, Category.assoc, Category.assoc, Category.assoc, Functor.LaxMonoidal.associativity,
    associator_naturality_assoc]

/-- The left unitor of `C` intertwines the isomorphisms of `𝟙 ⊗ X` and of `X` with their double
right duals. -/
theorem leftUnitor_hom_comp_iso_hom (X : Pivotalization e) :
    (λ_ X.obj).hom ≫ X.iso.hom =
      (tensorObj tensorUnit X).iso.hom ≫ (doubleRightDualFunctor C).map (λ_ X.obj).hom := by
  simp only [tensorObj, tensorUnit, Iso.trans_hom, tensorIso_hom, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.εIso_hom]
  rw [tensorHom_def', Category.assoc, Category.assoc, ← Functor.LaxMonoidal.left_unitality,
    leftUnitor_naturality]

/-- The right unitor of `C` intertwines the isomorphisms of `X ⊗ 𝟙` and of `X` with their double
right duals. -/
theorem rightUnitor_hom_comp_iso_hom (X : Pivotalization e) :
    (ρ_ X.obj).hom ≫ X.iso.hom =
      (tensorObj X tensorUnit).iso.hom ≫ (doubleRightDualFunctor C).map (ρ_ X.obj).hom := by
  simp only [tensorObj, tensorUnit, Iso.trans_hom, tensorIso_hom, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.εIso_hom]
  rw [tensorHom_def, Category.assoc, Category.assoc, ← Functor.LaxMonoidal.right_unitality,
    rightUnitor_naturality]

/-- The tensor product, unit, associators and unitors of the pivotalization, computed in `C`. -/
noncomputable instance : MonoidalCategoryStruct (Pivotalization e) where
  tensorObj := tensorObj
  whiskerLeft X _ _ f := ⟨X.obj ◁ f.hom, by
    rw [← id_tensorHom]
    exact tensorHom_comp_tensorIso_hom (𝟙 X) f⟩
  whiskerRight f Y := ⟨f.hom ▷ Y.obj, by
    rw [← tensorHom_id]
    exact tensorHom_comp_tensorIso_hom f (𝟙 Y)⟩
  tensorHom f g := ⟨f.hom ⊗ₘ g.hom, tensorHom_comp_tensorIso_hom f g⟩
  tensorUnit := tensorUnit
  associator X Y Z := isoMk (α_ X.obj Y.obj Z.obj) (associator_hom_comp_iso_hom X Y Z)
  leftUnitor X := isoMk (λ_ X.obj) (leftUnitor_hom_comp_iso_hom X)
  rightUnitor X := isoMk (ρ_ X.obj) (rightUnitor_hom_comp_iso_hom X)

/-- The underlying object of a tensor product in the pivotalization. -/
@[simp]
theorem tensorObj_obj (X Y : Pivotalization e) : (X ⊗ Y).obj = X.obj ⊗ Y.obj :=
  (rfl)

/-- The isomorphism of a tensor product with its double right dual is `tensorIso`. -/
@[simp]
theorem tensorObj_iso (X Y : Pivotalization e) : (X ⊗ Y).iso = tensorIso X Y :=
  (rfl)

/-- The underlying object of the unit of the pivotalization is the unit of `C`. -/
@[simp]
theorem tensorUnit_obj : (𝟙_ (Pivotalization e)).obj = 𝟙_ C :=
  (rfl)

/-- The isomorphism of the unit with its double right dual is the unit comparison of the
double right dual functor. -/
@[simp]
theorem tensorUnit_iso :
    (𝟙_ (Pivotalization e)).iso = Functor.Monoidal.εIso (doubleRightDualFunctor C) :=
  (rfl)

/-- Left whiskering in the pivotalization is computed in `C`. -/
@[simp]
theorem whiskerLeft_hom (X : Pivotalization e) {Y₁ Y₂ : Pivotalization e} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).hom = X.obj ◁ f.hom :=
  (rfl)

/-- Right whiskering in the pivotalization is computed in `C`. -/
@[simp]
theorem whiskerRight_hom {X₁ X₂ : Pivotalization e} (f : X₁ ⟶ X₂) (Y : Pivotalization e) :
    (f ▷ Y).hom = f.hom ▷ Y.obj :=
  (rfl)

/-- The tensor product of morphisms of the pivotalization is computed in `C`. -/
@[simp]
theorem tensorHom_hom {X₁ Y₁ X₂ Y₂ : Pivotalization e} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).hom = f.hom ⊗ₘ g.hom :=
  (rfl)

/-- The associator of the pivotalization is that of `C`. -/
@[simp]
theorem associator_hom_hom (X Y Z : Pivotalization e) :
    (α_ X Y Z).hom.hom = (α_ X.obj Y.obj Z.obj).hom :=
  (rfl)

/-- The inverse associator of the pivotalization is that of `C`. -/
@[simp]
theorem associator_inv_hom (X Y Z : Pivotalization e) :
    (α_ X Y Z).inv.hom = (α_ X.obj Y.obj Z.obj).inv :=
  (rfl)

/-- The left unitor of the pivotalization is that of `C`. -/
@[simp]
theorem leftUnitor_hom_hom (X : Pivotalization e) : (λ_ X).hom.hom = (λ_ X.obj).hom :=
  (rfl)

/-- The inverse left unitor of the pivotalization is that of `C`. -/
@[simp]
theorem leftUnitor_inv_hom (X : Pivotalization e) : (λ_ X).inv.hom = (λ_ X.obj).inv :=
  (rfl)

/-- The right unitor of the pivotalization is that of `C`. -/
@[simp]
theorem rightUnitor_hom_hom (X : Pivotalization e) : (ρ_ X).hom.hom = (ρ_ X.obj).hom :=
  (rfl)

/-- The inverse right unitor of the pivotalization is that of `C`. -/
@[simp]
theorem rightUnitor_inv_hom (X : Pivotalization e) : (ρ_ X).inv.hom = (ρ_ X.obj).inv :=
  (rfl)

/-- The pivotalization is a monoidal category, with tensor products, unit, associators and
unitors computed in `C`. -/
noncomputable instance : MonoidalCategory (Pivotalization e) where
  tensorHom_def f g := hom_ext (tensorHom_def f.hom g.hom)
  id_tensorHom_id X Y := hom_ext (id_tensorHom_id X.obj Y.obj)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ :=
    hom_ext (tensorHom_comp_tensorHom f₁.hom f₂.hom g₁.hom g₂.hom)
  whiskerLeft_id X Y := hom_ext (MonoidalCategory.whiskerLeft_id X.obj Y.obj)
  id_whiskerRight X Y := hom_ext (id_whiskerRight X.obj Y.obj)
  associator_naturality f₁ f₂ f₃ := hom_ext (associator_naturality f₁.hom f₂.hom f₃.hom)
  leftUnitor_naturality f := hom_ext (leftUnitor_naturality f.hom)
  rightUnitor_naturality f := hom_ext (rightUnitor_naturality f.hom)
  pentagon W X Y Z := hom_ext (pentagon W.obj X.obj Y.obj Z.obj)
  triangle X Y := hom_ext (triangle X.obj Y.obj)

/-- The forgetful functor from the pivotalization to `C` is strict monoidal. -/
noncomputable instance : (forget e).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

/-- The unit comparison of the forgetful functor is the identity. -/
@[simp]
theorem forget_ε : ε (forget e) = 𝟙 (𝟙_ C) :=
  (rfl)

/-- The inverse unit comparison of the forgetful functor is the identity. -/
@[simp]
theorem forget_η : η (forget e) = 𝟙 (𝟙_ C) :=
  (rfl)

/-- The tensor comparison of the forgetful functor is the identity. -/
@[simp]
theorem forget_μ (X Y : Pivotalization e) : μ (forget e) X Y = 𝟙 (X.obj ⊗ Y.obj) :=
  (rfl)

/-- The inverse tensor comparison of the forgetful functor is the identity. -/
@[simp]
theorem forget_δ (X Y : Pivotalization e) : δ (forget e) X Y = 𝟙 (X.obj ⊗ Y.obj) :=
  (rfl)

end Monoidal

section Rigid

variable [NatTrans.IsMonoidal e.hom]

/-- The right dual of an object `(X, a)` of the pivotalization: `Xᘁ` with the mate
`(a⁻¹)ᘁ : Xᘁ ≅ Xᘁᘁᘁ` of the inverse of `a`. -/
noncomputable abbrev rightDualObj (X : Pivotalization e) : Pivotalization e where
  obj := X.objᘁ
  iso :=
    -- The implicit arguments are given so that the mates are taken between `X.obj` and
    -- `(doubleRightDualFunctor C).obj X.obj`, rather than between unfoldings of these objects.
    { hom := @rightAdjointMate C _ _ ((doubleRightDualFunctor C).obj X.obj) X.obj _ _ X.iso.inv
      inv := @rightAdjointMate C _ _ X.obj ((doubleRightDualFunctor C).obj X.obj) _ _ X.iso.hom
      hom_inv_id := (comp_rightAdjointMate (f := X.iso.hom) (g := X.iso.inv)).symm.trans
        ((congrArg _ X.iso.hom_inv_id).trans rightAdjointMate_id)
      inv_hom_id := (comp_rightAdjointMate (f := X.iso.inv) (g := X.iso.hom)).symm.trans
        ((congrArg _ X.iso.inv_hom_id).trans rightAdjointMate_id) }
  iso_hom_comp_map_iso_hom := by
    have h : (doubleRightDualFunctor C).map X.iso.inv ≫ X.iso.inv = e.inv.app X.obj := by
      refine ((Iso.hom_comp_eq_id (e.app X.obj)).1 ?_)
      rw [Iso.app_hom, ← X.iso_hom_comp_map_iso_hom, Category.assoc,
        ← (doubleRightDualFunctor C).map_comp_assoc, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
    -- The mates are stated at `(doubleRightDualFunctor C).obj X.obj`, which agrees with the
    -- objects of the goal only up to unfolding, so the steps are chained by `Eq.trans`.
    exact (comp_rightAdjointMate (g := X.iso.inv)).symm.trans
      ((congrArg rightAdjointMate h).trans (e.hom_app_rightDual X.obj).symm)

/-- The coevaluation of `X.obj` with its right dual, as a morphism of the pivotalization. -/
noncomputable def coevaluation (X : Pivotalization e) :
    𝟙_ (Pivotalization e) ⟶ X ⊗ rightDualObj X where
  hom := η_ X.obj X.objᘁ
  -- The right dual `(X.objᘁᘁ)ᘁ` of `X.objᘁᘁ` and the double right dual `(X.objᘁ)ᘁᘁ` of `X.objᘁ`
  -- agree only up to unfolding, so the steps are chained by `Eq.trans` rather than by rewriting.
  comm := (X.iso.coevaluation_comp_hom_tensorHom_rightAdjointMate_inv_assoc _).trans
    ((Functor.Monoidal.ε_η_assoc _ _).symm.trans
      (congrArg (_ ≫ ·) (doubleRightDualFunctor_map_coevaluation X.obj).symm))

/-- The evaluation of `X.obj` with its right dual, as a morphism of the pivotalization. -/
noncomputable def evaluation (X : Pivotalization e) :
    rightDualObj X ⊗ X ⟶ 𝟙_ (Pivotalization e) where
  hom := ε_ X.obj X.objᘁ
  -- As for `coevaluation`, the objects agree only up to unfolding.
  comm := ((X.iso.rightAdjointMate_inv_tensorHom_hom_comp_evaluation_assoc _).symm.trans
    (congrArg (_ ≫ ·) (doubleRightDualFunctor_μ_comp_map_evaluation X.obj).symm)).trans
      (Category.assoc _ _ _).symm

/-- An object `(X, a)` of the pivotalization is paired with `(Xᘁ, (a⁻¹)ᘁ)` by the evaluation
and coevaluation of `C`. -/
noncomputable instance exactPairingRightDualObj (X : Pivotalization e) :
    ExactPairing X (rightDualObj X) where
  coevaluation' := coevaluation X
  evaluation' := evaluation X
  coevaluation_evaluation' := hom_ext (ExactPairing.coevaluation_evaluation X.obj X.objᘁ)
  evaluation_coevaluation' := hom_ext (ExactPairing.evaluation_coevaluation X.obj X.objᘁ)

/-- The pivotalization is right rigid: the right dual of `(X, a)` is `(Xᘁ, (a⁻¹)ᘁ)`, with the
evaluation and coevaluation of `C`. -/
noncomputable instance : RightRigidCategory (Pivotalization e) where
  rightDual X := ⟨rightDualObj X⟩

/-- The underlying object of the right dual of `(X, a)` is `Xᘁ`. -/
@[simp]
theorem rightDual_obj (X : Pivotalization e) : (Xᘁ).obj = X.objᘁ :=
  (rfl)

/-- The isomorphism of the right dual of `(X, a)` with its double right dual is `(a⁻¹)ᘁ`. -/
@[simp]
theorem rightDual_iso_hom (X : Pivotalization e) : (Xᘁ).iso.hom = X.iso.invᘁ :=
  (rfl)

/-- The inverse of the isomorphism of the right dual of `(X, a)` with its double right dual is
`aᘁ`. -/
@[simp]
theorem rightDual_iso_inv (X : Pivotalization e) : (Xᘁ).iso.inv = X.iso.homᘁ :=
  (rfl)

/-- The coevaluation of `(X, a)` and its right dual is that of `X` in `C`. -/
@[simp]
theorem coevaluation_hom (X : Pivotalization e) : (η_ X Xᘁ).hom = η_ X.obj X.objᘁ :=
  (rfl)

/-- The evaluation of `(X, a)` and its right dual is that of `X` in `C`. -/
@[simp]
theorem evaluation_hom (X : Pivotalization e) : (ε_ X Xᘁ).hom = ε_ X.obj X.objᘁ :=
  (rfl)

/-- The right adjoint mate of a morphism of the pivotalization is computed in `C`. -/
@[simp]
theorem rightAdjointMate_hom {X Y : Pivotalization e} (f : X ⟶ Y) : (fᘁ).hom = (f.hom)ᘁ :=
  (rfl)

/-- The tensor comparison of the double right dual functor of the pivotalization is that of
`C`. -/
@[simp]
theorem doubleRightDualFunctor_μ_hom (X Y : Pivotalization e) :
    (μ (doubleRightDualFunctor (Pivotalization e)) X Y).hom =
      μ (doubleRightDualFunctor C) X.obj Y.obj := by
  rw [doubleRightDualFunctor_μ, doubleRightDualFunctor_μ]
  -- Both sides are built from the evaluations and coevaluations of `C`, which the
  -- pivotalization uses on underlying objects.
  rfl

/-- The unit comparison of the double right dual functor of the pivotalization is that of `C`. -/
@[simp]
theorem doubleRightDualFunctor_ε_hom :
    (ε (doubleRightDualFunctor (Pivotalization e))).hom = ε (doubleRightDualFunctor C) := by
  rw [doubleRightDualFunctor_ε_eq_rightAdjointMate, doubleRightDualFunctor_ε_eq_rightAdjointMate]
  -- As for `doubleRightDualFunctor_μ_hom`.
  rfl

end Rigid

section Pivotal

variable [NatTrans.IsMonoidal e.hom]

variable (e) in
/-- The tautological pivotal structure of the pivotalization: its component at `(X, a)` is `a`,
which is a morphism of the pivotalization from `(X, a)` to its double right dual. -/
noncomputable def pivotalIso : 𝟭 (Pivotalization e) ≅ doubleRightDualFunctor (Pivotalization e) :=
  NatIso.ofComponents (fun X => isoMk X.iso rfl) fun f => hom_ext f.comm

/-- The tautological pivotal structure is monoidal: the unit and tensor comparisons of the double
right dual functor of the pivotalization are those of `C`. -/
instance : NatTrans.IsMonoidal (pivotalIso e).hom where
  unit := hom_ext ((Category.id_comp _).trans doubleRightDualFunctor_ε_hom.symm)
  tensor X Y := by
    ext
    rw [comp_hom, comp_hom, doubleRightDualFunctor_μ_hom]
    exact Category.id_comp _

/-- The pivotalization is rigid: the left dual of `(X, a)` is its right dual, paired with `(X, a)`
through the tautological pivotal structure. -/
noncomputable instance : RigidCategory (Pivotalization e) :=
  rigidCategoryOfIsoDoubleRightDual (pivotalIso e).app

/-- The tautological pivotal structure of the pivotalization. -/
noncomputable instance : PivotalCategory (Pivotalization e) :=
  pivotalCategoryOfRightRigid (pivotalIso e)

/-- The component at `(X, a)` of the pivotal structure of the pivotalization is `a`. -/
@[simp]
theorem pivotalIsoApp_hom_hom (X : Pivotalization e) : (pivotalIsoApp X).hom.hom = X.iso.hom := by
  rw [pivotalIsoApp_pivotalCategoryOfRightRigid (pivotalIso e) X]
  -- The components of `pivotalIso e` are defined by `isoMk X.iso`.
  rfl

/-- The inverse of the component at `(X, a)` of the pivotal structure of the pivotalization is
the inverse of `a`. -/
@[simp]
theorem pivotalIsoApp_inv_hom (X : Pivotalization e) : (pivotalIsoApp X).inv.hom = X.iso.inv := by
  rw [pivotalIsoApp_pivotalCategoryOfRightRigid (pivotalIso e) X]
  -- The components of `pivotalIso e` are defined by `isoMk X.iso`.
  rfl

/-- The trace of a morphism `b : X ⟶ Xᘁᘁ` of the pivotalization is computed in `C`. -/
@[simp]
theorem doubleDualTrace_hom {X : Pivotalization e} (b : X ⟶ (Xᘁ)ᘁ) :
    (doubleDualTrace b).hom = doubleDualTrace b.hom := by
  rw [doubleDualTrace_def, doubleDualTrace_def]
  -- Composition, whiskering, evaluation and coevaluation are computed in `C`.
  rfl

/-- The squared norm of an object of the pivotalization, with respect to an isomorphism
`a : X ≅ Xᘁᘁ`, is the squared norm of the underlying object with respect to the underlying
isomorphism: the forgetful functor preserves squared norms. -/
theorem squaredNorm_hom {X : Pivotalization e} (a : X ≅ (Xᘁ)ᘁ) :
    (squaredNorm a).hom = squaredNorm ((forget e).mapIso a) := by
  rw [squaredNorm_def, squaredNorm_def, comp_hom, doubleDualTrace_hom, doubleDualTrace_hom]
  -- Mates are computed in `C`, by `rightAdjointMate_hom`.
  rfl

/-- The right dimension of `(X, a)` in the pivotalization is the trace of `a`. -/
theorem rightDim_hom (X : Pivotalization e) : (rightDim X).hom = doubleDualTrace X.iso.hom := by
  rw [← doubleDualTrace_pivotalIsoApp_hom, doubleDualTrace_hom, pivotalIsoApp_hom_hom]

/-- The left dimension of `(X, a)` in the pivotalization is the trace of the mate `(a⁻¹)ᘁ`. -/
theorem leftDim_hom (X : Pivotalization e) :
    (leftDim X).hom = doubleDualTrace (rightAdjointMate X.iso.inv) := by
  rw [← doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv, doubleDualTrace_hom,
    rightAdjointMate_hom, pivotalIsoApp_inv_hom]

/-- The squared norm of the underlying object of `(X, a)` with respect to `a` is the product of
the left and right dimensions of `(X, a)` in the pivotalization. -/
theorem squaredNorm_iso (X : Pivotalization e) :
    squaredNorm X.iso = (leftDim X ≫ rightDim X).hom := by
  rw [← squaredNorm_pivotalIsoApp, squaredNorm_hom]
  congr 1
  ext
  exact (pivotalIsoApp_hom_hom X).symm

end Pivotal

end Pivotalization

end TauCeti
