/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Strong monoidal functors preserve tensor powers

A strong monoidal functor `F : C ⥤ D` carries the tensor powers `TauCeti.tensorPow X n` of an
object `X` of `C` to the tensor powers of `F.obj X`, by the isomorphism
`F.mapTensorPowIso X n : F.obj (tensorPow X n) ≅ tensorPow (F.obj X) n` built from the unit and
tensor comparisons of `F`. This comparison is natural in `X`, is the identity for the identity
functor, is compatible with composition of strong monoidal functors, and commutes with monoidal
natural transformations.

## Main declarations

* `CategoryTheory.Functor.mapTensorPowIso`: the comparison `F (X^{⊗n}) ≅ (F X)^{⊗n}`;
* `CategoryTheory.Functor.mapTensorPowIso_hom_naturality`: its naturality in `X`;
* `CategoryTheory.Functor.mapTensorPowIso_id` and `CategoryTheory.Functor.mapTensorPowIso_comp`:
  the comparisons for the identity functor and for a composite;
* `CategoryTheory.NatTrans.app_tensorPow_comp_mapTensorPowIso_hom`: compatibility with a monoidal
  natural transformation.
-/

public section

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

namespace Functor

variable (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor carries tensor powers to tensor powers:
`F (X^{⊗0}) ≅ 𝟙_ D` is the inverse unit comparison, and `F (X ⊗ X^{⊗n}) ≅ F X ⊗ (F X)^{⊗n}` is
the inverse tensor comparison followed by the comparison for `X^{⊗n}`. -/
def mapTensorPowIso (X : C) :
    (n : ℕ) → F.obj (TauCeti.tensorPow X n) ≅ TauCeti.tensorPow (F.obj X) n
  | 0 => (Monoidal.εIso F).symm
  | n + 1 => (Monoidal.μIso F X (TauCeti.tensorPow X n)).symm ≪≫
      whiskerLeftIso (F.obj X) (mapTensorPowIso X n)

/-- The comparison for the zeroth tensor power is the inverse unit comparison. -/
@[simp]
theorem mapTensorPowIso_zero (X : C) : F.mapTensorPowIso X 0 = (Monoidal.εIso F).symm :=
  (rfl)

/-- The comparison for `X^{⊗(n + 1)} = X ⊗ X^{⊗n}` is the inverse tensor comparison followed by
the comparison for `X^{⊗n}` on the right factor. -/
theorem mapTensorPowIso_succ (X : C) (n : ℕ) :
    F.mapTensorPowIso X (n + 1) = (Monoidal.μIso F X (TauCeti.tensorPow X n)).symm ≪≫
      whiskerLeftIso (F.obj X) (F.mapTensorPowIso X n) :=
  (rfl)

/-- The forward comparison for `X^{⊗(n + 1)}` is `δ` followed by the comparison for `X^{⊗n}`. -/
theorem mapTensorPowIso_succ_hom (X : C) (n : ℕ) :
    (F.mapTensorPowIso X (n + 1)).hom =
      δ F X (TauCeti.tensorPow X n) ≫ F.obj X ◁ (F.mapTensorPowIso X n).hom :=
  (rfl)

/-- The inverse comparison for `X^{⊗(n + 1)}` is the inverse comparison for `X^{⊗n}` followed by
`μ`. -/
theorem mapTensorPowIso_succ_inv (X : C) (n : ℕ) :
    (F.mapTensorPowIso X (n + 1)).inv =
      F.obj X ◁ (F.mapTensorPowIso X n).inv ≫ μ F X (TauCeti.tensorPow X n) :=
  (rfl)

/-- The inverse comparison is natural in the object. -/
@[reassoc]
theorem mapTensorPowIso_inv_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    TauCeti.tensorPowMap (F.map f) n ≫ (F.mapTensorPowIso Y n).inv =
      (F.mapTensorPowIso X n).inv ≫ F.map (TauCeti.tensorPowMap f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [mapTensorPowIso_succ_inv, mapTensorPowIso_succ_inv, TauCeti.tensorPowMap_succ,
      TauCeti.tensorPowMap_succ, Category.assoc, ← μ_natural, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ih,
      Category.id_comp, Category.comp_id]

/-- **Naturality** of the comparison `F (X^{⊗n}) ≅ (F X)^{⊗n}` in `X`. -/
@[reassoc]
theorem mapTensorPowIso_hom_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    F.map (TauCeti.tensorPowMap f n) ≫ (F.mapTensorPowIso Y n).hom =
      (F.mapTensorPowIso X n).hom ≫ TauCeti.tensorPowMap (F.map f) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    mapTensorPowIso_inv_naturality]

/-- For the identity functor, the comparison of tensor powers is the identity. -/
@[simp]
theorem mapTensorPowIso_id (X : C) (n : ℕ) :
    (𝟭 C).mapTensorPowIso X n = Iso.refl (TauCeti.tensorPow X n) := by
  ext
  induction n with
  | zero => simp
  | succ n ih => simp [mapTensorPowIso_succ_hom, ih]

/-- For a composite of strong monoidal functors, the comparison of tensor powers is the image of
the comparison for the first functor followed by the comparison for the second. -/
theorem mapTensorPowIso_comp (G : D ⥤ E) [G.Monoidal] (X : C) (n : ℕ) :
    (F ⋙ G).mapTensorPowIso X n =
      G.mapIso (F.mapTensorPowIso X n) ≪≫ G.mapTensorPowIso (F.obj X) n := by
  ext
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Iso.trans_hom, mapIso_hom] at ih
    rw [mapTensorPowIso_succ_hom, ih, comp_δ, Iso.trans_hom, mapIso_hom, mapTensorPowIso_succ_hom,
      mapTensorPowIso_succ_hom, Functor.map_comp]
    simp only [comp_obj, Category.assoc, MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc]

end Functor

namespace NatTrans

variable {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G) [τ.IsMonoidal]

/-- A monoidal natural transformation commutes with the inverse comparisons of tensor powers. -/
@[reassoc]
theorem mapTensorPowIso_inv_comp_app_tensorPow (X : C) (n : ℕ) :
    (F.mapTensorPowIso X n).inv ≫ τ.app (TauCeti.tensorPow X n) =
      TauCeti.tensorPowMap (τ.app X) n ≫ (G.mapTensorPowIso X n).inv := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Functor.mapTensorPowIso_succ_inv, Functor.mapTensorPowIso_succ_inv,
      TauCeti.tensorPowMap_succ, Category.assoc, IsMonoidal.tensor, ← Category.assoc,
      ← Category.assoc]
    congr 1
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ih,
      Category.id_comp, Category.comp_id]

/-- A monoidal natural transformation `τ : F ⟶ G` commutes with the comparisons
`F (X^{⊗n}) ≅ (F X)^{⊗n}` and `G (X^{⊗n}) ≅ (G X)^{⊗n}`: on tensor powers it acts as the tensor
power of its component at `X`. -/
@[reassoc]
theorem app_tensorPow_comp_mapTensorPowIso_hom (X : C) (n : ℕ) :
    τ.app (TauCeti.tensorPow X n) ≫ (G.mapTensorPowIso X n).hom =
      (F.mapTensorPowIso X n).hom ≫ TauCeti.tensorPowMap (τ.app X) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    mapTensorPowIso_inv_comp_app_tensorPow]

end NatTrans

end CategoryTheory
