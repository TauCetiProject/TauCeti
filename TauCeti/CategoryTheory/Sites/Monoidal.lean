/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The sectionwise tensor product of sheaves maps to their tensor product

Let `A` be a monoidal category and `J` a Grothendieck topology such that sheafification of
`A`-valued presheaves is compatible with tensor products. Equip `Sheaf J A` with the tensor
product obtained by sheafifying the sectionwise tensor product
(`CategoryTheory.Sheaf.monoidalCategory`). This file constructs the canonical map
`F.obj ⊗ G.obj ⟶ (F ⊗ G).obj` from the sectionwise tensor product of two sheaves to the underlying
presheaf of their tensor product, and shows that it is natural and that morphisms out of `F ⊗ G`
are determined by their restriction along it. It gives the same description of the unit of
`Sheaf J A`, the sheafification of the constant presheaf `𝟙_ A`, and identifies it with the constant
sheaf `𝟙_ A`.

## Main declarations

* `CategoryTheory.Sheaf.toTensorObj F G`: the canonical map `F.obj ⊗ G.obj ⟶ (F ⊗ G).obj`.
* `CategoryTheory.Sheaf.toTensorObj_naturality`: it is natural in `F` and `G`.
* `CategoryTheory.Sheaf.tensorObj_hom_ext`: morphisms of sheaves out of `F ⊗ G` agreeing after
  `Sheaf.toTensorObj F G` are equal.
* `CategoryTheory.Sheaf.toTensorUnit J A`: the canonical map `𝟙_ (Cᵒᵖ ⥤ A) ⟶ (𝟙_ (Sheaf J A)).obj`.
* `CategoryTheory.Sheaf.tensorUnit_hom_ext`: morphisms of sheaves out of `𝟙_ (Sheaf J A)` agreeing
  after `Sheaf.toTensorUnit J A` are equal.
* `CategoryTheory.Sheaf.tensorUnitIsoConstantSheaf`: the unit `𝟙_ (Sheaf J A)` is the constant
  sheaf `𝟙_ A`.
-/

public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Sheaf

attribute [local instance] monoidalCategory

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

/-- The canonical map from the sectionwise tensor product of the underlying presheaves of two
sheaves to the underlying presheaf of their tensor product: the unit of sheafification followed by
the identification of the sheafified tensor product with `F ⊗ G`. -/
noncomputable def toTensorObj (F G : Sheaf J A) : F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  CategoryTheory.toSheafify J (F.obj ⊗ G.obj) ≫
    ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
      ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)).hom

/-- `Sheaf.toTensorObj F G` is the unit of sheafification followed by the identification of the
sheafified tensor product with `F ⊗ G`. -/
lemma toTensorObj_def (F G : Sheaf J A) :
    toTensorObj F G = CategoryTheory.toSheafify J (F.obj ⊗ G.obj) ≫
      ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
        ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)).hom :=
  (rfl)

/-- Morphisms of sheaves out of `F ⊗ G` are determined by their restriction along
`Sheaf.toTensorObj F G`. -/
lemma tensorObj_hom_ext {F G H : Sheaf J A} {f g : F ⊗ G ⟶ H}
    (h : toTensorObj F G ≫ f.hom = toTensorObj F G ≫ g.hom) : f = g := by
  refine (cancel_epi ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
    ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv))).1 (Sheaf.hom_ext ?_)
  exact sheafify_hom_ext _ _ _ H.property (by simpa [toTensorObj_def] using h)

/-- `Sheaf.toTensorObj` is natural in both sheaves. -/
@[reassoc]
lemma toTensorObj_naturality {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G') :
    (f.hom ⊗ₘ g.hom) ≫ toTensorObj F' G' = toTensorObj F G ≫ (f ⊗ₘ g).hom := by
  have hF : (presheafToSheaf J A).map f.hom ≫ (sheafificationIso F').inv =
      (sheafificationIso F).inv ≫ f := (sheafificationNatIso J A).inv.naturality f
  have hG : (presheafToSheaf J A).map g.hom ≫ (sheafificationIso G').inv =
      (sheafificationIso G).inv ≫ g := (sheafificationNatIso J A).inv.naturality g
  have h : (presheafToSheaf J A).map (f.hom ⊗ₘ g.hom) ≫
      (Functor.Monoidal.μIso (presheafToSheaf J A) F'.obj G'.obj).inv ≫
        ((sheafificationIso F').inv ⊗ₘ (sheafificationIso G').inv) =
      ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
        ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)) ≫ (f ⊗ₘ g) := by
    rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv,
      ← Functor.OplaxMonoidal.δ_natural_assoc, Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, hF, hG]
  rw [toTensorObj_def, toTensorObj_def, toSheafify_naturality_assoc, Category.assoc]
  exact congrArg (toSheafify J _ ≫ ·.hom) h

variable (J A) in
/-- The canonical map from the unit `𝟙_ (Cᵒᵖ ⥤ A)` of presheaves, the constant presheaf `𝟙_ A`, to
the underlying presheaf of the unit of sheaves: the unit of sheafification followed by the
identification of the sheafified unit with `𝟙_ (Sheaf J A)`. -/
noncomputable def toTensorUnit : 𝟙_ (Cᵒᵖ ⥤ A) ⟶ (𝟙_ (Sheaf J A)).obj :=
  CategoryTheory.toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫
    (Functor.Monoidal.εIso (presheafToSheaf J A)).inv.hom

variable (J A) in
/-- `Sheaf.toTensorUnit J A` is the unit of sheafification followed by the identification of the
sheafified unit with `𝟙_ (Sheaf J A)`. -/
lemma toTensorUnit_def :
    toTensorUnit J A = CategoryTheory.toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫
      (Functor.Monoidal.εIso (presheafToSheaf J A)).inv.hom :=
  (rfl)

/-- Morphisms of sheaves out of `𝟙_ (Sheaf J A)` are determined by their restriction along
`Sheaf.toTensorUnit J A`. -/
lemma tensorUnit_hom_ext {H : Sheaf J A} {f g : 𝟙_ (Sheaf J A) ⟶ H}
    (h : toTensorUnit J A ≫ f.hom = toTensorUnit J A ≫ g.hom) : f = g := by
  refine (cancel_epi (Functor.Monoidal.εIso (presheafToSheaf J A)).inv).1 (Sheaf.hom_ext ?_)
  exact sheafify_hom_ext _ _ _ H.property (by simpa [toTensorUnit_def] using h)

variable (J A) in
/-- The unit of the tensor product of sheaves, the sheafification of the constant presheaf `𝟙_ A`,
is the constant sheaf `𝟙_ A`. It is characterised by
`toTensorUnit_comp_tensorUnitIsoConstantSheaf_hom_hom`. -/
noncomputable def tensorUnitIsoConstantSheaf :
    𝟙_ (Sheaf J A) ≅ (constantSheaf J A).obj (𝟙_ A) :=
  Functor.Monoidal.εIso (presheafToSheaf J A) ≪≫
    (presheafToSheaf J A).mapIso (NatIso.ofComponents fun _ ↦ Iso.refl _)

variable (J A) in
/-- Restricted along `Sheaf.toTensorUnit J A`, the identification of `𝟙_ (Sheaf J A)` with the
constant sheaf `𝟙_ A` is the unit of sheafification of the constant presheaf `𝟙_ A`. -/
@[reassoc]
lemma toTensorUnit_comp_tensorUnitIsoConstantSheaf_hom_hom :
    toTensorUnit J A ≫ (tensorUnitIsoConstantSheaf J A).hom.hom =
      CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ A)) := by
  rw [toTensorUnit_def, tensorUnitIsoConstantSheaf, Category.assoc,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.trans_hom, Iso.inv_hom_id_assoc]
  -- The second factor is the sheafification of the componentwise identity, which is
  -- `𝟙 ((Functor.const Cᵒᵖ).obj (𝟙_ A))` by definition.
  exact (toSheafify_naturality J (𝟙 ((Functor.const Cᵒᵖ).obj (𝟙_ A)))).symm.trans
    (Category.id_comp _)

end CategoryTheory.Sheaf
