/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The sectionwise tensor product of sheaves maps to their tensor product

Let `A` be a monoidal category and `J` a Grothendieck topology such that sheafification of
`A`-valued presheaves is compatible with tensor products. Equip `Sheaf J A` with the tensor
product obtained by sheafifying the sectionwise tensor product
(`CategoryTheory.Sheaf.monoidalCategory`). This file constructs the canonical map
`F.obj ⊗ G.obj ⟶ (F ⊗ G).obj` from the sectionwise tensor product of two sheaves to the underlying
presheaf of their tensor product, and shows that it is natural and that morphisms out of `F ⊗ G`
are determined by their restriction along it.

## Main declarations

* `CategoryTheory.Sheaf.toTensorObj F G`: the canonical map `F.obj ⊗ G.obj ⟶ (F ⊗ G).obj`.
* `CategoryTheory.Sheaf.toTensorObj_naturality`: it is natural in `F` and `G`.
* `CategoryTheory.Sheaf.tensorObj_hom_ext`: morphisms of sheaves out of `F ⊗ G` agreeing after
  `Sheaf.toTensorObj F G` are equal.
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
@[expose] noncomputable def toTensorObj (F G : Sheaf J A) : F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  CategoryTheory.toSheafify J (F.obj ⊗ G.obj) ≫
    ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
      ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)).hom

/-- Morphisms of sheaves out of `F ⊗ G` are determined by their restriction along
`Sheaf.toTensorObj F G`. -/
lemma tensorObj_hom_ext {F G H : Sheaf J A} {f g : F ⊗ G ⟶ H}
    (h : toTensorObj F G ≫ f.hom = toTensorObj F G ≫ g.hom) : f = g := by
  refine (cancel_epi ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
    ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv))).1 (Sheaf.hom_ext ?_)
  exact sheafify_hom_ext _ _ _ H.property (by simpa [toTensorObj] using h)

/-- `Sheaf.toTensorObj` is natural in both sheaves. -/
@[reassoc]
lemma toTensorObj_naturality {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G') :
    (f.hom ⊗ₘ g.hom) ≫ toTensorObj F' G' = toTensorObj F G ≫ (f ⊗ₘ g).hom := by
  have hF : (presheafToSheaf J A).map f.hom ≫ (sheafificationIso F').inv =
      (sheafificationIso F).inv ≫ f := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    ext1
    simp
  have hG : (presheafToSheaf J A).map g.hom ≫ (sheafificationIso G').inv =
      (sheafificationIso G).inv ≫ g := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    ext1
    simp
  have h : (presheafToSheaf J A).map (f.hom ⊗ₘ g.hom) ≫
      (Functor.Monoidal.μIso (presheafToSheaf J A) F'.obj G'.obj).inv ≫
        ((sheafificationIso F').inv ⊗ₘ (sheafificationIso G').inv) =
      ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
        ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)) ≫ (f ⊗ₘ g) := by
    rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv,
      ← Functor.OplaxMonoidal.δ_natural_assoc, Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, hF, hG]
  rw [toTensorObj, toTensorObj, toSheafify_naturality_assoc, Category.assoc]
  exact congrArg (toSheafify J _ ≫ ·.hom) h

end CategoryTheory.Sheaf
