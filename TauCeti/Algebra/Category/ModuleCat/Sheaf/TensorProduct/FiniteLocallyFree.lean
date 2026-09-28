/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Dual

/-!
# Internal Hom from a finite free sheaf

The internal Hom from a finite free sheaf into a finite locally free sheaf is finite locally free.
The finite free sheaf is self-dual, so this internal Hom is its tensor product with the target.
This is the local calculation behind duals and internal Homs of algebraic vector bundles.

The closure gives an endofunctor of the full category of finite locally free sheaves. Its
underlying object and morphism are the usual internal Hom object and map.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

namespace SheafOfModules

open _root_.SheafOfModules

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] [HasPullbacks C] [HasBinaryProducts C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- Internal Hom out of a finite free sheaf preserves finite local freeness. -/
theorem isFiniteLocallyFree_ihom_free (I : Type u) [Finite I]
    (N : _root_.SheafOfModules.{u} (ringCatSheaf R))
    (hN : isFiniteLocallyFree (ringCatSheaf R) N) :
    isFiniteLocallyFree (ringCatSheaf R) ((ihom (free I)).obj N) := by
  have hfree : isFiniteLocallyFree (ringCatSheaf R) (free I) :=
    ⟨inferInstance, isFinitePresentation_free I⟩
  have htensor : isFiniteLocallyFree (ringCatSheaf R) (free I ⊗ N) :=
    (isFiniteLocallyFree (ringCatSheaf R)).prop_tensor hfree hN
  exact (isFiniteLocallyFree (ringCatSheaf R)).prop_of_iso (ihomFreeIso I N).symm htensor

/-- Internal Hom out of a finite free sheaf as an endofunctor of finite locally free sheaves. -/
def internalHomFree (I : Type u) [Finite I] :
    (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory ⥤
      (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory :=
  (isFiniteLocallyFree (ringCatSheaf R)).lift
    ((isFiniteLocallyFree (ringCatSheaf R)).ι ⋙ ihom (free I))
    fun E ↦ isFiniteLocallyFree_ihom_free I E.obj E.property

/-- The underlying sheaf of the finite free internal Hom is the ordinary internal Hom. -/
@[simp]
theorem internalHomFree_obj_obj (I : Type u) [Finite I]
    (N : (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory) :
    ((internalHomFree I).obj N).obj = (ihom (free I)).obj N.obj :=
  (rfl)

/-- On morphisms, the finite free internal Hom is the ordinary internal Hom map. -/
@[simp]
theorem internalHomFree_map_hom (I : Type u) [Finite I]
    {M N : (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory} (f : M ⟶ N) :
    ((internalHomFree I).map f).hom =
      eqToHom (internalHomFree_obj_obj I M) ≫ (ihom (free I)).map f.hom ≫
        eqToHom (internalHomFree_obj_obj I N).symm := by
  cases internalHomFree_obj_obj I M
  cases internalHomFree_obj_obj I N
  rfl

end

end SheafOfModules

end TauCeti
