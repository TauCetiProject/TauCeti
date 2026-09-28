/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

/-!
# Internal Hom from a finite free sheaf

The internal Hom from a finite free sheaf into a finite locally free sheaf is finite locally free.
The finite free sheaf is self-dual, so this internal Hom is its tensor product with the target.
This is the local calculation behind duals and internal Homs of algebraic vector bundles.

The closure gives an endofunctor of the full category of finite locally free sheaves. Its
underlying object and morphism are the usual internal Hom object and map.

On each finite free chart of a source sheaf, the same calculation shows that internal Hom
from its restriction preserves finite local freeness. This is the local input for descent from
a finite locally free source.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

open _root_.SheafOfModules TauCeti.SheafOfModules

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

/-- Internal Hom from a sheaf isomorphic to a finite free sheaf preserves finite local
freeness. -/
theorem isFiniteLocallyFree_ihom_of_iso_free (I : Type u) [Finite I]
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) (e : free I ≅ M)
    (hN : isFiniteLocallyFree (ringCatSheaf R) N) :
    isFiniteLocallyFree (ringCatSheaf R) ((ihom M).obj N) := by
  have hfree : isFiniteLocallyFree (ringCatSheaf R) ((ihom (free I)).obj N) :=
    isFiniteLocallyFree_ihom_free I N hN
  have : IsIso (MonoidalClosed.pre e.hom) := MonoidalClosed.pre_isIso e
  exact (isFiniteLocallyFree (ringCatSheaf R)).prop_of_iso
    (asIso ((MonoidalClosed.pre e.hom).app N)).symm hfree

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
/-- On a finite free chart of `M`, internal Hom from the restriction of `M` preserves finite
local freeness. This is the chartwise input for descending internal Homs from a finite locally
free source. -/
theorem isFiniteLocallyFree_ihom_chart
    {M : _root_.SheafOfModules.{u} (ringCatSheaf R)}
    {q : M.LocalGeneratorsData.{u}} (i : q.I)
    [IsIso (q.generators i).π] [(q.generators i).IsFiniteType]
    (N : _root_.SheafOfModules.{u} ((ringCatSheaf R).over (q.X i)))
    (hN : isFiniteLocallyFree ((ringCatSheaf R).over (q.X i)) N) :
    letI : MonoidalCategory (_root_.SheafOfModules.{u} ((ringCatSheaf R).over (q.X i))) :=
      monoidalCategory (R.over (q.X i))
    letI : MonoidalClosed (_root_.SheafOfModules.{u} ((ringCatSheaf R).over (q.X i))) :=
      monoidalClosed (R.over (q.X i))
    isFiniteLocallyFree ((ringCatSheaf R).over (q.X i))
      ((ihom (M.over (q.X i))).obj N) := by
  let : MonoidalCategory (_root_.SheafOfModules.{u} ((ringCatSheaf R).over (q.X i))) :=
    monoidalCategory (R.over (q.X i))
  let : MonoidalClosed (_root_.SheafOfModules.{u} ((ringCatSheaf R).over (q.X i))) :=
    monoidalClosed (R.over (q.X i))
  have : HasBinaryProducts (Over (q.X i)) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let e : free (R := (ringCatSheaf R).over (q.X i)) (q.generators i).I ≅
      M.over (q.X i) := asIso (q.generators i).π
  exact isFiniteLocallyFree_ihom_of_iso_free (R := R.over (q.X i))
    (q.generators i).I (M.over (q.X i)) N e hN

/-- Internal Hom out of a finite free sheaf as an endofunctor of finite locally free sheaves. -/
def ihomFree (I : Type u) [Finite I] :
    (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory ⥤
      (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory :=
  (isFiniteLocallyFree (ringCatSheaf R)).lift
    ((isFiniteLocallyFree (ringCatSheaf R)).ι ⋙ ihom (free I))
    fun E ↦ isFiniteLocallyFree_ihom_free I E.obj E.property

/-- The underlying sheaf of the finite free internal Hom is the ordinary internal Hom. -/
@[simp]
theorem ihomFree_obj_obj (I : Type u) [Finite I]
    (N : (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory) :
    ((ihomFree I).obj N).obj = (ihom (free I)).obj N.obj :=
  (rfl)

/-- On morphisms, the finite free internal Hom is the ordinary internal Hom map. -/
@[simp]
theorem ihomFree_map_hom (I : Type u) [Finite I]
    {M N : (isFiniteLocallyFree (ringCatSheaf R)).FullSubcategory} (f : M ⟶ N) :
    ((ihomFree I).map f).hom =
      eqToHom (ihomFree_obj_obj I M) ≫ (ihom (free I)).map f.hom ≫
        eqToHom (ihomFree_obj_obj I N).symm := by
  cases ihomFree_obj_obj I M
  cases ihomFree_obj_obj I N
  rfl

end

end TauCeti
