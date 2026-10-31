/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.HomotopyCategory.PreservesHomology
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# Additivity of right derived functors and commutation with exact functors

Injective resolutions are additive after passing to the homotopy category: the sum of
two lifts is a lift of the sum, and lifts of the same morphism are homotopic. Thus right
derived functors of additive functors are additive. If the functor is exact, its
positive right derived functors vanish.

Right derived functors also commute with exact functors which preserve injective objects
(`CategoryTheory.Functor.rightDerivedCompIso`): if `F ⋙ G ≅ H ⋙ F'` where `G` preserves
homology and `H` preserves homology and injective objects, then `RⁿF ⋙ G ≅ H ⋙ RⁿF'`.

The proof uses Mathlib's `InjectiveResolution.descHomotopy`, the uniqueness theorem for
lifts between injective resolutions.
-/

public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- Choosing injective resolutions preserves addition in the homotopy category. -/
instance additive_injectiveResolutions : (injectiveResolutions C).Additive where
  map_add {X Y} f g := by
    let I := injectiveResolution X
    let J := injectiveResolution Y
    have h := InjectiveResolution.descHomotopy (f + g)
      (InjectiveResolution.desc (f + g) J I)
      (InjectiveResolution.desc f J I + InjectiveResolution.desc g J I)
      (by simp) (by simp [Preadditive.comp_add, Preadditive.add_comp])
    exact (HomotopyCategory.eq_of_homotopy _ _ h).trans
      (Functor.map_add (HomotopyCategory.quotient C (ComplexShape.up ℕ)))

variable {C} {D : Type*} [Category* D] [Abelian D]

/-- Right derived functors of an additive functor are additive. -/
instance Functor.additive_rightDerived (F : C ⥤ D) [F.Additive] (q : ℕ) :
    (F.rightDerived q).Additive :=
  inferInstanceAs ((injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙
    HomotopyCategory.homologyFunctor D _ q).Additive)

/-- An exact additive functor has no positive right derived functors. -/
theorem Functor.isZero_rightDerived_succ (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (X : C) (q : ℕ) : Limits.IsZero ((F.rightDerived (q + 1)).obj X) := by
  let I := injectiveResolution X
  refine Limits.IsZero.of_iso ?_ (I.isoRightDerivedObj F (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 1 + 1) (by simp) (by simp)]
  exact (I.exact_succ q).map F

/-- **Right derived functors commute with exact functors preserving injective objects.**
Let `F : C ⥤ D` and `F' : C' ⥤ D'` be additive functors, `G : D ⥤ D'` an additive functor
preserving homology, and `H : C ⥤ C'` an additive functor preserving homology and injective
objects, with `F ⋙ G ≅ H ⋙ F'`. Then `RⁿF ⋙ G ≅ H ⋙ RⁿF'` for every `n`.

Indeed `H` sends an injective resolution of `X` to an injective resolution of `H.obj X`, and `G`
commutes with taking homology. -/
noncomputable def Functor.rightDerivedCompIso {C' : Type*} [Category* C'] [Abelian C']
    [HasInjectiveResolutions C'] {D' : Type*} [Category* D'] [Abelian D']
    (F : C ⥤ D) [F.Additive] (G : D ⥤ D') [G.Additive] [G.PreservesHomology]
    (H : C ⥤ C') [H.Additive] [H.PreservesInjectiveObjects] [H.PreservesHomology]
    (F' : C' ⥤ D') [F'.Additive] (e : F ⋙ G ≅ H ⋙ F') (n : ℕ) :
    F.rightDerived n ⋙ G ≅ H ⋙ F'.rightDerived n :=
  -- `RⁿF` is `injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ homologyFunctor _ _ n`
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (injectiveResolutions C ⋙ F.mapHomotopyCategory _)
      (G.mapHomotopyCategoryCompHomologyFunctorIso _ n).symm ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (injectiveResolutions C)
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e _ ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ F')) _).symm) _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight H.injectiveResolutionsCompIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft H (Functor.associator _ _ _).symm

end CategoryTheory
