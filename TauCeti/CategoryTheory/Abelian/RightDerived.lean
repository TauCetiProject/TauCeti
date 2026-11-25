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
# Additivity, commutation with exact functors, and dimension shifting for right derived functors

Injective resolutions are additive after passing to the homotopy category: the sum of
two lifts is a lift of the sum, and lifts of the same morphism are homotopic. Thus right
derived functors of additive functors are additive. If the functor is exact, its
positive right derived functors vanish.

`CategoryTheory.NatIso.rightDerived` transports a natural isomorphism to right derived
functors, with the induced transformations as its hom and inverse.

Right derived functors also commute with exact functors which preserve injective objects
(`CategoryTheory.Functor.rightDerivedCompIso`): if `F ⋙ G ≅ H ⋙ F'` where `G` preserves
homology and `H` preserves homology and injective objects, then `RⁿF ⋙ G ≅ H ⋙ RⁿF'`.

The proof uses Mathlib's `InjectiveResolution.descHomotopy`, the uniqueness theorem for
lifts between injective resolutions.

## Dimension shifting

For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, an injective resolution of `Q`
extends to one of `X` (`CategoryTheory.InjectiveResolution.ofShortExact`), which shifts the
right derived functors by one degree:

* `R^{n+2} G (X) ≅ R^{n+1} G (Q)` (`CategoryTheory.Functor.rightDerivedObjX₁IsoOfShortExact`), so
  `R^{n+1} G (Q)` vanishes if and only if `R^{n+2} G (X)` does
  (`CategoryTheory.Functor.isZero_rightDerived_obj_X₃_iff`);
* if `G` is left exact, then `G I ⟶ G Q` is an epimorphism if and only if `R¹ G (X)` vanishes
  (`CategoryTheory.Functor.epi_map_g_iff_isZero_rightDerived_one`), so
  `0 ⟶ G X ⟶ G I ⟶ G Q ⟶ 0` is short exact if and only if `R¹ G (X)` vanishes
  (`CategoryTheory.Functor.shortExact_map_iff_isZero_rightDerived_one`).

These are the dimension-shifting steps of inductive arguments on vanishing derived functors,
such as Leray's acyclicity theorem.

The composition comparison is computed on arbitrary chosen resolutions by
`Functor.rightDerivedCompIso_app_injectiveResolution`. Its special case with the identity as the
outer functor, `RⁿF ≅ H' ⋙ RⁿF''` for `F ≅ H' ⋙ F''`, is `Functor.rightDerivedPrecompIso`.
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

/-- A natural isomorphism between additive functors induces an isomorphism between their
right derived functors in each degree. -/
noncomputable def NatIso.rightDerived {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := e.hom.rightDerived n
  inv := e.inv.rightDerived n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- The forward map of the derived isomorphism is the derived forward transformation. -/
@[simp]
lemma NatIso.rightDerived_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : (NatIso.rightDerived e n).hom = e.hom.rightDerived n :=
  (rfl)

/-- The inverse map of the derived isomorphism is the derived inverse transformation. -/
@[simp]
lemma NatIso.rightDerived_inv {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : (NatIso.rightDerived e n).inv = e.inv.rightDerived n :=
  (rfl)

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

/-! ### Dimension shifting

Let `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` be a short exact sequence with `I` injective. An injective resolution
`Q ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `Q` extends to the injective resolution `X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `X`
(`InjectiveResolution.ofShortExact`). Computing the right derived functors of `G` with these two
resolutions shifts degrees by one, without the long exact sequence of right derived functors. -/

section DimensionShift

open Limits

namespace Functor

variable (G : C ⥤ D) [G.Additive] {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]

include hS in
/-- **Dimension shifting.** For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective,
`R^{n+2} G (X) ≅ R^{n+1} G (Q)`: an injective resolution of `Q` computes the right side, and its
extension `X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` (`InjectiveResolution.ofShortExact`) computes the left side,
with the same differentials one degree higher. -/
noncomputable def rightDerivedObjX₁IsoOfShortExact (n : ℕ) :
    (G.rightDerived (n + 2)).obj S.X₁ ≅ (G.rightDerived (n + 1)).obj S.X₃ :=
  let R := injectiveResolution S.X₃
  (R.ofShortExact hS).isoRightDerivedObj G (n + 2) ≪≫
    HomologicalComplex.homologyIsoSc' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp) ≪≫
    -- the short complexes in degrees `n + 2` and `n + 1` agree by unfolding `augment`
    (HomologicalComplex.homologyIsoSc' ((G.mapHomologicalComplex _).obj R.cocomplex) n (n + 1)
      (n + 2) (by simp) (by simp)).symm ≪≫
    (R.isoRightDerivedObj G (n + 1)).symm

include hS in
/-- **Dimension shifting.** For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective,
`R^{n+1} G (Q)` vanishes if and only if `R^{n+2} G (X)` does. -/
theorem isZero_rightDerived_obj_X₃_iff (n : ℕ) :
    IsZero ((G.rightDerived (n + 1)).obj S.X₃) ↔ IsZero ((G.rightDerived (n + 2)).obj S.X₁) :=
  (G.rightDerivedObjX₁IsoOfShortExact hS n).isZero_iff.symm

include hS in
/-- **Dimension shifting in degree one.** For a left exact functor `G` and a short exact sequence
`0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, `G I ⟶ G Q` is an epimorphism if and only if `R¹ G (X)`
vanishes. -/
theorem epi_map_g_iff_isZero_rightDerived_one [PreservesFiniteLimits G] :
    Epi (G.map S.g) ↔ IsZero ((G.rightDerived 1).obj S.X₁) := by
  let R := injectiveResolution S.X₃
  rw [((R.ofShortExact hS).isoRightDerivedObj G 1).isZero_iff,
    HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  -- `G (R⁰)` has kernel `G Q` along `G (R⁰ ⟶ R¹)`, as `G` is left exact.
  let T := ShortComplex.mk (G.map R.ι₀) (G.map (R.cocomplex.d 0 1))
    (by rw [← G.map_comp]; simp)
  have hT : T.Exact := R.exact_ι₀.map_of_mono_of_preservesKernel G inferInstance inferInstance
  have : Mono T.f := inferInstanceAs (Mono (G.map R.ι₀))
  have : Epi (kernel.lift T.g T.f T.zero) := hT.epi_kernelLift
  have : IsIso (kernel.lift T.g T.f T.zero) := isIso_of_mono_of_epi _
  -- the differential `G I ⟶ G (R⁰)` of `G` applied to the augmented complex is
  -- `G (S.g ≫ R.ι₀)` by unfolding `augment`
  change _ ↔ Epi (kernel.lift T.g (G.map (S.g ≫ R.ι₀)) (by rw [← G.map_comp]; simp))
  have e : kernel.lift T.g (G.map (S.g ≫ R.ι₀)) (by rw [← G.map_comp]; simp) =
      G.map S.g ≫ kernel.lift T.g T.f T.zero := by
    ext
    simp [T]
  rw [e, epi_comp_iff_of_isIso]

include hS in
/-- For a left exact functor `G` and a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I`
injective, `0 ⟶ G X ⟶ G I ⟶ G Q ⟶ 0` is short exact if and only if `R¹ G (X)` vanishes. -/
theorem shortExact_map_iff_isZero_rightDerived_one [PreservesFiniteLimits G] :
    (S.map G).ShortExact ↔ IsZero ((G.rightDerived 1).obj S.X₁) :=
  ⟨fun h ↦ (G.epi_map_g_iff_isZero_rightDerived_one hS).1 h.epi_g, fun h ↦
    { exact := hS.exact.map_of_mono_of_preservesKernel G hS.mono_f inferInstance
      mono_f := have := hS.mono_f; inferInstanceAs (Mono (G.map S.f))
      epi_g := (G.epi_map_g_iff_isZero_rightDerived_one hS).2 h }⟩

end Functor

end DimensionShift

end CategoryTheory

/-! ### Chosen-resolution computation of the native composition comparison -/

universe u' v' u₂ v₂ u₃ v₃

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The chosen-resolution derived-object isomorphism factors through homotopy homology. -/
theorem _root_.CategoryTheory.InjectiveResolution.isoRightDerivedObj_eq_mapIso
    {X : C} (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    I.isoRightDerivedObj F n =
      (HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).mapIso
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).mapIso I.iso) ≪≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).app
        ((F.mapHomologicalComplex _).obj I.cocomplex) := by
  apply Iso.ext
  -- The chosen-resolution object iso is defined through the quotient homology factorization.
  change (HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).map
      ((F.mapHomotopyCategory (ComplexShape.up ℕ)).map I.iso.hom ≫
        (F.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).hom.app I.cocomplex) ≫ _ = _
  erw [CategoryTheory.Functor.mapHomotopyCategoryFactors_hom_app, Category.comp_id]
  rfl

section Component
variable {C' : Type u₂} [Category.{v₂} C'] [Abelian C'] [HasInjectiveResolutions C']
  {D' : Type u₃} [Category.{v₃} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive]
  (G : D ⥤ D') [G.Additive] [G.PreservesHomology]
  (H' : C ⥤ C') [H'.Additive] [H'.PreservesInjectiveObjects] [H'.PreservesHomology]
  (F' : C' ⥤ D') [F'.Additive] (e : F ⋙ G ≅ H' ⋙ F')

private def comparisonComplexIso (K : CochainComplex C ℕ) :
    (G.mapHomologicalComplex _).obj ((F.mapHomologicalComplex _).obj K) ≅
      (F'.mapHomologicalComplex _).obj ((H'.mapHomologicalComplex _).obj K) :=
  (CategoryTheory.Functor.mapHomologicalComplexCompIso e _).app K ≪≫
    ((CategoryTheory.Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) _).app K).symm

private noncomputable def comparisonHomotopyIso (n : ℕ) :
    (F.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
      HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n) ⋙ G ≅
      H'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
        F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n :=
  CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (F.mapHomotopyCategory _)
      (G.mapHomotopyCategoryCompHomologyFunctorIso _ n).symm ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.mapHomotopyCategoryCompIso e _ ≪≫
        (CategoryTheory.Functor.mapHomotopyCategoryCompIso (Iso.refl (H' ⋙ F')) _).symm) _ ≪≫
    CategoryTheory.Functor.associator _ _ _

private theorem derivedComparison_homotopy_canonical (X : C) (n : ℕ) :
    (CategoryTheory.Functor.rightDerivedCompIso F G H' F' e n).hom.app X =
      (comparisonHomotopyIso F G H' F' e n).hom.app ((injectiveResolutions C).obj X) ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
            (H'.injectiveResolutionsCompIso.hom.app X) := by
  dsimp [CategoryTheory.Functor.rightDerivedCompIso, comparisonHomotopyIso,
    CategoryTheory.Functor.associator, CategoryTheory.Functor.rightDerived,
    CategoryTheory.Functor.rightDerivedToHomotopyCategory]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]


private theorem derivedComparison_homotopy_arbitrary {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (CategoryTheory.Functor.rightDerivedCompIso F G H' F' e n).hom.app X ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
            (H'.mapInjectiveResolution I).iso.hom =
      G.map ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).map
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).map I.iso.hom)) ≫
      (comparisonHomotopyIso F G H' F' e n).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).obj I.cocomplex) := by
  let T := F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
    HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n
  erw [derivedComparison_homotopy_canonical, Category.assoc, ← T.map_comp,
    injectiveResolutionsCompIso_hom_app_comp_iso_hom]
  exact ((comparisonHomotopyIso F G H' F' e n).hom.naturality I.iso.hom).symm


omit [HasInjectiveResolutions C] in
/-- On the class of a complex `L`, the homotopy-category comparison
`G.mapHomotopyCategoryCompHomologyFunctorIso` is the homological-complex comparison conjugated by
the identifications `homologyFunctorFactors`. -/
private lemma mapHomotopyCategoryCompHomologyFunctorIso_app_quotient (L : CochainComplex D ℕ)
    (n : ℕ) :
    (G.mapHomotopyCategoryCompHomologyFunctorIso (ComplexShape.up ℕ) n).app
        ((HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj L) =
      (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).app
          ((G.mapHomologicalComplex _).obj L) ≪≫
        (G.mapHomologicalComplexCompHomologyFunctorIso _ n).app L ≪≫
        (G.mapIso ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).app L)).symm :=
  Iso.ext (G.mapHomotopyCategoryCompHomologyFunctorIso_hom_app (ComplexShape.up ℕ) n L)

omit [HasInjectiveResolutions C]
  [HasInjectiveResolutions C'] [H'.PreservesInjectiveObjects] [H'.PreservesHomology] in
private theorem comparisonHomotopy_complex_component (K : CochainComplex C ℕ) (n : ℕ) :
    (comparisonHomotopyIso F G H' F' e n).app
        ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).obj K) =
      G.mapIso ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).app
          ((F.mapHomologicalComplex _).obj K)) ≪≫
        ((G.mapHomologicalComplexCompHomologyFunctorIso _ n).app
          ((F.mapHomologicalComplex _).obj K)).symm ≪≫
        (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
          (comparisonComplexIso F G H' F' e K) ≪≫
        ((HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).app
          ((F'.mapHomologicalComplex _).obj ((H'.mapHomologicalComplex _).obj K))).symm := by
  apply Iso.ext
  simp only [comparisonHomotopyIso, comparisonComplexIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id, Iso.app_inv,
    Functor.mapIso_hom]
  -- `F.mapHomotopyCategory` sends the class of `K` to the class of `F` applied to `K`.
  have hG : (G.mapHomotopyCategoryCompHomologyFunctorIso (ComplexShape.up ℕ) n).inv.app
      ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).obj K)) = _ :=
    congrArg Iso.inv (mapHomotopyCategoryCompHomologyFunctorIso_app_quotient G
      ((F.mapHomologicalComplex _).obj K) n)
  have hn := (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).inv.naturality
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) (ComplexShape.up ℕ)).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hG, mapHomotopyCategoryCompIso_hom_app_quotient_obj,
    mapHomotopyCategoryCompIso_inv_app_quotient_obj,
    ← Functor.map_comp]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  -- The remaining square is naturality of `homologyFunctorFactors` for the comparison map.
  rw [← hn]

omit [HasInjectiveResolutions C] in
/-- Reassociation of a composite of six morphisms. -/
private lemma comp_assoc_five {E : Type*} [Category* E] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : E}
    (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) (f₆ : A₅ ⟶ A₆) :
    (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅) ≫ f₆ = f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ := by
  simp only [Category.assoc]

/-- Compute the native derived composition comparison using any injective resolution. -/
theorem rightDerivedCompIso_app_injectiveResolution {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (CategoryTheory.Functor.rightDerivedCompIso F G H' F' e n).app X =
      G.mapIso (I.isoRightDerivedObj F n) ≪≫
        ((G.mapHomologicalComplexCompHomologyFunctorIso _ n).app
          ((F.mapHomologicalComplex _).obj I.cocomplex)).symm ≪≫
        (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
          ((Functor.mapHomologicalComplexCompIso e _).app I.cocomplex ≪≫
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) _).app I.cocomplex).symm) ≪≫
        ((H'.mapInjectiveResolution I).isoRightDerivedObj F' n).symm := by
  apply Iso.ext
  -- `derivedComparison_homotopy_arbitrary` computes the comparison after the homotopy-homology
  -- image of the chosen-resolution iso of `H'.mapInjectiveResolution I`; move that iso across.
  have t : (rightDerivedCompIso F G H' F' e n).hom.app X = _ ≫
      (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
        HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
          (H'.mapInjectiveResolution I).iso.inv :=
    (Iso.eq_comp_inv ((F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
      HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
        (H'.mapInjectiveResolution I).iso)).2 (derivedComparison_homotopy_arbitrary F G H' F' e I n)
  have q := congrArg Iso.hom (comparisonHomotopy_complex_component F G H' F' e I.cocomplex n)
  have hI := congrArg Iso.hom (I.isoRightDerivedObj_eq_mapIso F n)
  have hJ := congrArg Iso.inv ((H'.mapInjectiveResolution I).isoRightDerivedObj_eq_mapIso F' n)
  simp only [Iso.app_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv] at q hI hJ
  -- `(H'.mapInjectiveResolution I).cocomplex` is `H'` applied to `I.cocomplex` by definition; in
  -- that form the last two factors of the right side are the composite `hJ`.
  have hlast : ((HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
        ((Functor.mapHomologicalComplexCompIso e _).app I.cocomplex ≪≫
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) _).app I.cocomplex).symm) ≪≫
        ((H'.mapInjectiveResolution I).isoRightDerivedObj F' n).symm).hom =
      (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
        (comparisonComplexIso F G H' F' e I.cocomplex).hom ≫
        (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).inv.app
          ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            ((H'.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
            (H'.mapInjectiveResolution I).iso.inv :=
    congrArg (_ ≫ ·) hJ
  dsimp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom]
  rw [t, q, hI, Iso.symm_hom, hlast, Iso.app_inv]
  -- The two sides agree up to `Functor.map_comp` and reassociation. Some of the intermediate
  -- objects agree only after unfolding `Functor.mapHomotopyCategory` and
  -- `Functor.mapInjectiveResolution`, so the steps are assembled by unification, not by `rw`.
  exact (comp_assoc_five _ _ _ _ _ _).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (G.map_comp _ _).symm))

/-- If `F ≅ H' ⋙ F''` where `H'` preserves homology and injective objects, then
`RⁿF ≅ H' ⋙ RⁿF''`. This is `rightDerivedCompIso` with the identity functor as `G`. -/
noncomputable def rightDerivedPrecompIso (F'' : C' ⥤ D) [F''.Additive] (e' : F ≅ H' ⋙ F'')
    (n : ℕ) : F.rightDerived n ≅ H' ⋙ F''.rightDerived n :=
  (Functor.rightUnitor (F.rightDerived n)).symm ≪≫
    Functor.rightDerivedCompIso F (𝟭 D) H' F'' (Functor.rightUnitor F ≪≫ e') n

/-- `rightDerivedPrecompIso` acts by the comparison cochain map on any chosen resolution. -/
theorem rightDerivedPrecompIso_app_hom (F'' : C' ⥤ D) [F''.Additive]
    (e' : F ≅ H' ⋙ F'') {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (rightDerivedPrecompIso F H' F'' e' n).hom.app X ≫
      ((H'.mapInjectiveResolution I).isoRightDerivedObj F'' n).hom =
    (I.isoRightDerivedObj F n).hom ≫ HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex e'.hom _).app I.cocomplex ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F'')) _).inv.app I.cocomplex) n := by
  dsimp only [rightDerivedPrecompIso, Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor]
  simp_rw [← Iso.app_hom]
  erw [Functor.rightDerivedCompIso_app_injectiveResolution F (𝟭 D) H' F''
    (Functor.rightUnitor F ≪≫ e') I n]
  dsimp only [CategoryTheory.Functor.mapInjectiveResolution, Iso.app_hom,
    Functor.rightUnitor]
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.id_map, Category.assoc, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]
  dsimp only [Iso.app_inv]
  erw [CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso_id_inv_app]
  erw [← HomologicalComplex.homologyMap_comp]
  congr 2
  ext j
  simp
end Component
end CategoryTheory.Functor
