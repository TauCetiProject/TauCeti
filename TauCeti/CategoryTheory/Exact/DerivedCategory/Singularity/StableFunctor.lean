/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Functor.Conflation
public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.Functor
public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.Triangulated
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Shift
public import TauCeti.CategoryTheory.Shift.CommShift

/-!
# Stable functors and the Keller–Vossieck functors

Let `F : C ⥤ D` be a stable conflation-exact functor between Frobenius exact structures `E` and
`E'`. It preserves projective objects, so it induces triangle functors `stable(E) ⥤ stable(E')`
and `D_sg(E) ⥤ D_sg(E')`. This file proves that these functors commute with the Keller–Vossieck
functors `stable(E) ⥤ D_sg(E)` and `stable(E') ⥤ D_sg(E')` placing an object in degree zero, up to
an isomorphism of triangle functors:

```text
stable(E)  ⥤ D_sg(E)
   ↓            ↓
stable(E') ⥤ D_sg(E')
```

On objects, the comparison is the commutation of `D_sg(E) ⥤ D_sg(E')` with placing an object in
degree zero. Its compatibility with the shifts reduces to the shift by one, where both shift
comparisons are given by connecting morphisms of suspension presentations, and the functor
`Dᵇ(E) ⥤ Dᵇ(E')` preserves connecting morphisms.

## Main definitions

* `TauCeti.StableConflationExact.stableToSingularityCompMapSingularityCategoryIso`: the
  commutation of the square above.

## Main results

* `TauCeti.ExactStructure.IsConflationExact.mapSingularityCategory_map_conflationδ`: the functor
  `D_sg(E) ⥤ D_sg(E')` preserves connecting morphisms of conflations.
* `TauCeti.StableConflationExact.map_isProjective`: a stable conflation-exact functor out of a
  Frobenius exact structure preserves projective objects.
* `TauCeti.StableConflationExact.stableToSingularityCompMapSingularityCategoryIso_commShift`: the
  comparison is compatible with the shifts.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti.ExactStructure.IsConflationExact

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F)
  (hP : ∀ {X : C}, E.isProjective X → E'.isProjective (F.obj X))

/-- The functor `D_sg(E) ⥤ D_sg(E')` preserves connecting morphisms of conflations. -/
@[reassoc]
theorem mapSingularityCategory_map_conflationδ {S : ShortComplex C} (hS : E.Conflation S) :
    (hF.mapSingularityCategory hP).map ((SingularityCategory.Q E).map
        (BoundedDerivedCategory.conflationδ hS)) ≫
      (hF.mapSingularityCategory hP).map
        (((SingularityCategory.Q E).commShiftIso (1 : ℤ)).hom.app _) ≫
      ((hF.mapSingularityCategory hP).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((hF.mapSingularityCategoryFactors hP).hom.app _)⟦(1 : ℤ)⟧' ≫
      ((SingularityCategory.Q E').map
        ((hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app S.X₁))⟦(1 : ℤ)⟧' =
    (hF.mapSingularityCategoryFactors hP).hom.app _ ≫ (SingularityCategory.Q E').map
      ((hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app S.X₃) ≫
      (SingularityCategory.Q E').map (BoundedDerivedCategory.conflationδ (hF.map_conflation hS)) ≫
      ((SingularityCategory.Q E').commShiftIso (1 : ℤ)).hom.app _ := by
  have h := NatTrans.shift_app_comm (hF.mapSingularityCategoryFactors hP).hom (1 : ℤ)
    ((BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj S.X₁))
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at h
  simp only [Functor.comp_obj, Category.assoc] at h
  rw [← Functor.map_comp_assoc (SingularityCategory.Q E'),
    ← hF.mapBoundedDerivedCategory_map_conflationδ hS]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% h,
    mapSingularityCategoryFactors_hom_naturality_assoc, ← Functor.commShiftIso_hom_naturality,
    Functor.comp_obj, ShortComplex.map_X₁]

end TauCeti.ExactStructure.IsConflationExact

namespace TauCeti.StableConflationExact

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : StableConflationExact E E' F) (hE : E.IsFrobenius)

include hF hE in
/-- A stable conflation-exact functor out of a Frobenius exact category preserves projective
objects. -/
theorem map_isProjective {X : C} (hX : E.isProjective X) : E'.isProjective (F.obj X) :=
  ((E'.projectiveInjective_iff _).1 (hF.map_projectiveInjective
    ((E.projectiveInjective_iff _).2 ⟨hX, (hE.projective_iff_injective X).1 hX⟩))).1

/-- On the image of a morphism of `C`, the stable functor is the image of `F`. -/
theorem stableFunctor_map_projectiveStableFunctor_map_eq {X Y : C} (f : X ⟶ Y) :
    (hF.stableFunctor hE).map (E.projectiveStableFunctor.map f) =
      eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X) ≫
        E'.projectiveStableFunctor.map (F.map f) ≫
          eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE Y).symm := by
  rw [← cancel_mono (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE Y)),
    hF.stableFunctor_map_projectiveStableFunctor_map hE f]
  simp

/-- **The Keller–Vossieck functors commute with stable functors**: for a stable conflation-exact
functor `F` out of a Frobenius exact category, `stable(E) ⥤ D_sg(E) ⥤ D_sg(E')` is isomorphic to
`stable(E) ⥤ stable(E') ⥤ D_sg(E')`. -/
noncomputable def stableToSingularityCompMapSingularityCategoryIso :
    E.stableToSingularity ⋙ hF.isConflationExact.mapSingularityCategory (hF.map_isProjective hE) ≅
      hF.stableFunctor hE ⋙ E'.stableToSingularity :=
  CategoryTheory.Quotient.natIsoLift _ (NatIso.ofComponents
    (fun A ↦ eqToIso (congrArg (hF.isConflationExact.mapSingularityCategory _).obj
        (E.stableToSingularity_obj_projectiveStableFunctor_obj A)) ≪≫
      (hF.isConflationExact.singleToSingularityCompMapSingularityCategoryIso
        (hF.map_isProjective hE)).app A ≪≫
      eqToIso ((congrArg E'.stableToSingularity.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A)).trans
          (E'.stableToSingularity_obj_projectiveStableFunctor_obj (F.obj A))).symm)
    (fun {A B} f ↦ by
      have h := (hF.isConflationExact.singleToSingularityCompMapSingularityCategoryIso
        (hF.map_isProjective hE)).hom.naturality f
      simp only [Functor.comp_map] at h
      simp only [Functor.comp_map,
        ExactStructure.stableToSingularity_map_projectiveStableFunctor_map,
        stableFunctor_map_projectiveStableFunctor_map_eq, Functor.map_comp, eqToHom_map,
        Iso.trans_hom, eqToIso.hom, Iso.app_hom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, reassoc_of% h, eqToHom_trans]))

/-- On the class of an object `A`, the comparison is the comparison of `mapSingularityCategory`
with placing `A` in degree zero. -/
theorem stableToSingularityCompMapSingularityCategoryIso_hom_app (A : C) :
    (hF.stableToSingularityCompMapSingularityCategoryIso hE).hom.app
        (E.projectiveStableFunctor.obj A) =
      eqToHom (congrArg (hF.isConflationExact.mapSingularityCategory _).obj
        (E.stableToSingularity_obj_projectiveStableFunctor_obj A)) ≫
      (hF.isConflationExact.singleToSingularityCompMapSingularityCategoryIso
        (hF.map_isProjective hE)).hom.app A ≫
      eqToHom ((congrArg E'.stableToSingularity.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A)).trans
          (E'.stableToSingularity_obj_projectiveStableFunctor_obj (F.obj A))).symm :=
  (rfl)

variable (hE' : E'.IsFrobenius)

/-- On the class of an object `A`, the suspension comparison of the stable functor is the
connecting map of the image of the suspension presentation of `A`. -/
theorem stableSuspensionCompStableFunctorIso_hom_app_eq_connectingMap (A : C) :
    (hF.stableSuspensionCompStableFunctorIso hE hE').hom.app (E.projectiveStableFunctor.obj A) =
      eqToHom (congrArg (hF.stableFunctor hE).obj
        (hE.stableSuspension_obj_projectiveStableFunctor_obj A)) ≫
      eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE (hE.suspensionObj A)) ≫
      E'.projectiveStableFunctor.map (hE'.connectingMap
        (hF.isConflationExact.map_conflation (hE.suspensionPresentation A).conflation)) ≫
      eqToHom (hE'.stableSuspension_obj_projectiveStableFunctor_obj (F.obj A)).symm ≫
      eqToHom (congrArg hE'.stableSuspension.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A)).symm := by
  have hc : E'.projectiveStableFunctor.map
      (F.map (hE.connectingMap (hE.suspensionPresentation A).conflation)) = 𝟙 _ := by
    have h := hF.stableFunctor_map_projectiveStableFunctor_map hE
      (hE.connectingMap (hE.suspensionPresentation A).conflation)
    rw [hE.projectiveStableFunctor_map_connectingMap_suspensionPresentation,
      CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact (cancel_epi (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE _))).1
      (h.symm.trans (Category.comp_id _).symm)
  have h := hF.map_connectingMap_comp_suspensionComparison hE hE'
    (hE.suspensionPresentation A).conflation
  rw [hc, Category.id_comp] at h
  rw [stableSuspensionCompStableFunctorIso_hom_app,
    ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_hom, reassoc_of% h]

/-- The comparison intertwines the commutations of the two Keller–Vossieck functors with
suspension, through the commutations of the functors on stable categories and on singularity
categories with suspension and with the shift by one. -/
theorem stableToSingularityCompMapSingularityCategoryIso_suspension :
    Functor.whiskerRight hE.stableSuspensionCompStableToSingularityIso.hom
        (hF.isConflationExact.mapSingularityCategory (hF.map_isProjective hE)) ≫
      Functor.whiskerLeft E.stableToSingularity
        ((hF.isConflationExact.mapSingularityCategory (hF.map_isProjective hE)).commShiftIso
          (1 : ℤ)).hom ≫
      Functor.whiskerRight (hF.stableToSingularityCompMapSingularityCategoryIso hE).hom
        (shiftFunctor _ (1 : ℤ)) =
    Functor.whiskerLeft hE.stableSuspension
        (hF.stableToSingularityCompMapSingularityCategoryIso hE).hom ≫
      Functor.whiskerRight (hF.stableSuspensionCompStableFunctorIso hE hE').hom
        E'.stableToSingularity ≫
      Functor.whiskerLeft (hF.stableFunctor hE)
        hE'.stableSuspensionCompStableToSingularityIso.hom := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext A
  dsimp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  have hδ := hE'.stableToSingularity_map_connectingMap_comp
    (hF.isConflationExact.map_conflation (hE.suspensionPresentation A).conflation)
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
  rw [NatTrans.congr (hF.stableToSingularityCompMapSingularityCategoryIso hE).hom
      (hE.stableSuspension_obj_projectiveStableFunctor_obj A),
    NatTrans.congr hE'.stableSuspensionCompStableToSingularityIso.hom
      (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A),
    NatTrans.congr ((hF.isConflationExact.mapSingularityCategory
      (hF.map_isProjective hE)).commShiftIso (1 : ℤ)).hom
      ((E.stableToSingularity_obj_projectiveStableFunctor_obj A).trans
        (E.singleToSingularity_obj A))]
  simp only [stableToSingularityCompMapSingularityCategoryIso_hom_app,
    stableSuspensionCompStableFunctorIso_hom_app_eq_connectingMap,
    ExactStructure.IsFrobenius.stableSuspensionCompStableToSingularityIso_hom_app,
    hE.stableToSingularitySuspensionMap_eq,
    ExactStructure.IsConflationExact.singleToSingularityCompMapSingularityCategoryIso_hom_app,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, ExactStructure.stableToSingularityObjIso_hom,
    ExactStructure.stableToSingularityObjIso_inv]
  have hM := hF.isConflationExact.mapSingularityCategory_map_conflationδ
    (hF.map_isProjective hE) (hE.suspensionPresentation A).conflation
  dsimp only at hM
  rw [reassoc_of% hδ, reassoc_of% hM]
  simp only [ExactStructure.stableToSingularityObjIso_hom, eqToHom_map, eqToHom_refl,
    ExactStructure.stableToSingularityObjIso_inv, Category.id_comp, eqToHom_trans,
    eqToHom_trans_assoc]
  -- The two sides agree up to unfolding the abbreviation `suspensionObj` and `ShortComplex.map`.
  rfl

/-- **The comparison of the Keller–Vossieck functors is an isomorphism of triangle functors**:
it is compatible with the shifts. -/
theorem stableToSingularityCompMapSingularityCategoryIso_commShift :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := hE.stableToSingularityCommShift
    letI := hE'.stableToSingularityCommShift
    letI := hF.stableFunctorCommShift hE hE'
    NatTrans.CommShift (hF.stableToSingularityCompMapSingularityCategoryIso hE).hom ℤ := by
  let _ := hE.stableHasShift
  let _ := hE'.stableHasShift
  let _ := hE.stableToSingularityCommShift
  let _ := hE'.stableToSingularityCommShift
  let _ := hF.stableFunctorCommShift hE hE'
  refine natTrans_commShift_iff_one.mpr ⟨?_⟩
  ext X
  have hs := congr_app (hF.stableToSingularityCompMapSingularityCategoryIso_suspension hE hE') X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hs ⊢
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
    hE.stableToSingularity_commShiftIso_one_hom_app,
    hE'.stableToSingularity_commShiftIso_one_hom_app, hF.stableFunctorCommShift_iso_one hE hE']
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  have hn := (hF.stableToSingularityCompMapSingularityCategoryIso hE).hom.naturality
    (hE.stableShiftFunctorOneIso.hom.app X)
  simp only [Functor.comp_map] at hn
  rw [hs, ← reassoc_of% hn, ← Functor.map_comp_assoc E'.stableToSingularity
    (hE'.stableShiftFunctorOneIso.inv.app _), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

end TauCeti.StableConflationExact
