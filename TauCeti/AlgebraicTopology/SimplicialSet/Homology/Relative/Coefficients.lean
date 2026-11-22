/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coefficients
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
/-!
# Coefficient change for relative simplicial homology

Adapts `SSet.chainComplexFunctorObjCompMapIso` and `SimplicialSet.Homology.Coefficients` to
`SSetPair` in preadditive `[CategoryWithHomology]` categories with `w`-coproducts, using the
degreewise `IsSplitMono` instance from `SimplicialSet.Homology.Relative.Basic` (Hatcher, §3.A):
* `SSetPair.homologyNatTransOfCoefficients` and `homologyNatIsoOfCoefficientsIso`:
  coefficient-change naturality on relative simplicial homology.
* `CokernelCofork.isColimitMapOfIsSplitMono` / `SSetPair.isColimitMapCokernelCofork`: additive
  preservation of the split cokernel cofork via `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel`.
* `SSetPair.chainComplexObjMapIso`, `chainComplexFunctorObjCompMapIso`, `homologyFunctorObjCompIso`:
  `F (C(P; R)) ≅ C(P; F R)` and `F (Hₙ(P; R)) ≅ Hₙ(P; F R)` for exact coproduct-preserving `F`.
Feeds relative singular/local homology coefficient change and scalar extension of orientations.
-/
public noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe w v v' u u'
namespace CategoryTheory.Limits.CokernelCofork
/-- An additive functor preserves any colimit cokernel cofork of a split monomorphism. -/
def isColimitMapOfIsSplitMono {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {X Y : C} {f : X ⟶ Y}
    [IsSplitMono f] {c : CokernelCofork f} (hc : IsColimit c) : IsColimit (c.map F) := by
  haveI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have hb := isBinaryBilimitOfPreserves F (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hc)
  exact IsColimit.ofIsoColimit (BinaryBicone.isColimitInlCokernelCofork hb.isColimit)
    (Cofork.ext (Iso.refl _) ((Category.comp_id _).trans (CokernelCofork.map_π c F).symm))
end CategoryTheory.Limits.CokernelCofork
namespace SSetPair
open CategoryTheory.Functor (whiskerRight isoWhiskerLeft isoWhiskerRight)
open HomologicalComplex (homologyMap)
section CoefficientsMap
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C] {R R' R'' : C}
/-- A coefficient morphism `φ : R ⟶ R'` induces a natural transformation on relative homology. -/
def homologyNatTransOfCoefficients (φ : R ⟶ R') (n : ℕ) :
    homologyFunctor.{w} R n ⟶ homologyFunctor.{w} R' n :=
  whiskerRight ((chainComplexFunctor C).map φ) (HomologicalComplex.homologyFunctor C _ n)
@[simp] lemma homologyNatTransOfCoefficients_app (φ : R ⟶ R') (n : ℕ) (P : SSetPair.{w}) :
    (homologyNatTransOfCoefficients φ n).app P =
      homologyMap (((chainComplexFunctor C).map φ).app P) n := (rfl)
@[simp] lemma homologyNatTransOfCoefficients_id (R : C) (n : ℕ) :
    homologyNatTransOfCoefficients.{w} (𝟙 R) n = 𝟙 _ :=
  (congrArg (whiskerRight · _) ((chainComplexFunctor C).map_id R)).trans (Functor.whiskerRight_id _)
@[simp] lemma homologyNatTransOfCoefficients_comp (φ : R ⟶ R') (ψ : R' ⟶ R'') (n : ℕ) :
    homologyNatTransOfCoefficients.{w} (φ ≫ ψ) n =
      homologyNatTransOfCoefficients φ n ≫ homologyNatTransOfCoefficients ψ n :=
  (congrArg (whiskerRight · _) ((chainComplexFunctor C).map_comp φ ψ)).trans
    (Functor.whiskerRight_comp _ _ _)
variable (e : R ≅ R')
/-- A coefficient iso `e : R ≅ R'` induces a natural isomorphism on relative homology. -/
def homologyNatIsoOfCoefficientsIso (n : ℕ) : homologyFunctor.{w} R n ≅ homologyFunctor.{w} R' n :=
  isoWhiskerRight ((chainComplexFunctor C).mapIso e) (HomologicalComplex.homologyFunctor C _ n)
@[simp] lemma homologyNatIsoOfCoefficientsIso_hom (n : ℕ) :
    (homologyNatIsoOfCoefficientsIso.{w} e n).hom = homologyNatTransOfCoefficients e.hom n := (rfl)
@[simp] lemma homologyNatIsoOfCoefficientsIso_inv (n : ℕ) :
    (homologyNatIsoOfCoefficientsIso.{w} e n).inv = homologyNatTransOfCoefficients e.inv n := (rfl)
@[simp] lemma homologyNatIsoOfCoefficientsIso_refl (R : C) (n : ℕ) :
    homologyNatIsoOfCoefficientsIso.{w} (Iso.refl R) n = Iso.refl _ :=
  Iso.ext (homologyNatTransOfCoefficients_id R n)
@[simp] lemma homologyNatIsoOfCoefficientsIso_symm (n : ℕ) : homologyNatIsoOfCoefficientsIso.{w}
    e.symm n = (homologyNatIsoOfCoefficientsIso e n).symm := Iso.ext rfl
@[simp] lemma homologyNatIsoOfCoefficientsIso_trans (e₁ : R ≅ R') (e₂ : R' ≅ R'') (n : ℕ) :
    homologyNatIsoOfCoefficientsIso.{w} (e₁ ≪≫ e₂) n =
      homologyNatIsoOfCoefficientsIso e₁ n ≪≫ homologyNatIsoOfCoefficientsIso e₂ n :=
  Iso.ext (homologyNatTransOfCoefficients_comp e₁.hom e₂.hom n)
end CoefficientsMap
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasCoproducts.{w} C]
/-- Any additive functor `F : C ⥤ D` preserves `C(P.left; R) ⟶ C(P.right; R) ⟶ C(P; R)`. -/
def isColimitMapCokernelCofork (F : C ⥤ D) [F.Additive] (R : C) (P : SSetPair.{w}) :
    IsColimit ((P.cokernelCoforkChainComplex R).map (F.mapHomologicalComplex (.down ℕ))) :=
  HomologicalComplex.isColimitOfEval _ _ fun n ↦ (((P.cokernelCoforkChainComplex R).map
    (F.mapHomologicalComplex _)).isColimitMapCoconeEquiv (HomologicalComplex.eval D _ n)).symm <|
    IsColimit.ofIsoColimit (CokernelCofork.isColimitMapOfIsSplitMono F
      (P.isColimitCokernelCoforkChainComplexX R n)) (Cofork.ext (Iso.refl _) (by
      simp [CokernelCofork.map_π, cokernelCoforkChainComplex, cokernelCoforkChainComplexX]))
variable [HasCoproducts.{w} D]
  (F : C ⥤ D) [F.Additive] [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] (R : C)
private def chainComplexMapArrowIso (P : SSetPair.{w}) :
    Arrow.mk ((F.mapHomologicalComplex (.down ℕ)).map (SSet.chainComplexMap P.hom R)) ≅
      Arrow.mk (SSet.chainComplexMap P.hom (F.obj R)) :=
  Arrow.isoMk ((SSet.chainComplexFunctorObjCompMapIso F R).app P.left)
    ((SSet.chainComplexFunctorObjCompMapIso F R).app P.right)
    (by simpa using ((SSet.chainComplexFunctorObjCompMapIso F R).hom.naturality P.hom).symm)
/-- **Relative simplicial chains commute with additive coproduct-preserving `F`**: `F C ≅ C F`. -/
def chainComplexObjMapIso (P : SSetPair.{w}) :
    (F.mapHomologicalComplex (.down ℕ)).obj (P.chainComplex R) ≅ P.chainComplex (F.obj R) :=
  CokernelCofork.mapIsoOfIsColimit (isColimitMapCokernelCofork F R P)
    (P.isColimitCokernelCoforkChainComplex (F.obj R)) (chainComplexMapArrowIso F R P)
@[reassoc (attr := simp)] lemma map_chainComplexπ_comp_chainComplexObjMapIso_hom
    (P : SSetPair.{w}) : (F.mapHomologicalComplex (.down ℕ)).map (P.chainComplexπ R) ≫
      (chainComplexObjMapIso F R P).hom =
      ((SSet.chainComplexFunctorObjCompMapIso F R).app P.right).hom ≫ P.chainComplexπ (F.obj R) :=
  CokernelCofork.π_mapOfIsColimit (P.cokernelCoforkChainComplex (F.obj R))
    (isColimitMapCokernelCofork F R P) (chainComplexMapArrowIso F R P).hom
@[reassoc (attr := simp)] lemma chainComplexπ_comp_chainComplexObjMapIso_inv (P : SSetPair.{w}) :
    P.chainComplexπ (F.obj R) ≫ (chainComplexObjMapIso F R P).inv =
      ((SSet.chainComplexFunctorObjCompMapIso F R).app P.right).inv ≫
        (F.mapHomologicalComplex (.down ℕ)).map (P.chainComplexπ R) :=
  CokernelCofork.π_mapOfIsColimit
    ((P.cokernelCoforkChainComplex R).map (F.mapHomologicalComplex (.down ℕ)))
    (P.isColimitCokernelCoforkChainComplex (F.obj R)) (chainComplexMapArrowIso F R P).inv
@[reassoc] lemma map_chainComplexMap_comp_chainComplexObjMapIso_hom {P P' : SSetPair.{w}}
    (f : P ⟶ P') : (F.mapHomologicalComplex (.down ℕ)).map (chainComplexMap f R) ≫
      (chainComplexObjMapIso F R P').hom =
      (chainComplexObjMapIso F R P).hom ≫ chainComplexMap f (F.obj R) := by
  refine Cofork.IsColimit.hom_ext (isColimitMapCokernelCofork F R P) ?_
  simp only [CokernelCofork.map_π, cokernelCoforkChainComplex, CokernelCofork.π_ofπ]
  rw [← Functor.map_comp_assoc, ← chainComplexπ_naturality, Functor.map_comp_assoc,
    map_chainComplexπ_comp_chainComplexObjMapIso_hom,
    map_chainComplexπ_comp_chainComplexObjMapIso_hom_assoc, ← chainComplexπ_naturality]
  simpa using (SSet.chainComplexFunctorObjCompMapIso F R).hom.naturality_assoc f.right
    (P'.chainComplexπ (F.obj R))
/-- **Relative simplicial chains commute naturally with additive coproduct-preserving `F`**. -/
def chainComplexFunctorObjCompMapIso : (chainComplexFunctor C).obj R ⋙
    F.mapHomologicalComplex (.down ℕ) ≅ (chainComplexFunctor D).obj (F.obj R) :=
  NatIso.ofComponents (chainComplexObjMapIso F R)
    (map_chainComplexMap_comp_chainComplexObjMapIso_hom F R)
@[simp] lemma chainComplexFunctorObjCompMapIso_hom_app (P : SSetPair.{w}) :
    (chainComplexFunctorObjCompMapIso F R).hom.app P = (chainComplexObjMapIso F R P).hom := (rfl)
@[simp] lemma chainComplexFunctorObjCompMapIso_inv_app (P : SSetPair.{w}) :
    (chainComplexFunctorObjCompMapIso F R).inv.app P = (chainComplexObjMapIso F R P).inv := (rfl)
variable [CategoryWithHomology C] [CategoryWithHomology D] [F.PreservesHomology]
/-- **Relative simplicial homology commutes with exact coproduct-preserving `F`**: `F Hₙ ≅ Hₙ F`. -/
def homologyFunctorObjCompIso (n : ℕ) :
    homologyFunctor.{w} R n ⋙ F ≅ homologyFunctor.{w} (F.obj R) n :=
  isoWhiskerLeft ((chainComplexFunctor C).obj R)
    (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).symm ≪≫
  isoWhiskerRight (chainComplexFunctorObjCompMapIso F R) (HomologicalComplex.homologyFunctor _ _ n)
lemma homologyFunctorObjCompIso_hom_app (n : ℕ) (P : SSetPair.{w}) :
    (homologyFunctorObjCompIso F R n).hom.app P =
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app (P.chainComplex R) ≫
        homologyMap (chainComplexObjMapIso F R P).hom n := (rfl)
lemma homologyFunctorObjCompIso_inv_app (n : ℕ) (P : SSetPair.{w}) :
    (homologyFunctorObjCompIso F R n).inv.app P =
      homologyMap (chainComplexObjMapIso F R P).inv n ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso _ n).hom.app (P.chainComplex R) := (rfl)
@[reassoc] lemma map_homologyπ_comp_homologyFunctorObjCompIso_hom_app (n : ℕ) (P : SSetPair.{w}) :
    F.map (P.homologyπ R n) ≫ (homologyFunctorObjCompIso F R n).hom.app P =
      (SSet.homologyObjIso F R P.right n).hom ≫ P.homologyπ (F.obj R) n := by
  have h := (F.mapHomologicalComplexCompHomologyFunctorIso _ n).inv.naturality (P.chainComplexπ R)
  have hcomm := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (homologyMap · n) (map_chainComplexπ_comp_chainComplexObjMapIso_hom F R P)).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [homologyFunctorObjCompIso_hom_app, SSet.homologyObjIso_hom,
    SSet.homologyFunctorObjCompIso_hom_app]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h)).trans
    (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hcomm)).trans (Category.assoc _ _ _).symm)
end SSetPair
