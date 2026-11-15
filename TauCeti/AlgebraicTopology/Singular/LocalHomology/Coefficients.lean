/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System

/-!
# Changing the category of coefficients in relative and local singular homology

For an additive `w`-coproduct-preserving functor `F : C ⥤ D` between preadditive categories, `F`
preserves simplicial chains (`SSet.chainComplexFunctorObjCompMapIso`) and maps the degreewise split
cofork `C(P.left; R) ⟶ C(P.right; R) ⟶ C(P; R)` to a colimit
(`SSetPair.isColimitMapCokernelCofork`), giving `SSetPair.chainComplexFunctorObjCompMapIso`. When
`F` preserves homology, it commutes with simplicial, relative, and local homology
(`SSet.homologyFunctorObjCompIso`, `SSetPair.homologyFunctorObjCompIso`,
`TopPair.singularHomologyObjCompIso`, `TauCeti.localHomologyObjCompIso`), compatibly with quotient
maps, restrictions, maps, and transport
(`TauCeti.map_localHomologyTransport_comp_localHomologyObjCompIso_hom`), as do `R ≅ R'`
(`TauCeti.localHomologyIsoOfCoefficientsIso`). Specializing to exact `ModuleCat.extendScalars f`
along `f : R →+* S` gives `TauCeti.singularHomologyExtendScalarsIso` and
`TauCeti.localHomologyExtendScalarsIso`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §3.A, §3.3.
-/

public section
noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped ChangeOfRings Simplicial

universe w v v' u u'

namespace SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

/-- A morphism of coefficient objects `φ : R ⟶ R'` induces a natural transformation on simplicial
homology. -/
def homologyNatTransOfCoefficients {R R' : C} (φ : R ⟶ R') (n : ℕ) :
    SSet.homologyFunctor.{w} R n ⟶ SSet.homologyFunctor.{w} R' n :=
  Functor.whiskerRight ((SSet.chainComplexFunctor C).map φ)
    (HomologicalComplex.homologyFunctor C (.down ℕ) n)

/-- An isomorphism of coefficient objects `e : R ≅ R'` induces a natural isomorphism on simplicial
homology. -/
def homologyNatIsoOfCoefficientsIso {R R' : C} (e : R ≅ R') (n : ℕ) :
    SSet.homologyFunctor.{w} R n ≅ SSet.homologyFunctor.{w} R' n :=
  Functor.isoWhiskerRight ((SSet.chainComplexFunctor C).mapIso e)
    (HomologicalComplex.homologyFunctor C (.down ℕ) n)

@[simp] lemma homologyNatIsoOfCoefficientsIso_hom_app {R R' : C} (e : R ≅ R') (n : ℕ)
    (X : SSet.{w}) : (homologyNatIsoOfCoefficientsIso e n).hom.app X =
      HomologicalComplex.homologyMap (((SSet.chainComplexFunctor C).map e.hom).app X) n := (rfl)

@[simp] lemma homologyNatIsoOfCoefficientsIso_inv_app {R R' : C} (e : R ≅ R') (n : ℕ)
    (X : SSet.{w}) : (homologyNatIsoOfCoefficientsIso e n).inv.app X =
      HomologicalComplex.homologyMap (((SSet.chainComplexFunctor C).map e.inv).app X) n := (rfl)

/-- An isomorphism of coefficient objects `e : R ≅ R'` induces an isomorphism on the simplicial
homology of `X`. -/
def homologyIsoOfCoefficientsIso {R R' : C} (e : R ≅ R') (X : SSet.{w}) (n : ℕ) :
    X.homology R n ≅ X.homology R' n := (homologyNatIsoOfCoefficientsIso e n).app X

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]
  [CategoryWithHomology D] (F : C ⥤ D) [F.Additive]
  [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] [F.PreservesHomology] (R : C)

/-- **Simplicial homology commutes with an exact coproduct-preserving functor of coefficients**:
`F (Hₙ(X; R)) ≅ Hₙ(X; F R)`, naturally in `X : SSet`. -/
def homologyFunctorObjCompIso (n : ℕ) :
    SSet.homologyFunctor.{w} R n ⋙ F ≅ SSet.homologyFunctor.{w} (F.obj R) n :=
  Functor.isoWhiskerLeft ((SSet.chainComplexFunctor C).obj R)
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).symm ≪≫
    Functor.isoWhiskerRight (SSet.chainComplexFunctorObjCompMapIso F R)
      (HomologicalComplex.homologyFunctor D (.down ℕ) n)

lemma homologyFunctorObjCompIso_hom_app (n : ℕ) (X : SSet.{w}) :
    (homologyFunctorObjCompIso F R n).hom.app X =
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app (X.chainComplex R) ≫
        (HomologicalComplex.homologyFunctor D (.down ℕ) n).map
          ((SSet.chainComplexFunctorObjCompMapIso F R).hom.app X) := (rfl)

/-- **Simplicial homology of `X` commutes with an exact coproduct-preserving functor of
coefficients**: `F (Hₙ(X; R)) ≅ Hₙ(X; F R)`. -/
def homologyObjCompIso (X : SSet.{w}) (n : ℕ) :
    F.obj (X.homology R n) ≅ X.homology (F.obj R) n := (homologyFunctorObjCompIso F R n).app X

end SSet

namespace SSetPair

section CoefficientsMap

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

/-- A morphism of coefficient objects `φ : R ⟶ R'` induces a natural transformation on relative
simplicial homology. -/
def homologyNatTransOfCoefficients {R R' : C} (φ : R ⟶ R') (n : ℕ) :
    SSetPair.homologyFunctor.{w} R n ⟶ SSetPair.homologyFunctor.{w} R' n where
  app P := HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map φ).app P) n
  naturality _ _ g := by
    dsimp [SSetPair.homologyMap]; rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, ((SSetPair.chainComplexFunctor C).map φ).naturality g]

/-- An isomorphism of coefficient objects `e : R ≅ R'` induces a natural isomorphism on relative
simplicial homology. -/
def homologyNatIsoOfCoefficientsIso {R R' : C} (e : R ≅ R') (n : ℕ) :
    SSetPair.homologyFunctor.{w} R n ≅ SSetPair.homologyFunctor.{w} R' n where
  hom := homologyNatTransOfCoefficients e.hom n
  inv := homologyNatTransOfCoefficients e.inv n
  hom_inv_id := by
    ext P; dsimp [homologyNatTransOfCoefficients]; rw [← HomologicalComplex.homologyMap_comp,
      ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    ext P; dsimp [homologyNatTransOfCoefficients]; rw [← HomologicalComplex.homologyMap_comp,
      ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, HomologicalComplex.homologyMap_id]

@[simp] lemma homologyNatIsoOfCoefficientsIso_hom_app {R R' : C} (e : R ≅ R') (n : ℕ)
    (P : SSetPair.{w}) : (homologyNatIsoOfCoefficientsIso e n).hom.app P =
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map e.hom).app P) n := (rfl)

@[simp] lemma homologyNatIsoOfCoefficientsIso_inv_app {R R' : C} (e : R ≅ R') (n : ℕ)
    (P : SSetPair.{w}) : (homologyNatIsoOfCoefficientsIso e n).inv.app P =
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map e.inv).app P) n := (rfl)

/-- The quotient map `Hₙ(Y; R) ⟶ Hₙ(Y, X; R)` commutes with the isomorphisms induced by `e : R ≅ R'`
on ambient and relative simplicial homology. -/
@[reassoc] lemma homologyIsoOfCoefficientsIso_hom_comp_homologyπ {R R' : C} (e : R ≅ R') (n : ℕ)
    (P : SSetPair.{w}) :
    (SSet.homologyIsoOfCoefficientsIso e P.right n).hom ≫ P.homologyπ R' n =
      P.homologyπ R n ≫ (homologyNatIsoOfCoefficientsIso e n).hom.app P := by
  dsimp only [SSet.homologyIsoOfCoefficientsIso, SSetPair.homologyπ]
  rw [Iso.app_hom, SSet.homologyNatIsoOfCoefficientsIso_hom_app,
    homologyNatIsoOfCoefficientsIso_hom_app,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (HomologicalComplex.homologyMap · n)
    (congrArg (·.app P) ((SSetPair.chainComplexFunctorπ C).naturality e.hom))

end CoefficientsMap

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasCoproducts.{w} C]

/-- For a pair `P` of simplicial sets, the cokernel cofork `C(P.left; R) ⟶ C(P.right; R) ⟶ C(P; R)`
is degreewise split, so any additive functor `F : C ⥤ D` maps it to a colimit cokernel cofork. -/
def isColimitMapCokernelCofork (F : C ⥤ D) [F.Additive] (R : C) (P : SSetPair.{w}) :
    IsColimit ((P.cokernelCoforkChainComplex R).map (F.mapHomologicalComplex (.down ℕ))) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n ↦ (((P.cokernelCoforkChainComplex R).map
    (F.mapHomologicalComplex (.down ℕ))).isColimitMapCoconeEquiv
      (HomologicalComplex.eval D (.down ℕ) n)).symm ?_
  let hc := P.isColimitCokernelCoforkChainComplexX R n
  let fₙ := (SSet.chainComplexMap P.hom R).f n
  have hf0 : fₙ ≫ (𝟙 _ - retraction fₙ ≫ fₙ) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, reassoc_of% (IsSplitMono.id fₙ), sub_self]
  let s : (P.chainComplex R).X n ⟶ (((𝟭 SSet).obj P.right).chainComplex R).X n :=
    hc.desc (CokernelCofork.ofπ _ hf0)
  have hgs : (P.chainComplexπ R).f n ≫ s = 𝟙 _ - retraction fₙ ≫ fₙ :=
    hc.fac _ WalkingParallelPair.one
  have hsg : s ≫ (P.chainComplexπ R).f n = 𝟙 ((P.chainComplex R).X n) := by
    rw [← cancel_epi ((P.chainComplexπ R).f n), reassoc_of% hgs, Preadditive.sub_comp,
      Category.id_comp, Category.assoc, P.chainComplex_condition_f R n, comp_zero, sub_zero,
      Category.comp_id]
  refine CokernelCofork.IsColimit.ofπ _
    (((P.cokernelCoforkChainComplex R).map (F.mapHomologicalComplex (.down ℕ))).map_condition
      (HomologicalComplex.eval D (.down ℕ) n))
    (fun x _ ↦ F.map s ≫ x) (fun x hx ↦ ?_) (fun x _ b hb ↦ ?_)
  · have hx' : F.map fₙ ≫ x = 0 := hx
    have hFgs :
        F.map ((P.chainComplexπ R).f n) ≫ F.map s = 𝟙 _ - F.map (retraction fₙ) ≫ F.map fₙ := by
      simpa using congrArg
        (fun φ : (((𝟭 SSet).obj P.right).chainComplex R).X n ⟶ _ ↦ F.map φ) hgs
    change F.map ((P.chainComplexπ R).f n) ≫ F.map s ≫ x = x
    rw [reassoc_of% hFgs, Preadditive.sub_comp, Category.id_comp, sub_eq_self, Category.assoc, hx',
      comp_zero]
  · let b' : F.obj ((P.chainComplex R).X n) ⟶ _ := b
    have hb' : F.map ((P.chainComplexπ R).f n) ≫ b' = x := hb
    change b' = F.map s ≫ x
    rw [← hb', ← Category.assoc, ← F.map_comp, hsg, F.map_id _, Category.id_comp]

variable [HasCoproducts.{w} D]
  (F : C ⥤ D) [F.Additive] [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] (R : C)

private def chainComplexMapArrowIso (P : SSetPair.{w}) :
    Arrow.mk ((F.mapHomologicalComplex (.down ℕ)).map (SSet.chainComplexMap P.hom R)) ≅
      Arrow.mk (SSet.chainComplexMap P.hom (F.obj R)) :=
  Arrow.isoMk ((SSet.chainComplexFunctorObjCompMapIso F R).app P.left)
    ((SSet.chainComplexFunctorObjCompMapIso F R).app P.right)
    (by simpa using ((SSet.chainComplexFunctorObjCompMapIso F R).hom.naturality P.hom).symm)

/-- **Relative simplicial chains commute with an additive coproduct-preserving functor of
coefficients**: for `P : SSetPair`, applying `F` to `C(P; R)` gives `C(P; F R)`. -/
def chainComplexObjMapIso (P : SSetPair.{w}) :
    (F.mapHomologicalComplex (.down ℕ)).obj (P.chainComplex R) ≅ P.chainComplex (F.obj R) :=
  CokernelCofork.mapIsoOfIsColimit (isColimitMapCokernelCofork F R P)
    (P.isColimitCokernelCoforkChainComplex (F.obj R)) (chainComplexMapArrowIso F R P)

/-- The quotient map from ambient to relative simplicial chains commutes with
`SSetPair.chainComplexObjMapIso`. -/
@[reassoc (attr := simp)]
lemma map_chainComplexπ_comp_chainComplexObjMapIso_hom (P : SSetPair.{w}) :
    (F.mapHomologicalComplex (.down ℕ)).map (P.chainComplexπ R) ≫
        (chainComplexObjMapIso F R P).hom =
      ((SSet.chainComplexFunctorObjCompMapIso F R).app P.right).hom ≫
        P.chainComplexπ (F.obj R) :=
  CokernelCofork.π_mapOfIsColimit (isColimitMapCokernelCofork F R P)
    (P.cokernelCoforkChainComplex (F.obj R)) (chainComplexMapArrowIso F R P).hom

/-- The inverse of `SSetPair.chainComplexObjMapIso` intertwines the quotient maps from ambient to
relative simplicial chains. -/
@[reassoc (attr := simp)] lemma chainComplexπ_comp_chainComplexObjMapIso_inv (P : SSetPair.{w}) :
    P.chainComplexπ (F.obj R) ≫ (chainComplexObjMapIso F R P).inv =
      ((SSet.chainComplexFunctorObjCompMapIso F R).app P.right).inv ≫
        (F.mapHomologicalComplex (.down ℕ)).map (P.chainComplexπ R) :=
  CokernelCofork.π_mapOfIsColimit (P.isColimitCokernelCoforkChainComplex (F.obj R))
    ((P.cokernelCoforkChainComplex R).map (F.mapHomologicalComplex (.down ℕ)))
    (chainComplexMapArrowIso F R P).inv

/-- `SSetPair.chainComplexObjMapIso` is natural in morphisms of simplicial-set pairs. -/
@[reassoc] lemma map_chainComplexMap_comp_chainComplexObjMapIso_hom {P P' : SSetPair.{w}}
    (f : P ⟶ P') :
    (F.mapHomologicalComplex (.down ℕ)).map (SSetPair.chainComplexMap f R) ≫
        (chainComplexObjMapIso F R P').hom =
      (chainComplexObjMapIso F R P).hom ≫ SSetPair.chainComplexMap f (F.obj R) := by
  refine Cofork.IsColimit.hom_ext (isColimitMapCokernelCofork F R P) ?_
  change (F.mapHomologicalComplex (.down ℕ)).map (P.chainComplexπ R) ≫ _ =
    (F.mapHomologicalComplex (.down ℕ)).map (P.chainComplexπ R) ≫ _
  rw [← Functor.map_comp_assoc, ← chainComplexπ_naturality, Functor.map_comp_assoc,
    map_chainComplexπ_comp_chainComplexObjMapIso_hom,
    map_chainComplexπ_comp_chainComplexObjMapIso_hom_assoc, ← chainComplexπ_naturality]
  simpa using (SSet.chainComplexFunctorObjCompMapIso F R).hom.naturality_assoc f.right
    (P'.chainComplexπ (F.obj R))

/-- **Relative simplicial chains commute with an additive coproduct-preserving functor of
coefficients**, naturally in the pair. -/
def chainComplexFunctorObjCompMapIso :
    (SSetPair.chainComplexFunctor C).obj R ⋙ F.mapHomologicalComplex (.down ℕ) ≅
      (SSetPair.chainComplexFunctor D).obj (F.obj R) :=
  NatIso.ofComponents (chainComplexObjMapIso F R) fun f ↦
    map_chainComplexMap_comp_chainComplexObjMapIso_hom F R f

@[simp] lemma chainComplexFunctorObjCompMapIso_hom_app (P : SSetPair.{w}) :
    (chainComplexFunctorObjCompMapIso F R).hom.app P = (chainComplexObjMapIso F R P).hom := (rfl)

@[simp] lemma chainComplexFunctorObjCompMapIso_inv_app (P : SSetPair.{w}) :
    (chainComplexFunctorObjCompMapIso F R).inv.app P = (chainComplexObjMapIso F R P).inv := (rfl)

variable [CategoryWithHomology C] [CategoryWithHomology D] [F.PreservesHomology]

/-- **Relative simplicial homology commutes with an exact functor of coefficients**:
`F (Hₙ(P; R)) ≅ Hₙ(P; F R)`, naturally in the pair `P`. -/
def homologyFunctorObjCompIso (n : ℕ) :
    SSetPair.homologyFunctor.{w} R n ⋙ F ≅ SSetPair.homologyFunctor.{w} (F.obj R) n :=
  Functor.isoWhiskerLeft ((SSetPair.chainComplexFunctor C).obj R)
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).symm ≪≫
    Functor.isoWhiskerRight (chainComplexFunctorObjCompMapIso F R)
      (HomologicalComplex.homologyFunctor D (.down ℕ) n)

lemma homologyFunctorObjCompIso_hom_app (n : ℕ) (P : SSetPair.{w}) :
    (homologyFunctorObjCompIso F R n).hom.app P =
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app (P.chainComplex R) ≫
        (HomologicalComplex.homologyFunctor D (.down ℕ) n).map (chainComplexObjMapIso F R P).hom :=
  (rfl)

/-- The quotient map `Hₙ(Y; R) ⟶ Hₙ(Y, X; R)` commutes with the coefficient-functor comparison
on absolute and relative simplicial homology. -/
@[reassoc] lemma map_homologyπ_comp_homologyFunctorObjCompIso_hom_app (n : ℕ) (P : SSetPair.{w}) :
    F.map (P.homologyπ R n) ≫ (homologyFunctorObjCompIso F R n).hom.app P =
      (SSet.homologyObjCompIso F R P.right n).hom ≫ P.homologyπ (F.obj R) n := by
  let H := HomologicalComplex.homologyFunctor D (.down ℕ) n
  let e := F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n
  change F.map ((HomologicalComplex.homologyFunctor C (.down ℕ) n).map (P.chainComplexπ R)) ≫
      (e.inv.app (P.chainComplex R) ≫ H.map (chainComplexObjMapIso F R P).hom) =
    (e.inv.app (P.right.chainComplex R) ≫
      H.map ((SSet.chainComplexFunctorObjCompMapIso F R).hom.app P.right)) ≫
      H.map (P.chainComplexπ (F.obj R))
  rw [reassoc_of% (e.inv.naturality (P.chainComplexπ R)), ← CategoryTheory.Functor.map_comp,
    map_chainComplexπ_comp_chainComplexObjMapIso_hom, Iso.app_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]

end SSetPair

namespace TopPair

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasCoproducts.{w} C] [HasCoproducts.{w} D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.Additive] [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F]
  [F.PreservesHomology] (R : C)

/-- **Relative singular homology commutes with an exact functor of coefficients**:
`F (Hₙ(P; R)) ≅ Hₙ(P; F R)` for a topological pair `P`. -/
def singularHomologyObjCompIso (P : TopPair.{w}) (n : ℕ) :
    F.obj (P.singularHomology R n) ≅ P.singularHomology (F.obj R) n :=
  (SSetPair.homologyFunctorObjCompIso F R n).app (toSSetPair.obj P)

/-- `TopPair.singularHomologyObjCompIso` is natural in maps of topological pairs. -/
@[reassoc] lemma map_singularHomologyMap_comp_singularHomologyObjCompIso_hom {P P' : TopPair.{w}}
    (f : P ⟶ P') (n : ℕ) :
    F.map (TopPair.singularHomologyMap f R n) ≫ (singularHomologyObjCompIso F R P' n).hom =
      (singularHomologyObjCompIso F R P n).hom ≫ TopPair.singularHomologyMap f (F.obj R) n :=
  (SSetPair.homologyFunctorObjCompIso F R n).hom.naturality (toSSetPair.map f)

/-- The quotient map `Hₙ(X; R) ⟶ Hₙ(X, A; R)` commutes with the coefficient-functor comparison
on absolute and relative singular homology. -/
@[reassoc] lemma map_singularHomologyπ_comp_singularHomologyObjCompIso_hom (P : TopPair.{w})
    (n : ℕ) :
    F.map (P.singularHomologyπ R n) ≫ (singularHomologyObjCompIso F R P n).hom =
      (SSet.homologyObjCompIso F R (TopCat.toSSet.obj P.fst) n).hom ≫
        P.singularHomologyπ (F.obj R) n :=
  SSetPair.map_homologyπ_comp_homologyFunctorObjCompIso_hom_app F R n (toSSetPair.obj P)

end TopPair

namespace TauCeti

/-- `TauCeti.singularHomologyToLocalHomology` is the underlying linear map of the quotient morphism
`TopPair.singularHomologyπ` onto `Hₖ(M, M ∖ {x}; N)`. -/
theorem singularHomologyToLocalHomology_eq_singularHomologyπ {M : Type w} [TopologicalSpace M]
    {Λ : Type u} [Ring Λ] (N : ModuleCat.{w} Λ) (x : M) (k : ℕ) :
    singularHomologyToLocalHomology N x k =
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N k).hom := by
  have h : (TopPair.ofSubset ((Set.univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
      (C := ModuleCat.{w} Λ) N k ≫ localHomologyRestriction N (Set.subset_univ {x}) k =
      (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N k := by
    rw [localHomologyRestriction_def]
    exact TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id N
      (Set.compl_subset_compl.2 (Set.subset_univ {x})) k
  ext μ; rw [singularHomologyToLocalHomology_apply]; exact ConcreteCategory.congr_hom h μ

section Coefficients

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]

section Iso
variable {R R' : A} (e : R ≅ R')

/-- An isomorphism of coefficient objects `e : R ≅ R'` induces an isomorphism on local homology. -/
def localHomologyIsoOfCoefficientsIso {M : Type w} [TopologicalSpace M] (S : Set M) (k : ℕ) :
    localHomology R S k ≅ localHomology R' S k :=
  (SSetPair.homologyNatIsoOfCoefficientsIso e k).app
    (TopPair.toSSetPair.obj (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))))

@[reassoc] lemma localHomologyRestriction_comp_localHomologyIsoOfCoefficientsIso_hom {M : Type w}
    [TopologicalSpace M] {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    localHomologyRestriction R h k ≫ (localHomologyIsoOfCoefficientsIso e S k).hom =
      (localHomologyIsoOfCoefficientsIso e T k).hom ≫ localHomologyRestriction R' h k := by
  rw [localHomologyRestriction_def, localHomologyRestriction_def]
  exact (SSetPair.homologyNatIsoOfCoefficientsIso e k).hom.naturality _

@[reassoc] lemma localHomologyMap_comp_localHomologyIsoOfCoefficientsIso_hom {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (j : C(M, N)) {S : Set M} {T : Set N}
    (h : j ⁻¹' T ⊆ S) (k : ℕ) :
    localHomologyMap R j h k ≫ (localHomologyIsoOfCoefficientsIso e T k).hom =
      (localHomologyIsoOfCoefficientsIso e S k).hom ≫ localHomologyMap R' j h k := by
  rw [localHomologyMap_def, localHomologyMap_def]
  exact (SSetPair.homologyNatIsoOfCoefficientsIso e k).hom.naturality _

@[reassoc] lemma localHomologyTransport_comp_localHomologyIsoOfCoefficientsIso_hom {M E : Type w}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport R M E k f ≫ (localHomologyIsoOfCoefficientsIso e {y.as} k).hom =
      (localHomologyIsoOfCoefficientsIso e {x.as} k).hom ≫ localHomologyTransport R' M E k f := by
  rw [← Iso.inv_comp_eq]
  refine eq_localHomologyTransport R' k
    (fun g ↦ (localHomologyIsoOfCoefficientsIso e _ k).inv ≫
      localHomologyTransport R M E k g ≫ (localHomologyIsoOfCoefficientsIso e _ k).hom)
    (fun g₁ g₂ ↦ by simp [localHomologyTransport_comp]) (fun φ {K} hK hKc hKφ {a b} γ hγ ↦ ?_) f
  have h0 : localHomologyRestriction R' (Set.singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
      (localHomologyIsoOfCoefficientsIso e {a} k).inv =
        (localHomologyIsoOfCoefficientsIso e (φ.symm '' K) k).inv ≫
          localHomologyRestriction R (Set.singleton_subset_iff.2 (γ.source ▸ hγ 0)) k := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      localHomologyRestriction_comp_localHomologyIsoOfCoefficientsIso_hom]
  rw [reassoc_of% h0,
    reassoc_of% (localHomologyRestriction_comp_localHomologyTransport R φ hK hKc hKφ γ hγ k),
    localHomologyRestriction_comp_localHomologyIsoOfCoefficientsIso_hom, Iso.inv_hom_id_assoc]

end Iso

/-- `TauCeti.localHomologyIsoOfCoefficientsIso` and `SSet.homologyIsoOfCoefficientsIso` intertwine
`TauCeti.singularHomologyToLocalHomology`. -/
lemma singularHomologyToLocalHomology_homologyIsoOfCoefficientsIso_hom_apply {M : Type w}
    [TopologicalSpace M] {Λ : Type u} [Ring Λ] {N N' : ModuleCat.{w} Λ} (e : N ≅ N') (x : M)
    (k : ℕ) (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology N' x k
        ((SSet.homologyIsoOfCoefficientsIso e (TopCat.toSSet.obj (TopCat.of M)) k).hom μ) =
      (localHomologyIsoOfCoefficientsIso e ({x} : Set M) k).hom
        (singularHomologyToLocalHomology N x k μ) := by
  rw [singularHomologyToLocalHomology_eq_singularHomologyπ,
    singularHomologyToLocalHomology_eq_singularHomologyπ]
  let P : SSetPair.{w} := TopPair.toSSetPair.obj (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)))
  have hcomm : (SSet.homologyIsoOfCoefficientsIso e P.right k).hom ≫ P.homologyπ N' k =
      P.homologyπ N k ≫ ((SSetPair.homologyNatIsoOfCoefficientsIso e k).app P).hom := by
    rw [Iso.app_hom]; exact SSetPair.homologyIsoOfCoefficientsIso_hom_comp_homologyπ e k (P := P)
  exact ConcreteCategory.congr_hom hcomm μ

variable {B : Type u'} [Category.{v'} B] [HasCoproducts.{w} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F]
  [F.PreservesHomology] (R : A)

/-- **Local homology commutes with an exact functor of coefficients**:
`F (Hₖ(M, M ∖ S; R)) ≅ Hₖ(M, M ∖ S; F R)`. -/
def localHomologyObjCompIso {M : Type w} [TopologicalSpace M] (S : Set M) (k : ℕ) :
    F.obj (localHomology R S k) ≅ localHomology (F.obj R) S k :=
  TopPair.singularHomologyObjCompIso F R (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))) k

/-- `TauCeti.localHomologyObjCompIso` commutes with `TauCeti.localHomologyRestriction`. -/
@[reassoc] lemma map_localHomologyRestriction_comp_localHomologyObjCompIso_hom {M : Type w}
    [TopologicalSpace M] {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    F.map (localHomologyRestriction R h k) ≫ (localHomologyObjCompIso F R S k).hom =
      (localHomologyObjCompIso F R T k).hom ≫ localHomologyRestriction (F.obj R) h k := by
  rw [localHomologyRestriction_def, localHomologyRestriction_def]
  exact TopPair.map_singularHomologyMap_comp_singularHomologyObjCompIso_hom F R _ k

/-- `TauCeti.localHomologyObjCompIso` commutes with `TauCeti.localHomologyMap`. -/
@[reassoc] lemma map_localHomologyMap_comp_localHomologyObjCompIso_hom {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (j : C(M, N)) {S : Set M} {T : Set N}
    (h : j ⁻¹' T ⊆ S) (k : ℕ) :
    F.map (localHomologyMap R j h k) ≫ (localHomologyObjCompIso F R T k).hom =
      (localHomologyObjCompIso F R S k).hom ≫ localHomologyMap (F.obj R) j h k := by
  rw [localHomologyMap_def, localHomologyMap_def]
  exact TopPair.map_singularHomologyMap_comp_singularHomologyObjCompIso_hom F R _ k

/-- **Transport of local homology commutes with an exact functor of coefficients.** Along every
path class `f : x ⟶ y`, `F` carries the transport for `R` to the transport for `F R` under
`TauCeti.localHomologyObjCompIso`. -/
@[reassoc] lemma map_localHomologyTransport_comp_localHomologyObjCompIso_hom {M E : Type w}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    F.map (localHomologyTransport R M E k f) ≫ (localHomologyObjCompIso F R {y.as} k).hom =
      (localHomologyObjCompIso F R {x.as} k).hom ≫ localHomologyTransport (F.obj R) M E k f := by
  rw [← Iso.inv_comp_eq]
  refine eq_localHomologyTransport (F.obj R) k
    (fun g ↦ (localHomologyObjCompIso F R _ k).inv ≫
      F.map (localHomologyTransport R M E k g) ≫ (localHomologyObjCompIso F R _ k).hom)
    (fun g₁ g₂ ↦ by simp [localHomologyTransport_comp]) (fun φ {K} hK hKc hKφ {a b} γ hγ ↦ ?_) f
  have h0 : localHomologyRestriction (F.obj R) (Set.singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
      (localHomologyObjCompIso F R {a} k).inv =
        (localHomologyObjCompIso F R (φ.symm '' K) k).inv ≫
          F.map (localHomologyRestriction R (Set.singleton_subset_iff.2 (γ.source ▸ hγ 0)) k) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      map_localHomologyRestriction_comp_localHomologyObjCompIso_hom]
  rw [reassoc_of% h0, ← F.map_comp_assoc,
    localHomologyRestriction_comp_localHomologyTransport R φ hK hKc hKφ γ hγ k,
    map_localHomologyRestriction_comp_localHomologyObjCompIso_hom, Iso.inv_hom_id_assoc]

end Coefficients

section ExtendScalars

variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

/-- The canonical isomorphism `(ModuleCat.extendScalars f).obj (ModuleCat.of R R) ≅`
`ModuleCat.of S S` sending `s ⊗ₜ r` to `f r * s`. -/
def extendScalarsSelfIso :
    (ModuleCat.extendScalars.{w, w, w} f).obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
  letI := f.toAlgebra; (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

@[simp] lemma extendScalarsSelfIso_hom_tmul (s : S) (r : R) :
    (extendScalarsSelfIso f).hom (s ⊗ₜ[R, f] r) = f r * s := (rfl)

@[simp] lemma extendScalarsSelfIso_inv_apply (s : S) :
    (extendScalarsSelfIso f).inv s = s ⊗ₜ[R, f] (1 : R) := (rfl)

variable [PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} f)]

private local instance : (ModuleCat.extendScalars.{w, w, w} f).Additive :=
  Functor.additive_of_preserves_binary_products _
private local instance : PreservesColimitsOfSize.{w, w} (ModuleCat.extendScalars.{w, w, w} f) :=
  (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits

/-- **Extension of scalars commutes with singular homology** along `f : R →+* S` with exact
extension of scalars: `S ⊗[R] Hₖ(M; R) ≅ Hₖ(M; S)`. -/
def singularHomologyExtendScalarsIso (M : Type w) [TopologicalSpace M] (k : ℕ) :
    (ModuleCat.extendScalars.{w, w, w} f).obj
        ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) k) ≅
      (TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of S S) k :=
  SSet.homologyObjCompIso (ModuleCat.extendScalars.{w, w, w} f) (ModuleCat.of R R)
      (TopCat.toSSet.obj (TopCat.of M)) k ≪≫
    SSet.homologyIsoOfCoefficientsIso (extendScalarsSelfIso f)
      (TopCat.toSSet.obj (TopCat.of M)) k

/-- **Extension of scalars commutes with local homology** along `f : R →+* S` with exact extension
of scalars: `S ⊗[R] Hₖ(M, M ∖ A; R) ≅ Hₖ(M, M ∖ A; S)`. -/
def localHomologyExtendScalarsIso {M : Type w} [TopologicalSpace M] (A : Set M) (k : ℕ) :
    (ModuleCat.extendScalars.{w, w, w} f).obj (localHomology (ModuleCat.of R R) A k) ≅
      localHomology (ModuleCat.of S S) A k :=
  localHomologyObjCompIso (ModuleCat.extendScalars.{w, w, w} f) (ModuleCat.of R R) A k ≪≫
    localHomologyIsoOfCoefficientsIso (extendScalarsSelfIso f) A k

/-- `TauCeti.singularHomologyExtendScalarsIso` and `TauCeti.localHomologyExtendScalarsIso`
intertwine `TauCeti.singularHomologyToLocalHomology`. -/
lemma singularHomologyToLocalHomology_singularHomologyExtendScalarsIso_hom_tmul {M : Type w}
    [TopologicalSpace M] (x : M) (k : ℕ) (s : S)
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) k : ModuleCat.{w} R)) :
    singularHomologyToLocalHomology (ModuleCat.of S S) x k
        ((singularHomologyExtendScalarsIso f M k).hom (s ⊗ₜ[R, f] μ)) =
      (localHomologyExtendScalarsIso f {x} k).hom
        (s ⊗ₜ[R, f] singularHomologyToLocalHomology (ModuleCat.of R R) x k μ) := by
  rw [singularHomologyToLocalHomology_eq_singularHomologyπ,
    singularHomologyToLocalHomology_eq_singularHomologyπ]
  let P : SSetPair.{w} := TopPair.toSSetPair.obj (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)))
  have hcomm : (SSet.homologyObjCompIso (ModuleCat.extendScalars.{w, w, w} f) (ModuleCat.of R R)
        P.right k ≪≫ SSet.homologyIsoOfCoefficientsIso (extendScalarsSelfIso f) P.right k).hom ≫
      P.homologyπ (ModuleCat.of S S) k =
    (ModuleCat.extendScalars.{w, w, w} f).map (P.homologyπ (ModuleCat.of R R) k) ≫
      ((SSetPair.homologyFunctorObjCompIso (ModuleCat.extendScalars.{w, w, w} f)
          (ModuleCat.of R R) k).app P ≪≫
        (SSetPair.homologyNatIsoOfCoefficientsIso (extendScalarsSelfIso f) k).app P).hom := by
    simp only [Iso.trans_hom, Iso.app_hom, Category.assoc,
      SSetPair.homologyIsoOfCoefficientsIso_hom_comp_homologyπ,
      SSetPair.map_homologyπ_comp_homologyFunctorObjCompIso_hom_app_assoc]
  exact ConcreteCategory.congr_hom hcomm (s ⊗ₜ[R, f] μ)

/-- `TauCeti.localHomologyExtendScalarsIso` commutes with `TauCeti.localHomologyRestriction`. -/
@[reassoc] lemma map_localHomologyRestriction_comp_localHomologyExtendScalarsIso_hom {M : Type w}
    [TopologicalSpace M] {A B : Set M} (h : A ⊆ B) (k : ℕ) :
    (ModuleCat.extendScalars.{w, w, w} f).map (localHomologyRestriction (ModuleCat.of R R) h k) ≫
        (localHomologyExtendScalarsIso f A k).hom =
      (localHomologyExtendScalarsIso f B k).hom ≫
        localHomologyRestriction (ModuleCat.of S S) h k := by
  simp only [localHomologyExtendScalarsIso, Iso.trans_hom, Category.assoc,
    map_localHomologyRestriction_comp_localHomologyObjCompIso_hom_assoc,
    localHomologyRestriction_comp_localHomologyIsoOfCoefficientsIso_hom]

/-- `TauCeti.localHomologyExtendScalarsIso` commutes with `TauCeti.localHomologyMap`. -/
@[reassoc] lemma map_localHomologyMap_comp_localHomologyExtendScalarsIso_hom {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (j : C(M, N)) {A : Set M} {B : Set N}
    (h : j ⁻¹' B ⊆ A) (k : ℕ) :
    (ModuleCat.extendScalars.{w, w, w} f).map (localHomologyMap (ModuleCat.of R R) j h k) ≫
        (localHomologyExtendScalarsIso f B k).hom =
      (localHomologyExtendScalarsIso f A k).hom ≫ localHomologyMap (ModuleCat.of S S) j h k := by
  simp only [localHomologyExtendScalarsIso, Iso.trans_hom, Category.assoc,
    map_localHomologyMap_comp_localHomologyObjCompIso_hom_assoc,
    localHomologyMap_comp_localHomologyIsoOfCoefficientsIso_hom]

/-- `TauCeti.localHomologyExtendScalarsIso` commutes with `TauCeti.localHomologyTransport`. -/
@[reassoc] lemma map_localHomologyTransport_comp_localHomologyExtendScalarsIso_hom {M E : Type w}
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (k : ℕ) {x y : FundamentalGroupoid M} (g : x ⟶ y) :
    (ModuleCat.extendScalars.{w, w, w} f).map
        (localHomologyTransport (ModuleCat.of R R) M E k g) ≫
        (localHomologyExtendScalarsIso f {y.as} k).hom =
      (localHomologyExtendScalarsIso f {x.as} k).hom ≫
        localHomologyTransport (ModuleCat.of S S) M E k g := by
  simp only [localHomologyExtendScalarsIso, Iso.trans_hom, Category.assoc,
    map_localHomologyTransport_comp_localHomologyObjCompIso_hom_assoc,
    localHomologyTransport_comp_localHomologyIsoOfCoefficientsIso_hom]

end ExtendScalars

end TauCeti
