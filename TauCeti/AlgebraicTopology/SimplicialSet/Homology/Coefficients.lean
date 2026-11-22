/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Rat

/-!
# Exactness of simplicial chains in the coefficients

Simplicial chains send a short exact sequence of coefficients to a short exact sequence of chain
complexes whenever coproducts in the coefficient category are exact. The construction is Mathlib's
`SSet.chainComplexFunctor`, whose degree-n object is a coproduct of coefficient objects over
the n-simplices. Applying the homology long
exact sequence gives the coefficient connecting homomorphisms, including Bockstein maps.

Extension of scalars along a ring map `f : R →+* S` with exact extension of scalars, such as a
flat one, commutes with homology: `SSet.homologyExtendScalarsIso` identifies the extension of
scalars of the homology with coefficients in `R` with the homology with coefficients in `S`,
naturally in the simplicial set (`SSet.homologyExtendScalarsIso_hom_naturality`). The instance
`ModuleCat.preservesFiniteLimits_extendScalars_intCastRat`, the `ℤ → ℚ` case of
`ModuleCat.preservesFiniteLimits_extendScalars_algebraMap`, supplies the exactness for the flat
map `ℤ → ℚ`, which compares integral and rational homology.

For preadditive `[CategoryWithHomology]` categories with `w`-coproducts, this file also supplies
coefficient-change functoriality (`SSet.homologyNatTransOfCoefficients`,
`SSet.homologyNatIsoOfCoefficientsIso`, `SSet.homologyIsoOfCoefficientsIso`), exact-functor
comparisons (`SSet.homologyFunctorObjCompIso`, `SSet.homologyObjIso`), and
`RingHom.simplicialHomologyFunctorExtendScalarsIso` (built via `Functor.Monoidal.εIso`), feeding
relative simplicial, singular, and local homology coefficient change.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.A, change of coefficients.
-/

public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe w v v' u u'

namespace CategoryTheory.ShortComplex.ShortExact

/-- Simplicial chains preserve short exact coefficient sequences when coproducts are exact. -/
lemma map_simplicialChains {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [AB4OfSize.{w} C] {S : ShortComplex C}
    (hS : S.ShortExact) (X : SSet.{w}) :
    (S.map ((SSet.chainComplexFunctor C).flip.obj X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let F : C ⥤ C := Functor.const (Discrete (X _⦋n⦌)) ⋙ colim
  -- In degree n the chain functor is the coproduct of the constant coefficient diagram.
  convert hS.map_of_exact F using 1
  rfl

end CategoryTheory.ShortComplex.ShortExact

namespace ModuleCat

/-- Rational extension of scalars is exact, since `ℚ` is a localization of `ℤ`. This is the
`ℤ → ℚ` case of `ModuleCat.preservesFiniteLimits_extendScalars_algebraMap`, stated for
`Int.castRingHom ℚ`, which instance search does not match against `algebraMap ℤ ℚ`. -/
instance preservesFiniteLimits_extendScalars_intCastRat :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars (Int.castRingHom ℚ) : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ) :=
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  preservesFiniteLimits_extendScalars_algebraMap (R := ℤ) (S := ℚ)

end ModuleCat

namespace SSet
section Coefficients
open CategoryTheory.Functor (whiskerRight isoWhiskerLeft isoWhiskerRight)
open HomologicalComplex (homologyMap)
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C] {R R' R'' : C}
/-- A coefficient morphism `φ : R ⟶ R'` induces a natural transformation on simplicial homology. -/
def homologyNatTransOfCoefficients (φ : R ⟶ R') (n : ℕ) :
    homologyFunctor.{w} R n ⟶ homologyFunctor.{w} R' n :=
  whiskerRight ((chainComplexFunctor C).map φ) (HomologicalComplex.homologyFunctor C _ n)
@[simp] lemma homologyNatTransOfCoefficients_app (φ : R ⟶ R') (n : ℕ) (X : SSet.{w}) :
    (homologyNatTransOfCoefficients φ n).app X =
      homologyMap (((chainComplexFunctor C).map φ).app X) n := (rfl)
@[simp] lemma homologyNatTransOfCoefficients_id (R : C) (n : ℕ) :
    homologyNatTransOfCoefficients.{w} (𝟙 R) n = 𝟙 _ :=
  (congrArg (whiskerRight · _) ((chainComplexFunctor C).map_id R)).trans (Functor.whiskerRight_id _)
@[simp] lemma homologyNatTransOfCoefficients_comp (φ : R ⟶ R') (ψ : R' ⟶ R'') (n : ℕ) :
    homologyNatTransOfCoefficients.{w} (φ ≫ ψ) n =
      homologyNatTransOfCoefficients φ n ≫ homologyNatTransOfCoefficients ψ n :=
  (congrArg (whiskerRight · _) ((chainComplexFunctor C).map_comp φ ψ)).trans
    (Functor.whiskerRight_comp _ _ _)
variable (e : R ≅ R')
/-- A coefficient iso `e : R ≅ R'` induces a natural isomorphism on simplicial homology. -/
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
section
variable (X : SSet.{w}) (n : ℕ)
/-- An iso `e : R ≅ R'` of coefficient objects induces an isomorphism on `Hₙ(X; R)`. -/
def homologyIsoOfCoefficientsIso : X.homology R n ≅ X.homology R' n :=
  (homologyNatIsoOfCoefficientsIso e n).app X
@[simp] lemma homologyIsoOfCoefficientsIso_hom : (homologyIsoOfCoefficientsIso e X n).hom =
    (homologyNatTransOfCoefficients e.hom n).app X := (rfl)
@[simp] lemma homologyIsoOfCoefficientsIso_inv : (homologyIsoOfCoefficientsIso e X n).inv =
    (homologyNatTransOfCoefficients e.inv n).app X := (rfl)
@[simp] lemma homologyIsoOfCoefficientsIso_symm :
    homologyIsoOfCoefficientsIso e.symm X n = (homologyIsoOfCoefficientsIso e X n).symm :=
  Iso.ext rfl
end
@[simp] lemma homologyIsoOfCoefficientsIso_refl (R : C) (X : SSet.{w}) (n : ℕ) :
    homologyIsoOfCoefficientsIso (Iso.refl R) X n = Iso.refl _ :=
  Iso.ext (congrArg (·.app X) (homologyNatTransOfCoefficients_id R n))
@[simp] lemma homologyIsoOfCoefficientsIso_trans (e₁ : R ≅ R') (e₂ : R' ≅ R'') (X : SSet.{w})
    (n : ℕ) : homologyIsoOfCoefficientsIso (e₁ ≪≫ e₂) X n =
      homologyIsoOfCoefficientsIso e₁ X n ≪≫ homologyIsoOfCoefficientsIso e₂ X n :=
  Iso.ext (congrArg (·.app X) (homologyNatTransOfCoefficients_comp e₁.hom e₂.hom n))
@[reassoc] lemma homologyMap_comp_homologyIsoOfCoefficientsIso_hom {X Y : SSet.{w}} (g : X ⟶ Y)
    (n : ℕ) : SSet.homologyMap g R n ≫ (homologyIsoOfCoefficientsIso e Y n).hom =
      (homologyIsoOfCoefficientsIso e X n).hom ≫ SSet.homologyMap g R' n :=
  (homologyNatIsoOfCoefficientsIso e n).hom.naturality g
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]
  [CategoryWithHomology D] (F : C ⥤ D) [F.Additive]
  [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] [F.PreservesHomology] (R : C)
/-- **Simplicial homology commutes with exact coproduct-preserving `F`**: `F Hₙ ≅ Hₙ F`. -/
def homologyFunctorObjCompIso (n : ℕ) :
    homologyFunctor.{w} R n ⋙ F ≅ homologyFunctor.{w} (F.obj R) n :=
  isoWhiskerLeft ((chainComplexFunctor C).obj R)
    (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).symm ≪≫
  isoWhiskerRight (chainComplexFunctorObjCompMapIso F R) (HomologicalComplex.homologyFunctor _ _ n)
lemma homologyFunctorObjCompIso_hom_app (n : ℕ) (X : SSet.{w}) :
    (homologyFunctorObjCompIso F R n).hom.app X =
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app (X.chainComplex R) ≫
        homologyMap ((chainComplexFunctorObjCompMapIso F R).hom.app X) n := (rfl)
lemma homologyFunctorObjCompIso_inv_app (n : ℕ) (X : SSet.{w}) :
    (homologyFunctorObjCompIso F R n).inv.app X =
      homologyMap ((chainComplexFunctorObjCompMapIso F R).inv.app X) n ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso _ n).hom.app (X.chainComplex R) := (rfl)
/-- **Simplicial homology of `X` commutes with exact coproduct-preserving `F`**: `F Hₙ ≅ Hₙ F`. -/
def homologyObjIso (X : SSet.{w}) (n : ℕ) : F.obj (X.homology R n) ≅ X.homology (F.obj R) n :=
  (homologyFunctorObjCompIso F R n).app X
lemma homologyObjIso_hom (X : SSet.{w}) (n : ℕ) :
    (homologyObjIso F R X n).hom = (homologyFunctorObjCompIso F R n).hom.app X := (rfl)
lemma homologyObjIso_inv (X : SSet.{w}) (n : ℕ) :
    (homologyObjIso F R X n).inv = (homologyFunctorObjCompIso F R n).inv.app X := (rfl)
@[reassoc] lemma map_homologyMap_comp_homologyObjIso_hom {X Y : SSet.{w}} (g : X ⟶ Y) (n : ℕ) :
    F.map (SSet.homologyMap g R n) ≫ (homologyObjIso F R Y n).hom =
      (homologyObjIso F R X n).hom ≫ SSet.homologyMap g (F.obj R) n :=
  (homologyFunctorObjCompIso F R n).hom.naturality g
end Coefficients
end SSet

namespace RingHom
open ModuleCat (extendScalars of)
open CategoryTheory.Functor.Monoidal (εIso)
open SSet (homologyFunctor homologyFunctorObjCompIso homologyNatIsoOfCoefficientsIso
  homologyObjIso homologyIsoOfCoefficientsIso)
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (extendScalars.{u} f)]
/-- **Extension of scalars commutes with simplicial homology**, naturally in `X : SSet`. -/
def simplicialHomologyFunctorExtendScalarsIso (n : ℕ) :
    homologyFunctor.{u} (of R R) n ⋙ extendScalars.{u} f ≅ homologyFunctor.{u} (of S S) n :=
  homologyFunctorObjCompIso (extendScalars.{u} f) (of R R) n ≪≫
    homologyNatIsoOfCoefficientsIso (εIso (extendScalars.{u} f)).symm n
lemma simplicialHomologyFunctorExtendScalarsIso_hom_app (X : SSet.{u}) (n : ℕ) :
    (f.simplicialHomologyFunctorExtendScalarsIso n).hom.app X =
      (homologyObjIso (extendScalars.{u} f) (of R R) X n).hom ≫
        (homologyIsoOfCoefficientsIso (εIso _).symm X n).hom := (rfl)
lemma simplicialHomologyFunctorExtendScalarsIso_inv_app (X : SSet.{u}) (n : ℕ) :
    (f.simplicialHomologyFunctorExtendScalarsIso n).inv.app X =
      (homologyIsoOfCoefficientsIso (εIso _).symm X n).inv ≫
        (homologyObjIso (extendScalars.{u} f) (of R R) X n).inv := (rfl)
end RingHom

namespace SSet

private def homologyFunctorExtendScalarsIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [PreservesFiniteLimits (ModuleCat.extendScalars.{u} f)] (n : ℕ) :
    homologyFunctor.{u} (ModuleCat.of R (ULift.{u} R)) n ⋙ ModuleCat.extendScalars.{u} f ≅
      homologyFunctor.{u} (ModuleCat.of S S) n :=
  Functor.isoWhiskerRight
      (homologyNatIsoOfCoefficientsIso.{u} (ULift.moduleEquiv.{u, u} (R := R)).toModuleIso n)
      (ModuleCat.extendScalars.{u} f) ≪≫
    f.simplicialHomologyFunctorExtendScalarsIso n

/-- **Extension of scalars commutes with simplicial homology** along a ring map `f : R →+* S` whose
extension of scalars is exact, for instance a flat one
(`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`): extending scalars of the homology with
coefficients in `R` gives the homology with coefficients in `S`. The `R`-coefficient object is the
native `ULift R`; the `S`-coefficient object is `S`. -/
def homologyExtendScalarsIso {R S : Type u} [CommRing R] [CommRing S] (X : SSet.{u})
    (f : R →+* S) [PreservesFiniteLimits (ModuleCat.extendScalars.{u} f)] (n : ℕ) :
    (ModuleCat.extendScalars f).obj (X.homology (ModuleCat.of R (ULift.{u} R)) n) ≅
      X.homology (ModuleCat.of S S) n :=
  (homologyFunctorExtendScalarsIso f n).app X

/-- The identification `SSet.homologyExtendScalarsIso` is the composite of three comparisons:
extension of scalars commutes with the homology of the chain complex, with the simplicial chain
complex, and carries the coefficients `ULift R` to `S`. -/
theorem homologyExtendScalarsIso_hom {R S : Type u} [CommRing R] [CommRing S] (X : SSet.{u})
    (f : R →+* S) [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f)] (n : ℕ) :
    (X.homologyExtendScalarsIso f n).hom =
      (((X.chainComplex (ModuleCat.of R (ULift.{u} R))).sc n).mapHomologyIso
          (ModuleCat.extendScalars f)).inv ≫
        HomologicalComplex.homologyMap ((SSet.chainComplexFunctorObjCompMapIso
          (ModuleCat.extendScalars f) (ModuleCat.of R (ULift.{u} R))).hom.app X) n ≫
        HomologicalComplex.homologyMap
          (((SSet.chainComplexFunctor (ModuleCat.{u} S)).flip.obj X).map
            ((ModuleCat.extendScalars f).map ULift.moduleEquiv.toModuleIso.hom ≫
              (letI := f.toAlgebra; (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso.hom)))
          n := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars f
  let M := ModuleCat.of R (ULift.{u} R)
  let φ : M ⟶ ModuleCat.of R R := ULift.moduleEquiv.{u, u}.toModuleIso.hom
  let := f.toAlgebra
  have hε : (CategoryTheory.Functor.Monoidal.εIso F).symm.hom =
      (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso.hom :=
    ModuleCat.extendScalars_η f
  have hinv : (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app
      (X.chainComplex M) = (((X.chainComplex M).sc n).mapHomologyIso F).inv := by
    rw [← cancel_mono (((X.chainComplex M).sc n).mapHomologyIso F).hom, Iso.inv_hom_id,
      ← Functor.mapHomologicalComplexCompHomologyFunctorIso_hom_app]
    exact ((F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).app
      (X.chainComplex M)).inv_hom_id
  have hcc : (F.mapHomologicalComplex (.down ℕ)).map (((SSet.chainComplexFunctor _).map φ).app X) ≫
      (SSet.chainComplexFunctorObjCompMapIso F (ModuleCat.of R R)).hom.app X =
      (SSet.chainComplexFunctorObjCompMapIso F M).hom.app X ≫
        ((SSet.chainComplexFunctor _).map (F.map φ)).app X := by
    refine HomologicalComplex.hom_ext _ _ fun k ↦
      (Limits.isColimitOfPreserves F (X.isColimitChainComplexXCofan M k)).hom_ext fun ⟨x⟩ ↦ ?_
    have h₁ : X.ιChainComplex x ≫ (((SSet.chainComplexFunctor _).map φ).app X).f k =
        φ ≫ X.ιChainComplex x := by
      simp [SSet.chainComplexFunctor, SSet.ιChainComplex]
    have h₂ : X.ιChainComplex x ≫ (((SSet.chainComplexFunctor _).map (F.map φ)).app X).f k =
        F.map φ ≫ X.ιChainComplex x := by
      simp [SSet.chainComplexFunctor, SSet.ιChainComplex]
    change F.map (X.ιChainComplex x) ≫
        F.map ((((SSet.chainComplexFunctor _).map φ).app X).f k) ≫
        ((SSet.chainComplexFunctorObjCompMapIso F (ModuleCat.of R R)).hom.app X).f k =
      F.map (X.ιChainComplex x) ≫
        ((SSet.chainComplexFunctorObjCompMapIso F M).hom.app X).f k ≫
        (((SSet.chainComplexFunctor _).map (F.map φ)).app X).f k
    rw [← F.map_comp_assoc, h₁, F.map_comp_assoc,
      SSet.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f,
      SSet.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f_assoc, h₂]
  have hnat :
      F.map (HomologicalComplex.homologyMap (((SSet.chainComplexFunctor _).map φ).app X) n) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app
          (X.chainComplex (ModuleCat.of R R)) =
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app (X.chainComplex M) ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.down ℕ)).map
            (((SSet.chainComplexFunctor _).map φ).app X)) n :=
    (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.naturality
      (((SSet.chainComplexFunctor _).map φ).app X)
  have hh := congrArg (HomologicalComplex.homologyMap · n) hcc
  simp only [HomologicalComplex.homologyMap_comp] at hh
  have hhh : F.map ((homologyNatTransOfCoefficients φ n).app X) ≫
      (homologyObjIso F (ModuleCat.of R R) X n).hom =
      (homologyObjIso F M X n).hom ≫ (homologyNatTransOfCoefficients (F.map φ) n).app X :=
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hnat)).trans
      ((Category.assoc _ _ _).trans (congrArg ((F.mapHomologicalComplexCompHomologyFunctorIso
        (.down ℕ) n).inv.app (X.chainComplex M) ≫ ·) hh))
  have hlast :
      (homologyNatTransOfCoefficients (F.map φ) n).app X ≫
        (homologyNatTransOfCoefficients (CategoryTheory.Functor.Monoidal.εIso F).symm.hom n).app X =
      HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat.{u} S)).flip.obj X).map
          (F.map φ ≫ (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso.hom)) n := by
    rw [← NatTrans.comp_app, ← homologyNatTransOfCoefficients_comp, hε]
    rfl
  simp only [homologyExtendScalarsIso, homologyFunctorExtendScalarsIso, Iso.app_hom,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    RingHom.simplicialHomologyFunctorExtendScalarsIso_hom_app, homologyIsoOfCoefficientsIso_hom,
    homologyNatIsoOfCoefficientsIso_hom]
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hhh)).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg ((homologyObjIso F M X n).hom ≫ ·) hlast).trans ?_)
  rw [homologyObjIso_hom, homologyFunctorObjCompIso_hom_app, hinv]
  exact Category.assoc _ _ _

/-- The identification of the extension of scalars of the homology with coefficients in `R` with
the homology with coefficients in `S` is natural in the simplicial set. -/
@[reassoc]
theorem homologyExtendScalarsIso_hom_naturality {R S : Type u} [CommRing R] [CommRing S]
    {X Y : SSet.{u}} (g : X ⟶ Y) (f : R →+* S)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f)] (n : ℕ) :
    (ModuleCat.extendScalars f).map (SSet.homologyMap g (ModuleCat.of R (ULift.{u} R)) n) ≫
        (Y.homologyExtendScalarsIso f n).hom =
      (X.homologyExtendScalarsIso f n).hom ≫ SSet.homologyMap g (ModuleCat.of S S) n :=
  (homologyFunctorExtendScalarsIso f n).hom.naturality g

end SSet
