/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import TauCeti.AlgebraicGeometry.Cohomology.Flasque
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# The module presheaf of higher direct images

For a scheme morphism `f : X ⟶ Y`, deriving pushforward with values in presheaves of
`𝒪_Y`-modules gives a presheaf whose underlying abelian presheaf is
`U ↦ Hⁿ(f⁻¹ U, M)`. Its sheafification is `Rⁿ f_* M`, as a sheaf of modules.
Thus both the scalar actions and the restriction maps can be retained when computing
higher direct images from cohomology on inverse images of opens. In particular, this
provides the module-valued comparison needed to apply localization criteria for
quasi-coherence.

The comparison with sheafification is natural in the coefficient module. In degree
zero the presheaf is the underlying presheaf of the ordinary direct image. The
comparison with cohomology is natural in coefficient modules
(`higherDirectImagePresheafToPresheafIso_naturality`) and uses the flasque abelian
resolution underlying an injective resolution of modules.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 8.1.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Functor

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The presheaf of `𝒪_Y`-modules `U ↦ Hⁿ(f⁻¹ U, M)`, constructed by deriving
pushforward with values in presheaves of modules. Its restriction maps are semilinear
along restriction of functions on `Y`. -/
abbrev higherDirectImagePresheaf (n : ℕ) :
    X.Modules ⥤ Y.PresheafOfModules :=
  letI := Functor.additive_of_preserves_binary_products
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
  (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y).rightDerived n

/-- In degree zero the module cohomology presheaf is the underlying presheaf of
the ordinary pushforward. -/
def higherDirectImagePresheafZeroIso :
    f.higherDirectImagePresheaf 0 ≅
      Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y :=
  letI := Functor.additive_of_preserves_binary_products
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
  (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y).rightDerivedZeroIsoSelf

/-- Sheafifying the module cohomology presheaf recovers the higher direct image,
naturally in the coefficient module, including its `𝒪_Y`-module structure. -/
def higherDirectImagePresheafSheafificationIso (n : ℕ) :
    let a : Y.PresheafOfModules ⥤ Y.Modules :=
      PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)
    f.higherDirectImagePresheaf n ⋙ a ≅ f.higherDirectImage n := by
  letI := Functor.additive_of_preserves_binary_products
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
  let a : Y.PresheafOfModules ⥤ Y.Modules :=
    PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)
  letI : a.Additive :=
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).additive_of_preserves_binary_products
  letI : a.PreservesHomology := inferInstanceAs
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).PreservesHomology)
  let ε := asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).counit
  exact Functor.rightDerivedCompIso
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y) a
    (𝟭 X.Modules) (Scheme.Modules.pushforward f)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ε ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm) n ≪≫
    Functor.leftUnitor _

private def pushforwardSectionsComplexIso :
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y).mapHomologicalComplex
        (ComplexShape.up ℕ) ⋙
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).mapHomologicalComplex _ ≅
    (toSheaf X).mapHomologicalComplex _ ⋙
      (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _ ⋙
        ((whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
          (Opens.map f.base).op).mapHomologicalComplex _ := by
  let t := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let W := (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map f.base).op
  exact Functor.mapHomologicalComplexCompIso
      (F := Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y) (G := t)
      (H := toSheaf X ⋙ sheafToPresheaf _ _ ⋙ W)
      (pushforwardCompToPresheafIso f ≪≫
        Functor.isoWhiskerRight
          (SheafOfModules.toSheafCompSheafToPresheafIso X.ringCatSheaf).symm W ≪≫
        Functor.associator _ _ _) _ ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (toSheaf X ⋙ sheafToPresheaf _ _ ⋙ W))
      _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapHomologicalComplexCompIso (Iso.refl (sheafToPresheaf _ _ ⋙ W)) _).symm

private def resolutionCohomologyIso {M : X.Modules} (P : InjectiveResolution M) (n : ℕ) :
    (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)).homology n ≅
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n := by
  haveI : Mono ((toSheaf X).map (P.ι.f 0)) := Functor.map_mono _ _
  exact Sheaf.H'.homologyIsoCohomologyPresheaf
    (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
    ((toSheaf X).map (P.ι.f 0)) (P.map_ι_f_zero_comp_d (toSheaf X))
    (P.exact₀_map (toSheaf X)) (P.exactAt_succ_map (toSheaf X))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (P.cocomplex.X j) k V) n

private lemma resolutionCohomologyIso_naturality {M N : X.Modules}
    (P : InjectiveResolution M) (Q : InjectiveResolution N) (φ : M ⟶ N)
    (ψ : P.cocomplex ⟶ Q.cocomplex) (hψ : P.ι.f 0 ≫ ψ.f 0 = φ ≫ Q.ι.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap
      (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (((toSheaf X).mapHomologicalComplex _).map ψ)) n ≫
      (resolutionCohomologyIso Q n).hom =
    (resolutionCohomologyIso P n).hom ≫
      (Sheaf.cohomologyPresheafFunctor _ n).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := by
  have : Mono ((toSheaf X).map (P.ι.f 0)) := Functor.map_mono _ _
  have : Mono ((toSheaf X).map (Q.ι.f 0)) := Functor.map_mono _ _
  dsimp only [resolutionCohomologyIso]
  exact Sheaf.H'.homologyMap_comp_homologyIsoCohomologyPresheaf_hom
    (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
    (K' := ((toSheaf X).mapHomologicalComplex _).obj Q.cocomplex)
    ((toSheaf X).map (P.ι.f 0)) (P.map_ι_f_zero_comp_d (toSheaf X))
    (P.exact₀_map (toSheaf X)) (P.exactAt_succ_map (toSheaf X))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (P.cocomplex.X j) k V) n
    ((toSheaf X).map (Q.ι.f 0)) (Q.map_ι_f_zero_comp_d (toSheaf X))
    (Q.exact₀_map (toSheaf X)) (Q.exactAt_succ_map (toSheaf X))
    (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      (Q.cocomplex.X j) k V)
    (φ := (toSheaf X).map φ) (ψ := ((toSheaf X).mapHomologicalComplex _).map ψ)
    (by
      exact (toSheaf X).map_comp _ _ |>.symm.trans
        ((congrArg (toSheaf X).map hψ).trans ((toSheaf X).map_comp _ _)))

/-- Forgetting the module structure of the module cohomology presheaf gives the
usual cohomology presheaf `U ↦ Hⁿ(f⁻¹ U, M)`. This comparison respects restriction
in `U`. -/
def higherDirectImagePresheafToPresheafIso (M : X.Modules) (n : ℕ) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj
        ((f.higherDirectImagePresheaf n).obj M) ≅
      (Opens.map f.base).op ⋙
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n := by
  letI := Functor.additive_of_preserves_binary_products
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
  let P := injectiveResolution M
  let t := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let W := (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map f.base).op
  exact t.mapIso (P.isoRightDerivedObj
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y) n) ≪≫
    (t.mapHomologicalComplexCompHomologyFunctorIso _ n).symm.app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((pushforwardSectionsComplexIso f).app P.cocomplex) ≪≫
    (W.mapHomologicalComplexCompHomologyFunctorIso _ n).app _ ≪≫
    W.mapIso (resolutionCohomologyIso P n)

/-- The comparison of the higher direct image presheaf with cohomology on inverse
images of opens is natural in the coefficient sheaf. -/
@[reassoc]
lemma higherDirectImagePresheafToPresheafIso_naturality {M N : X.Modules} (φ : M ⟶ N)
    (n : ℕ) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((f.higherDirectImagePresheaf n).map φ) ≫
      (f.higherDirectImagePresheafToPresheafIso N n).hom =
    (f.higherDirectImagePresheafToPresheafIso M n).hom ≫
      whiskerLeft (Opens.map f.base).op
        ((Sheaf.cohomologyPresheafFunctor _ n).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)) := by
  let := Functor.additive_of_preserves_binary_products
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
  let P := injectiveResolution M
  let Q := injectiveResolution N
  let ψ := InjectiveResolution.desc φ Q P
  let F := Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y
  let t := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let W := (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map f.base).op
  have h₁ := congrArg t.map (InjectiveResolution.isoRightDerivedObj_hom_naturality
    φ P Q ψ (InjectiveResolution.desc_commutes_zero φ Q P) F n)
  have h₂ := (t.mapHomologicalComplexCompHomologyFunctorIso _ n).inv.naturality
    ((F.mapHomologicalComplex _).map ψ)
  have h₃ := congrArg (HomologicalComplex.homologyFunctor _ _ n).map
    ((pushforwardSectionsComplexIso f).hom.naturality ψ)
  have h₄ := (W.mapHomologicalComplexCompHomologyFunctorIso _ n).hom.naturality
    (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
      (((toSheaf X).mapHomologicalComplex _).map ψ))
  have h₅ := congrArg W.map (resolutionCohomologyIso_naturality P Q φ ψ
    (InjectiveResolution.desc_commutes_zero φ Q P) n)
  simp only [Functor.map_comp, Functor.comp_map] at h₁ h₂ h₃ h₄ h₅
  -- Compose the five naturality squares without unfolding their objectwise isomorphisms.
  exact ((CommSq.mk h₁).vert_comp ((CommSq.mk h₂).vert_comp
    ((CommSq.mk h₃).vert_comp ((CommSq.mk h₄).vert_comp (CommSq.mk h₅))))).w

end AlgebraicGeometry.Scheme.Hom
