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
comparison with cohomology uses the flasque abelian resolution underlying an injective
resolution of modules.

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

/-- Forgetting the module structure of the module cohomology presheaf gives the
usual cohomology presheaf `U ↦ Hⁿ(f⁻¹ U, M)`. This comparison respects restriction
in `U`. -/
def higherDirectImagePresheafToPresheafIso (M : X.Modules) (n : ℕ) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj
        ((f.higherDirectImagePresheaf n).obj M) ≅
      (Opens.map f.base).op ⋙ ((toSheaf X).obj M).cohomologyPresheaf n := by
  letI := Functor.additive_of_preserves_binary_products
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
  let P := injectiveResolution M
  let t := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let W := (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map f.base).op
  haveI : Mono ((toSheaf X).map (P.ι.f 0)) := Functor.map_mono _ _
  exact t.mapIso (P.isoRightDerivedObj
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y) n) ≪≫
    (t.mapHomologicalComplexCompHomologyFunctorIso _ n).symm.app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      -- Forgetting scalars commutes with pushforward; the remaining steps only regroup
      -- the composite functors.
      ((Functor.mapHomologicalComplexCompIso
          (F := Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y) (G := t)
          (H := toSheaf X ⋙ sheafToPresheaf _ _ ⋙ W)
          (pushforwardCompToPresheafIso f ≪≫
            Functor.isoWhiskerRight
              (SheafOfModules.toSheafCompSheafToPresheafIso X.ringCatSheaf).symm W ≪≫
            Functor.associator _ _ _) _).app P.cocomplex ≪≫
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (toSheaf X ⋙ sheafToPresheaf _ _ ⋙ W)) _).app P.cocomplex).symm ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app
          (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)).symm) ≪≫
    (W.mapHomologicalComplexCompHomologyFunctorIso _ n).app _ ≪≫
    W.mapIso (Sheaf.H'.homologyIsoCohomologyPresheaf
      (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
      ((toSheaf X).map (P.ι.f 0)) (P.map_ι_f_zero_comp_d (toSheaf X))
      (P.exact₀_map (toSheaf X)) (P.exactAt_succ_map (toSheaf X))
      (fun V j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
        (P.cocomplex.X j) k V) n)

end AlgebraicGeometry.Scheme.Hom
