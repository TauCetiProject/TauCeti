/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.InjectiveResolution
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import TauCeti.AlgebraicGeometry.Modules.Pushforward.HomologicalComplex
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

The comparison with sheafification is natural in the coefficient module, and so is the
resulting map from the presheaf to `Rⁿ f_* M` (`higherDirectImagePresheafToSheaf`); maps out of
`Rⁿ f_* M` are determined by their restrictions along it
(`higherDirectImagePresheafToSheaf_hom_ext`). In degree
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

/-- The map from the presheaf of modules `V ↦ Hⁿ(f⁻¹ V, M)` to its sheafification `Rⁿ f_* M`,
natural in `M`. -/
def higherDirectImagePresheafToSheaf (n : ℕ) :
    f.higherDirectImagePresheaf n ⟶ f.higherDirectImage n ⋙
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)) :=
  whiskerLeft (f.higherDirectImagePresheaf n)
      (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit ≫
    whiskerRight (f.higherDirectImagePresheafSheafificationIso n).hom
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj))

/-- The map from `V ↦ Hⁿ(f⁻¹ V, M)` to `Rⁿ f_* M` is the sheafification unit followed by the
identification of the sheafification with `Rⁿ f_* M`. -/
lemma higherDirectImagePresheafToSheaf_app (n : ℕ) (M : X.Modules) :
    (f.higherDirectImagePresheafToSheaf n).app M =
      (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app _ ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
          ((f.higherDirectImagePresheafSheafificationIso n).hom.app M) :=
  (rfl)

/-- Maps out of `Rⁿ f_* M` are determined by their restrictions to the presheaf
`V ↦ Hⁿ(f⁻¹ V, M)` along `higherDirectImagePresheafToSheaf`. -/
lemma higherDirectImagePresheafToSheaf_hom_ext {n : ℕ} {M : X.Modules} {S : Y.Modules}
    {α β : (f.higherDirectImage n).obj M ⟶ S}
    (h : (f.higherDirectImagePresheafToSheaf n).app M ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map α =
      (f.higherDirectImagePresheafToSheaf n).app M ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
          β) :
    α = β := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  -- Transposing `e ≫ γ` along the sheafification adjunction gives the restriction of `γ`.
  -- Chain with `Eq.trans`: it identifies `Y.Modules` with `SheafOfModules Y.ringCatSheaf` in the
  -- objects, which `rw` does not.
  have key (γ : (f.higherDirectImage n).obj M ⟶ S) :
      adj.homEquiv _ _ ((f.higherDirectImagePresheafSheafificationIso n).hom.app M ≫ γ) =
        (f.higherDirectImagePresheafToSheaf n).app M ≫
          (SheafOfModules.forget _ ⋙
            PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map γ :=
    (adj.homEquiv_unit _ _ _).trans ((congrArg _ (Functor.map_comp _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (f.higherDirectImagePresheafToSheaf_app n M).symm)))
  exact (cancel_epi ((f.higherDirectImagePresheafSheafificationIso n).hom.app M)).mp
    ((adj.homEquiv _ _).injective ((key α).trans (h.trans (key β).symm)))

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
    W.mapIso (P.cohomologyPresheafIso n)

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
  have h₅ := congrArg W.map (InjectiveResolution.cohomologyPresheafIso_naturality P Q φ ψ
    (InjectiveResolution.desc_commutes_zero φ Q P) n)
  simp only [Functor.map_comp, Functor.comp_map] at h₁ h₂ h₃ h₄ h₅
  -- Compose the five naturality squares without unfolding their objectwise isomorphisms.
  exact ((CommSq.mk h₁).vert_comp ((CommSq.mk h₂).vert_comp
    ((CommSq.mk h₃).vert_comp ((CommSq.mk h₄).vert_comp (CommSq.mk h₅))))).w

/-- The comparison `higherDirectImagePresheafToPresheafIso` computed from the chosen injective
resolution `P` of `M`: the homology of `f_* P` as a presheaf of modules, read as a presheaf of
abelian groups, is the homology of the complex `Γ(f⁻¹ -, P)` of presheaves, which is the cohomology
presheaf of `M` on preimages. -/
lemma higherDirectImagePresheafToPresheafIso_def (M : X.Modules) (n : ℕ) :
    letI := Functor.additive_of_preserves_binary_products
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
    f.higherDirectImagePresheafToPresheafIso M n =
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).mapIso
          ((injectiveResolution M).isoRightDerivedObj
            (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y) n) ≪≫
        (Functor.mapHomologicalComplexCompHomologyFunctorIso
          (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj) _ n).symm.app _ ≪≫
        (HomologicalComplex.homologyFunctor _ _ n).mapIso
          ((pushforwardSectionsComplexIso f).app (injectiveResolution M).cocomplex) ≪≫
        (((whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
          (Opens.map f.base).op).mapHomologicalComplexCompHomologyFunctorIso _ n).app _ ≪≫
        ((whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opens.map f.base).op).mapIso
          ((injectiveResolution M).cohomologyPresheafIso n) :=
  (rfl)

/-- The identification of `V ↦ Hⁿ(f⁻¹ V, M)` with cohomology is natural in `M`, on elements. -/
lemma higherDirectImagePresheafToPresheafIso_hom_app_map {M N : X.Modules} (φ : M ⟶ N)
    (n : ℕ) (V : Y.Opens) (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    (f.higherDirectImagePresheafToPresheafIso N n).hom.app (.op V)
        (((f.higherDirectImagePresheaf n).map φ).app (.op V) x) =
      Scheme.Modules.cohomologyOnMap φ n (f ⁻¹ᵁ V)
        ((f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op V) x) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (f.higherDirectImagePresheafToPresheafIso_naturality φ n) (.op V)) x

/-- The inverse identification of cohomology with `V ↦ Hⁿ(f⁻¹ V, M)` is natural in `M`, on
elements. -/
lemma higherDirectImagePresheafToPresheafIso_inv_app_cohomologyOnMap {M N : X.Modules}
    (φ : M ⟶ N) (n : ℕ) (V : Y.Opens) (x : Scheme.Modules.cohomologyOn M n (f ⁻¹ᵁ V)) :
    (f.higherDirectImagePresheafToPresheafIso N n).inv.app (.op V)
        (Scheme.Modules.cohomologyOnMap φ n _ x) =
      ((f.higherDirectImagePresheaf n).map φ).app (.op V)
        ((f.higherDirectImagePresheafToPresheafIso M n).inv.app (.op V) x) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((f.higherDirectImagePresheafToPresheafIso N n).hom.app (.op V))).injective
  have h₁ := f.higherDirectImagePresheafToPresheafIso_hom_app_map φ n V
    ((f.higherDirectImagePresheafToPresheafIso M n).inv.app (.op V) x)
  simp only [Iso.inv_hom_id_app_apply] at h₁ ⊢
  exact h₁.symm

end AlgebraicGeometry.Scheme.Hom
