/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Restrict
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Sheafify
import TauCeti.AlgebraicGeometry.Cohomology.Localization
import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
import TauCeti.CategoryTheory.Sites.DenseSubsite

/-!
# Sections of higher direct images over affine opens

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes and `M` a quasi-coherent
sheaf on `X`. Over an affine open `V` of `Y`, the sections of the higher direct image `R^p f_* M`
are the cohomology `H^p(f⁻¹ V, M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsIso`). For an affine target `Y`, the
canonical comparison map `H^p(f⁻¹ U, M) ⟶ Γ(U, R^p f_* M)`
(`AlgebraicGeometry.Scheme.Hom.toHigherDirectImageSections`), from the presheaf
`U ↦ H^p(f⁻¹ U, M)` to its sheafification, is bijective on `U = Y` and on every basic open
`U = D(g)` (`AlgebraicGeometry.Scheme.Hom.bijective_toHigherDirectImageSections_basicOpen`).

The proof follows Hartshorne, Proposition III.8.5. For `Y` affine, the restriction maps
`H^p(f⁻¹ Y, M) ⟶ H^p(f⁻¹ D(g), M)` are localizations at the powers of `g`
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_inf_basicOpen`), so on
the basic opens the presheaf `U ↦ H^p(f⁻¹ U, M)` is isomorphic to the sheaf associated to the
`Γ(Y, ⊤)`-module `H^p(X, M)`. A presheaf that agrees with a sheaf on a basis has the sections of
that sheaf over the basic opens
(`CategoryTheory.Functor.IsCoverDense.bijective_toSheafify_app`). For an arbitrary target, the
formation of `R^p f_* M` commutes with restriction to the affine open `V`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.toHigherDirectImageSections`: the comparison map
  `H^p(f⁻¹ U, M) ⟶ Γ(U, R^p f_* M)`;
* `AlgebraicGeometry.Scheme.Hom.bijective_toHigherDirectImageSections_basicOpen`,
  `AlgebraicGeometry.Scheme.Hom.bijective_toHigherDirectImageSections_top`: it is bijective over
  the basic opens of an affine target and over the target itself;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsIso`: `Γ(V, R^p f_* M) ≅ H^p(f⁻¹ V, M)`
  for every affine open `V` of the target.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5.
* The Stacks Project, Lemma 30.4.5 (Tag 01XJ).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (p : ℕ)

/-- The comparison map `H^p(f⁻¹ U, M) ⟶ Γ(U, R^p f_* M)`: the map from the presheaf
`V ↦ H^p(f⁻¹ V, M)` to its sheafification, which is `R^p f_* M`
(`AlgebraicGeometry.Scheme.Hom.toSheafHigherDirectImageObjIsoSheafify`). -/
def toHigherDirectImageSections (U : Y.Opens) :
    cohomologyOn M p (f ⁻¹ᵁ U) ⟶
      ((toSheaf Y).obj ((f.higherDirectImage p).obj M)).obj.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology Y)
      ((Opens.map f.base).op ⋙ ((toSheaf X).obj M).cohomologyPresheaf p)).app (op U) ≫
    (f.toSheafHigherDirectImageObjIsoSheafify M p).inv.hom.app (op U)

/-- `H^p(W, M)` as a module over `Γ(Y, ⊤)`, through `f^* : Γ(Y, ⊤) ⟶ Γ(X, ⊤)`. -/
private def moduleOn (W : X.Opens) : ModuleCat.{u} Γ(Y, ⊤) :=
  letI := Module.compHom (cohomologyOn M p W) f.appTop.hom
  ModuleCat.of _ (cohomologyOn M p W)

/-- Restriction `H^p(W, M) ⟶ H^p(W', M)` as a `Γ(Y, ⊤)`-linear map. -/
private def resLinear {W W' : X.Opens} (h : W' ≤ W) :
    moduleOn f M p W →ₗ[Γ(Y, ⊤)] moduleOn f M p W' :=
  letI := f.appTop.hom.toAlgebra
  letI : ∀ W : X.Opens, Module Γ(Y, ⊤) (cohomologyOn M p W) :=
    fun _ ↦ Module.compHom _ f.appTop.hom
  haveI : ∀ W : X.Opens, IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) (cohomologyOn M p W) :=
    fun _ ↦ IsScalarTower.of_compHom _ _ _
  (cohomologyOnResLinear M p h).restrictScalars Γ(Y, ⊤)

private lemma resLinear_apply {W W' : X.Opens} (h : W' ≤ W) (x : moduleOn f M p W) :
    resLinear f M p h x = cohomologyOnRes M p h x :=
  cohomologyOnResLinear_apply M p h x

section Affine

variable [IsAffine Y]

/-- The basic opens `D(g)` of `Y`, indexed by the global functions `g`. -/
private abbrev basicOpenFamily (Y : Scheme.{u}) : Γ(Y, ⊤) → Y.Opens := Y.basicOpen

/-- The quasi-coherent sheaf on `Spec Γ(Y, ⊤)` associated to the `Γ(Y, ⊤)`-module `H^p(X, M)`. -/
private def tildeTop : (Spec Γ(Y, ⊤)).Modules := tilde (moduleOn f M p (f ⁻¹ᵁ ⊤))

/-- The underlying abelian sheaf of `H^p(X, M)~`, transported to `Y` along `Spec Γ(Y, ⊤) ≅ Y`. -/
private def tildeSheaf : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  (toSheaf Y).obj
    ((Scheme.Modules.pushforward (isAffineOpen_top Y).fromSpec).obj (tildeTop f M p))

/-- Restriction `H^p(f⁻¹ Y, M) ⟶ H^p(f⁻¹ D(g), M)` is the localization at the powers of
`f^* g`. -/
private lemma isLocalizedModule_cohomologyOnResLinear_preimage_basicOpen [QuasiCompact f]
    [QuasiSeparated f] [M.IsQuasicoherent] (g : Γ(Y, ⊤)) :
    IsLocalizedModule (.powers (f.appTop g)) (cohomologyOnResLinear M p
      (f.preimage_mono le_top : f ⁻¹ᵁ Y.basicOpen g ≤ f ⁻¹ᵁ ⊤)) := by
  have key := isLocalizedModule_cohomologyOnResLinear_inf_basicOpen M (f.appTop g)
    (f.isCompact_preimage (isAffineOpen_top Y).isCompact)
    (f.isQuasiSeparated_preimage (isAffineOpen_top Y).isQuasiSeparated) p
  have hW : f ⁻¹ᵁ Y.basicOpen g = f ⁻¹ᵁ ⊤ ⊓ X.basicOpen (f.appTop g) := by
    rw [Scheme.preimage_basicOpen_top]
    exact (top_inf_eq _).symm
  -- Transport along the equality of opens `f⁻¹ D(g) = f⁻¹ Y ⊓ D(f^* g)`.
  have H : ∀ (W : X.Opens) (_ : W = f ⁻¹ᵁ ⊤ ⊓ X.basicOpen (f.appTop g)) (h : W ≤ f ⁻¹ᵁ ⊤),
      IsLocalizedModule (.powers (f.appTop g)) (cohomologyOnResLinear M p h) := by
    rintro _ rfl _
    exact key
  exact H _ hW _

/-- Restriction `H^p(f⁻¹ Y, M) ⟶ H^p(f⁻¹ D(g), M)` is the localization at the powers of `g`, as a
map of `Γ(Y, ⊤)`-modules. -/
private lemma isLocalizedModule_resLinear [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    (g : Γ(Y, ⊤)) :
    IsLocalizedModule (.powers g) (resLinear f M p (f.preimage_mono le_top :
      f ⁻¹ᵁ Y.basicOpen g ≤ f ⁻¹ᵁ ⊤)) :=
  letI := f.appTop.hom.toAlgebra
  letI : ∀ W : X.Opens, Module Γ(Y, ⊤) (cohomologyOn M p W) :=
    fun _ ↦ Module.compHom _ f.appTop.hom
  haveI : ∀ W : X.Opens, IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) (cohomologyOn M p W) :=
    fun _ ↦ IsScalarTower.of_compHom _ _ _
  IsLocalizedModule.restrictScalars_powers g (cohomologyOnResLinear M p _)
    (h := isLocalizedModule_cohomologyOnResLinear_preimage_basicOpen f M p g)

/-- The sections of the tilde sheaf over `D(g)` are the localization at `g`. -/
private lemma isLocalizedModule_toOpen (g : Γ(Y, ⊤)) :
    IsLocalizedModule (.powers g) (tilde.toOpen (moduleOn f M p (f ⁻¹ᵁ ⊤))
      ((isAffineOpen_top Y).fromSpec ⁻¹ᵁ Y.basicOpen g)).hom := by
  rw [IsAffineOpen.fromSpec_preimage_basicOpen]
  infer_instance

/-- Both `H^p(f⁻¹ D(g), M)` and the sections of `H^p(X, M)~` over `D(g)` are the localization of
`H^p(X, M)` at the powers of `g`. -/
private def basicOpenEquiv [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    (g : Γ(Y, ⊤)) :
    moduleOn f M p (f ⁻¹ᵁ Y.basicOpen g) ≃ₗ[Γ(Y, ⊤)]
      (modulesSpecToSheaf.obj (tildeTop f M p)).presheaf.obj
        (op ((isAffineOpen_top Y).fromSpec ⁻¹ᵁ Y.basicOpen g)) :=
  @IsLocalizedModule.linearEquiv _ _ (.powers g) _ _ _ _ _ _ _ _ _ _ _
    (isLocalizedModule_resLinear f M p g) (isLocalizedModule_toOpen f M p g)

private lemma basicOpenEquiv_resLinear [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    (g : Γ(Y, ⊤)) (x : moduleOn f M p (f ⁻¹ᵁ ⊤)) :
    basicOpenEquiv f M p g (resLinear f M p (f.preimage_mono le_top) x) =
      (tilde.toOpen _ ((isAffineOpen_top Y).fromSpec ⁻¹ᵁ Y.basicOpen g)).hom x :=
  @IsLocalizedModule.linearEquiv_apply _ _ (.powers g) _ _ _ _ _ _ _ _ _ _ _
    (isLocalizedModule_resLinear f M p g) (isLocalizedModule_toOpen f M p g) x

/-- `basicOpenEquiv` commutes with restriction from `D(g)` to `D(h) ≤ D(g)`. Both composites are
`Γ(Y, ⊤)`-linear maps out of a localization at `g`, into a module on which `g` acts invertibly,
so they agree as soon as they agree on `H^p(X, M)`. -/
private lemma basicOpenEquiv_naturality [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    {g h : Γ(Y, ⊤)} (hgh : Y.basicOpen h ≤ Y.basicOpen g)
    (x : moduleOn f M p (f ⁻¹ᵁ Y.basicOpen g)) :
    ((modulesSpecToSheaf.obj (tildeTop f M p)).presheaf.map
        (homOfLE ((isAffineOpen_top Y).fromSpec.preimage_mono hgh)).op).hom
          (basicOpenEquiv f M p g x) =
      basicOpenEquiv f M p h (resLinear f M p (f.preimage_mono hgh) x) := by
  have hle : (isAffineOpen_top Y).fromSpec ⁻¹ᵁ Y.basicOpen h ≤ PrimeSpectrum.basicOpen g := by
    rw [← IsAffineOpen.fromSpec_preimage_basicOpen]
    exact (isAffineOpen_top Y).fromSpec.preimage_mono hgh
  have hunit (s : Submonoid.powers g) : IsUnit (algebraMap Γ(Y, ⊤) (Module.End Γ(Y, ⊤)
      ((modulesSpecToSheaf.obj (tildeTop f M p)).presheaf.obj
        (op ((isAffineOpen_top Y).fromSpec ⁻¹ᵁ Y.basicOpen h)))) s) := by
    obtain ⟨_, n, rfl⟩ := s
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen
      (M := tildeTop f M p) g hle).pow n
  refine LinearMap.congr_fun (@IsLocalizedModule.ext _ _ (.powers g) _ _ _ _ _ _ _ _ _
    (resLinear f M p (f.preimage_mono le_top)) (isLocalizedModule_resLinear f M p g) hunit
    (((modulesSpecToSheaf.obj (tildeTop f M p)).presheaf.map
        (homOfLE ((isAffineOpen_top Y).fromSpec.preimage_mono hgh)).op).hom ∘ₗ
      (basicOpenEquiv f M p g).toLinearMap)
    ((basicOpenEquiv f M p h).toLinearMap ∘ₗ resLinear f M p (f.preimage_mono hgh)) ?_) x
  ext y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, basicOpenEquiv_resLinear]
  have hy : resLinear f M p (f.preimage_mono hgh) (resLinear f M p (f.preimage_mono le_top) y) =
      resLinear f M p (f.preimage_mono le_top) y := by
    rw [resLinear_apply, resLinear_apply, resLinear_apply]
    exact cohomologyOnRes_comp_apply M p _ _ y
  rw [hy, basicOpenEquiv_resLinear]
  rfl

/-- The natural isomorphism, on the basic opens of `Y`, between `V ↦ H^p(f⁻¹ V, M)` and the
sections of the tilde sheaf of `H^p(X, M)`. -/
private def basicOpenNatTrans [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] :
    (inducedFunctor (basicOpenFamily Y)).op ⋙
        ((Opens.map f.base).op ⋙ ((toSheaf X).obj M).cohomologyPresheaf p) ⟶
      (inducedFunctor (basicOpenFamily Y)).op ⋙ (tildeSheaf f M p).obj where
  app g := AddCommGrpCat.ofHom (basicOpenEquiv f M p g.unop).toLinearMap.toAddMonoidHom
  naturality g h φ := by
    ext x
    have h₁ : (((inducedFunctor (basicOpenFamily Y)).op ⋙
        (Opens.map f.base).op ⋙ ((toSheaf X).obj M).cohomologyPresheaf p).map φ) x =
        resLinear f M p (f.preimage_mono φ.unop.hom.le) x :=
      (resLinear_apply f M p _ x).symm
    have h₂ (y) : (((inducedFunctor (basicOpenFamily Y)).op ⋙ (tildeSheaf f M p).obj).map φ) y =
        ((modulesSpecToSheaf.obj (tildeTop f M p)).presheaf.map
          (homOfLE ((isAffineOpen_top Y).fromSpec.preimage_mono φ.unop.hom.le)).op).hom y := rfl
    refine (congrArg (basicOpenEquiv f M p h.unop) h₁).trans ?_
    exact (basicOpenEquiv_naturality f M p φ.unop.hom.le x).symm.trans (h₂ _).symm

/-- **Higher direct images over the basic opens of an affine base.** For a quasi-compact
quasi-separated morphism `f : X ⟶ Y` to an affine scheme and a quasi-coherent `M`, the comparison
map `H^p(f⁻¹ D(g), M) ⟶ Γ(D(g), R^p f_* M)` is bijective for every basic open `D(g)` of `Y`. -/
theorem bijective_toHigherDirectImageSections_basicOpen [QuasiCompact f] [QuasiSeparated f]
    [M.IsQuasicoherent] (g : Γ(Y, ⊤)) :
    Function.Bijective (toHigherDirectImageSections f M p (Y.basicOpen g)) := by
  have := TopCat.Opens.coverDense_inducedFunctor (isBasis_basicOpen Y)
  let β := Functor.IsCoverDense.restrictHomEquivHom (basicOpenNatTrans f M p)
  have hβ (g' : Γ(Y, ⊤)) : Function.Bijective (β.app (op (Y.basicOpen g'))) := by
    change Function.Bijective
      ((Functor.whiskerLeft (inducedFunctor (basicOpenFamily Y)).op β).app (op g'))
    rw [show Functor.whiskerLeft (inducedFunctor (basicOpenFamily Y)).op β = _ from
      Functor.IsCoverDense.sheafHom_restrict_eq (basicOpenNatTrans f M p)]
    exact (basicOpenEquiv f M p g').bijective
  have h₁ := Functor.IsCoverDense.bijective_toSheafify_app
    (G := inducedFunctor (basicOpenFamily Y)) β hβ g
  have h₂ := ConcreteCategory.bijective_of_isIso (((sheafToPresheaf _ _).mapIso
    (f.toSheafHigherDirectImageObjIsoSheafify M p).symm).app (op (Y.basicOpen g))).hom
  exact h₂.comp h₁

/-- **Higher direct images over an affine base.** For a quasi-compact quasi-separated morphism
`f : X ⟶ Y` to an affine scheme and a quasi-coherent `M`, the comparison map
`H^p(X, M) ⟶ Γ(Y, R^p f_* M)` is bijective. -/
theorem bijective_toHigherDirectImageSections_top [QuasiCompact f] [QuasiSeparated f]
    [M.IsQuasicoherent] : Function.Bijective (toHigherDirectImageSections f M p ⊤) := by
  have := bijective_toHigherDirectImageSections_basicOpen f M p 1
  rwa [Scheme.basicOpen_one] at this

end Affine

/-- **Higher direct images over affine opens.** For a quasi-compact quasi-separated morphism
`f : X ⟶ Y`, a quasi-coherent `M` and an affine open `V` of `Y`, the sections of `R^p f_* M` over
`V` are `H^p(f⁻¹ V, M)`. The isomorphism restricts to `V`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageRestrictIso`), applies
`AlgebraicGeometry.Scheme.Hom.bijective_toHigherDirectImageSections_top` to `f ∣_ V`, and
identifies the cohomology of the open subscheme `f⁻¹ V` with that of the open subset. -/
def higherDirectImageSectionsIso [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    {V : Y.Opens} (hV : IsAffineOpen V) :
    ((toSheaf Y).obj ((f.higherDirectImage p).obj M)).obj.obj (op V) ≅
      cohomologyOn M p (f ⁻¹ᵁ V) :=
  haveI : IsAffine V := hV
  eqToIso (by rw [Scheme.Opens.ι_image_top]; rfl) ≪≫
    (Scheme.Modules.restrictAppIso V.ι _ ⊤).symm ≪≫
    ((sheafToPresheaf _ _).mapIso
      ((toSheaf V).mapIso ((f.higherDirectImageRestrictIso V p).app M))).app (op ⊤) ≪≫
    (AddEquiv.ofBijective _ (bijective_toHigherDirectImageSections_top (f ∣_ V)
      (M.restrict (f ⁻¹ᵁ V).ι) p)).toAddCommGrpIso.symm ≪≫
    cohomologyOnTopIso _ p ≪≫
    (Scheme.Modules.cohomologyOnOpensRangeIso (f ⁻¹ᵁ V).ι M p).symm ≪≫
    eqToIso (congrArg (cohomologyOn M p) (Scheme.Opens.opensRange_ι _))

end AlgebraicGeometry.Scheme.Hom
