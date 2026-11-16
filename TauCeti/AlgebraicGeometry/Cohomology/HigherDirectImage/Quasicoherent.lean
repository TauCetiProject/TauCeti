/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Scalars
public import TauCeti.AlgebraicGeometry.Modules.LocallyBijective
import TauCeti.Algebra.Module.LocalizedModule.Map
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Restrict
import TauCeti.AlgebraicGeometry.Cohomology.Localization

/-!
# Higher direct images of quasi-coherent modules are quasi-coherent

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and `M` a
quasi-coherent `𝒪_X`-module. Then every higher direct image `Rⁿ f_* M` is quasi-coherent
(`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_higherDirectImage`). Over an affine base `Y` with
`X` quasi-compact and quasi-separated, its sections over a basic open `D(g)` of `Y` are the
cohomology `Hⁿ(f⁻¹ D(g), M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv`). In particular, its
global sections are identified with `Hⁿ(X, M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv`), compatibly with the
action of global functions (`higherDirectImageGlobalSectionsAddEquiv_smul`). When `Y = Spec R`,
this promotes to an `R`-linear equivalence `Hⁿ(X, M) ≃ₗ[R] Γ(Rⁿ f_* M, ⊤)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyEquivHigherDirectImageSections`), and because
`Rⁿ f_* M` is quasi-coherent, the tilde–global-sections counit yields an isomorphism of
`𝒪_{Spec R}`-modules `Hⁿ(X, M)~ ≅ Rⁿ f_* M`
(`AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`).

The higher direct image is the sheafification of the presheaf of `𝒪_Y`-modules
`V ↦ Hⁿ(f⁻¹ V, M)` (`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheaf`). If `X` is
quasi-compact and quasi-separated, the restriction of this presheaf from `Y` to the basic open
`D(g)` of a global function `g` is the localization at the powers of `g`
(`AlgebraicGeometry.Scheme.Hom.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen`): its
underlying map is the restriction `Hⁿ(X, M) ⟶ Hⁿ(X_{f^* g}, M)`, which is a localization because
cohomology of quasi-coherent modules commutes with localization
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_inf_basicOpen`), and
its scalar action is the action through pullback of functions
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_smul`). A presheaf
of modules with this property on an affine scheme has quasi-coherent sheafification, with the
same sections over basic opens
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyBijective`). Over a general base,
higher direct images are local on the target
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageRestrictIso`), and `f` restricts over each affine
open of `Y` to a morphism from a quasi-compact quasi-separated scheme.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen`: for
  quasi-compact quasi-separated `X` and quasi-coherent `M`, the restriction of `V ↦ Hⁿ(f⁻¹ V, M)`
  from `Y` to `D(g)` is the localization at the powers of `g`;
* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_higherDirectImage`: the higher direct images of a
  quasi-coherent module along a quasi-compact quasi-separated morphism are quasi-coherent;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv`: over an affine base,
  the sections of `Rⁿ f_* M` over `D(g)` are `Hⁿ(f⁻¹ D(g), M)`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv`: additive equivalence
  `Hⁿ(X, M) ≃+ Γ(Rⁿ f_* M, ⊤)` over an affine base, with scalar compatibility
  `AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv_smul`;
* `AlgebraicGeometry.Scheme.Modules.cohomologyEquivHigherDirectImageSections`: `R`-linear
  equivalence `Hⁿ(X, M) ≃ₗ[R] moduleSpecΓFunctor.obj (Rⁿ f_* M)` for `X` quasi-compact and
  quasi-separated over `Spec R`;
* `AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`: isomorphism
  `Hⁿ(X, M)~ ≅ Rⁿ f_* M` of `𝒪_{Spec R}`-modules.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5.
* [The Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ) (quasi-coherence of
  higher direct images) and [Tag 01XK](https://stacks.math.columbia.edu/tag/01XK) (higher direct
  images over an affine base).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Higher direct images commute with localization.** For a quasi-compact quasi-separated
scheme `X`, a quasi-coherent `M` and a global function `g` on `Y`, the restriction of the presheaf
of modules `V ↦ Hⁿ(f⁻¹ V, M)` from `Y` to the basic open `D(g)` is the localization at the
powers of `g`. -/
theorem isLocalizedModule_higherDirectImagePresheaf_map_basicOpen [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (g : Γ(Y, ⊤)) :
    IsLocalizedModule (.powers g) (PresheafOfModulesOfCommRing.map (R := Y.presheaf)
      ((f.higherDirectImagePresheaf n).obj M) (homOfLE (Y.basicOpen_le g)).op).hom := by
  let e := f.higherDirectImagePresheafToPresheafIso M n
  have hW : f ⁻¹ᵁ Y.basicOpen g = f ⁻¹ᵁ ⊤ ⊓ X.basicOpen (f.appTop g) := by
    rw [Scheme.preimage_basicOpen]
    exact (inf_eq_right.2 (X.basicOpen_le _)).symm
  have : IsLocalizedModule ((Submonoid.powers g).map f.appTop.hom)
      (cohomologyOnResLinear M n (f.preimage_mono (Y.basicOpen_le g))) := by
    rw [Submonoid.map_powers]
    exact isLocalizedModule_cohomologyOnResLinear_inf_basicOpen M _
      (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) _ hW n
  -- Identify the restriction map with restriction in cohomology, semilinearly along `f^*`.
  refine IsLocalizedModule.of_bijective_semilinearMap (.powers g) _
    (cohomologyOnResLinear M n (f.preimage_mono (Y.basicOpen_le g)))
    { toFun := e.hom.app (.op ⊤)
      map_add' := map_add _
      map_smul' := fun r x ↦ ?_ }
    { toFun := e.hom.app (.op (Y.basicOpen g))
      map_add' := map_add _
      map_smul' := fun r x ↦
        f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r (Y.basicOpen g) x }
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op ⊤)))
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op (Y.basicOpen g)))) fun x ↦ ?_
  · refine (congrArg _ ?_).trans (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r ⊤ x)
    -- the inclusion of `⊤` into itself is the identity, as morphisms of a preorder are unique
    rw [show (⊤ : Y.Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  · rw [cohomologyOnResLinear_apply]
    exact ConcreteCategory.congr_hom (e.hom.naturality (homOfLE (Y.basicOpen_le g)).op) x

section Affine

variable [IsAffine Y] [QuasiCompact f] [QuasiSeparated f] (M : X.Modules)
  [M.IsQuasicoherent] (n : ℕ)

/-- **Higher direct images over an affine base.** For a quasi-compact quasi-separated scheme `X`
over an affine scheme `Y` and a quasi-coherent `M`, the sections of the higher direct image
`Rⁿ f_* M` over an open `V` equal to the basic open of a global function are the cohomology
`Hⁿ(f⁻¹ V, M)`. The equivalence sends a class to the section of the sheafification of
`V ↦ Hⁿ(f⁻¹ V, M)` that it defines
(`higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app`). -/
def higherDirectImageBasicOpenSectionsAddEquiv {V : Y.Opens}
    (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V) :
    cohomologyOn M n (f ⁻¹ᵁ V) ≃+ Γ((f.higherDirectImage n).obj M, V) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf n).obj M)).app (.op V)
  let e := ((f.higherDirectImagePresheafToPresheafIso M n).app (.op V)).symm
  let i := ((Scheme.Modules.toPresheaf Y).mapIso
    ((f.higherDirectImagePresheafSheafificationIso n).app M)).app (.op V)
  exact e.addCommGroupIsoToAddEquiv.trans ((AddEquiv.ofBijective η.hom.toAddMonoidHom
    (by
      obtain ⟨g, rfl⟩ := hV
      have hY := isAffineOpen_top Y
      exact hY.bijective_sheafificationAdjunction_unit_app_basicOpen_of_isLocalizedModule _
        (f.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen M n) g)).trans
      i.addCommGroupIsoToAddEquiv)

/-- The equivalence `higherDirectImageBasicOpenSectionsAddEquiv` sends the class in
`Hⁿ(f⁻¹ V, M)` of a section `x` of the presheaf `V ↦ Hⁿ(f⁻¹ V, M)` to the section of its
sheafification `Rⁿ f_* M` defined by `x`. -/
-- Apply before simp normalizes the cohomology presheaf section type.
@[simp↓]
lemma higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
    {V : Y.Opens} (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V)
    (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M n hV
        ((f.higherDirectImagePresheafToPresheafIso M n).hom.app _ x) =
      ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app _
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((f.higherDirectImagePresheaf n).obj M)).app _ x) := by
  -- the equivalence first inverts the identification of the presheaf with cohomology
  exact congrArg (fun y ↦ ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app _
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
      ((f.higherDirectImagePresheaf n).obj M)).app _ y))
    (Iso.hom_inv_id_apply ((f.higherDirectImagePresheafToPresheafIso M n).app _) x)

/-- Over an affine base, the higher direct images of a quasi-coherent module on a quasi-compact
quasi-separated scheme are quasi-coherent. -/
private lemma isQuasicoherent_higherDirectImage_of_isAffine :
    ((f.higherDirectImage n).obj M).IsQuasicoherent := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  apply (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((f.higherDirectImagePresheafSheafificationIso n).app M)
  exact Scheme.Modules.isQuasicoherent_sheafification_of_isLocalizedModule _
    (fun _ : Unit ↦ ⊤) (fun _ ↦ isAffineOpen_top Y) iSup_const
    fun _ ↦ f.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen M n

end Affine

/-- **Higher direct images of quasi-coherent modules are quasi-coherent.** For a quasi-compact
quasi-separated morphism `f : X ⟶ Y` and a quasi-coherent `𝒪_X`-module `M`, every higher direct
image `Rⁿ f_* M` is quasi-coherent. -/
instance isQuasicoherent_higherDirectImage [QuasiCompact f] [QuasiSeparated f] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) : ((f.higherDirectImage n).obj M).IsQuasicoherent := by
  refine (Scheme.Modules.isQuasicoherent_iff_of_iSup_eq_top _ (fun U : Y.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Y)).2 fun U ↦ ?_
  -- over the affine open `U`, the higher direct image is that of `f ∣_ U`, whose source
  -- `f⁻¹ U` is quasi-compact and quasi-separated
  have : IsAffine U.1 := U.2
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    ((f.higherDirectImageRestrictIso U.1 n).app M).symm
    (isQuasicoherent_higherDirectImage_of_isAffine (f ∣_ U.1) (M.restrict (f ⁻¹ᵁ U.1).ι) n)

/-- Restriction along the equality `f ⁻¹ᵁ ⊤ = ⊤` identifies `Hⁿ(X, M)` with `Hⁿ(f⁻¹ ⊤, M)`
linearly over global functions without unfolding `cohomologyOn`. -/
private def cohomologyEquivPreimageTop (M : X.Modules) (n : ℕ) :
    Cohomology M n ≃ₗ[Γ(X, ⊤)] cohomologyOn M n (f ⁻¹ᵁ ⊤) :=
  let res : cohomologyOn M n ⊤ ≃ₗ[Γ(X, ⊤)] cohomologyOn M n (f ⁻¹ᵁ ⊤) :=
    LinearEquiv.ofLinearMap (cohomologyOnResLinear M n (le_of_eq f.preimage_top))
      (cohomologyOnResLinear M n (le_of_eq f.preimage_top.symm))
      (by rw [cohomologyOnResLinear_comp, cohomologyOnResLinear_refl])
      (by rw [cohomologyOnResLinear_comp, cohomologyOnResLinear_refl])
  (cohomologyOnTopLinearEquiv M n).symm.trans res

section AffineGlobalSections

variable [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]

/-- **Global sections of a higher direct image over an affine base.** For a quasi-compact,
quasi-separated morphism `f : X ⟶ Y` to an affine scheme `Y` and a quasi-coherent `𝒪_X`-module
`M`, the cohomology `Hⁿ(X, M)` is additively equivalent to the global sections of `Rⁿ f_* M`. -/
def higherDirectImageGlobalSectionsAddEquiv (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Cohomology M n ≃+ Γ((f.higherDirectImage n).obj M, ⊤) :=
  (cohomologyEquivPreimageTop f M n).toAddEquiv.trans
    (f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩)

/-- The identification `Hⁿ(X, M) ≃+ Γ(Rⁿ f_* M, ⊤)` carries the action of a pulled-back global
function `f^* r` on cohomology to scalar multiplication by `r` on global sections of `Rⁿ f_* M`. -/
theorem higherDirectImageGlobalSectionsAddEquiv_smul (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (r : Γ(Y, ⊤)) (x : Cohomology M n) :
    f.higherDirectImageGlobalSectionsAddEquiv M n (f.appTop r • x) =
      r • f.higherDirectImageGlobalSectionsAddEquiv M n x := by
  let e := f.higherDirectImagePresheafToPresheafIso M n
  have hbij := ConcreteCategory.bijective_of_isIso (e.hom.app (.op ⊤))
  obtain ⟨y₀, hy₀⟩ := hbij.2 (cohomologyEquivPreimageTop f M n x)
  let y : ((f.higherDirectImagePresheaf n).obj M).obj (.op ⊤) := y₀
  have hy : (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) y =
      cohomologyEquivPreimageTop f M n x := hy₀
  -- Apply the basic-open comparison at `⊤ = D(1)` and use linearity of sheafification.
  simp only [higherDirectImageGlobalSectionsAddEquiv, AddEquiv.trans_apply,
    LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply, LinearEquiv.map_smul, ← hy]
  rw [← f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r ⊤ y,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf n).obj M)).app (.op ⊤)
  let i := ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op ⊤)
  -- `Y.ringCatSheaf.obj.obj (.op ⊤)` has carrier `Γ(Y, ⊤)` with the same scalar action on global
  -- sections, and restriction along `⊤ ⟶ ⊤` is the identity.
  exact ((congrArg i (η.hom.map_smul _ y)).trans (i.hom.map_smul _ (η y))).trans
    (congrArg (· • (i (η y) : Γ((f.higherDirectImage n).obj M, ⊤)))
      ((congrArg (fun φ ↦ φ r) (Scheme.presheaf_map_top_leTop Y)).trans
        (ConcreteCategory.id_apply r)))

end AffineGlobalSections

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry.Scheme.Modules

/-- **Cohomology as global sections of the higher direct image over `Spec R`.** For a
quasi-compact, quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`,
`Hⁿ(X, M)` is `R`-linearly equivalent to the global sections of `Rⁿ (X ↘ Spec R)_* M`. -/
def cohomologyEquivHigherDirectImageSections (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Cohomology M n ≃ₗ[R]
      moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) where
  __ := (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n
  map_smul' r x := by
    let f := X ↘ Spec (.of R)
    simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
    -- `moduleSpecΓFunctor.obj N` has carrier `Γ(N, ⊤)` with the `R`-module structure given by
    -- `Scheme.Modules.smul_Spec_def`, which `rw` does not match through the functor application.
    have hrhs :
        (r : R) • (show moduleSpecΓFunctor.obj ((f.higherDirectImage n).obj M) from
          f.higherDirectImageGlobalSectionsAddEquiv M n x) =
        (Scheme.ΓSpecIso (.of R)).inv r • f.higherDirectImageGlobalSectionsAddEquiv M n x := by
      refine (Scheme.Modules.smul_Spec_def (M := (f.higherDirectImage n).obj M) (U := ⊤) r
        (f.higherDirectImageGlobalSectionsAddEquiv M n x)).trans ?_
      simp
    rw [hrhs, base_smul_cohomology, baseRingToGlobalSections_apply]
    exact f.higherDirectImageGlobalSectionsAddEquiv_smul M n ((Scheme.ΓSpecIso (.of R)).inv r) x

/-- `cohomologyEquivHigherDirectImageSections` agrees on elements with
`higherDirectImageGlobalSectionsAddEquiv`. -/
@[simp]
theorem cohomologyEquivHigherDirectImageSections_apply (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Cohomology M n) :
    (cohomologyEquivHigherDirectImageSections R M n x :
        Γ(((X ↘ Spec (.of R)).higherDirectImage n).obj M, ⊤)) =
      (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv M n x := by
  rfl

/-- **Higher direct images over an affine base are associated to cohomology.** For a
quasi-compact, quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`,
the higher direct image `Rⁿ (X ↘ Spec R)_* M` is isomorphic as an `𝒪_{Spec R}`-module to the
quasi-coherent sheaf `Hⁿ(X, M)~`. -/
def tildeCohomologyIsoHigherDirectImage (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅
      ((X ↘ Spec (.of R)).higherDirectImage n).obj M :=
  (tilde.functor (.of R)).mapIso (cohomologyEquivHigherDirectImageSections R M n).toModuleIso ≪≫
    @asIso _ _ _ _ (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ
      (isIso_fromTildeΓ_of_isQuasicoherent _)

end AlgebraicGeometry.Scheme.Modules
