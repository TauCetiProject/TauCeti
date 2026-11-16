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
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageBasicOpenSectionsAddEquiv`).

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
* `AlgebraicGeometry.Scheme.Hom.cohomologyHigherDirectImageGlobalSectionsLinearEquiv`: over an
  affine base `Y` with `f : X ⟶ Y` a morphism over `Spec R`, the `R`-linear equivalence
  `Hⁿ(X, M) ≃ₗ[R] Γ(Rⁿ f_* M, ⊤)`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5.
* The Stacks Project, Lemma 30.4.5 (tag 01XJ).
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

/-- Over an affine base `Y`, the additive identification of `Hⁿ(f⁻¹ V, M)` with the sections of
`Rⁿ f_* M` over a basic open `V` intertwines the action of a global function `r ∈ Γ(Y, ⊤)` via
`f^* r` on cohomology with multiplication by `r|_V` on sections. -/
theorem higherDirectImageBasicOpenSectionsAddEquiv_smul {V : Y.Opens}
    (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V) (r : Γ(Y, ⊤)) (x : cohomologyOn M n (f ⁻¹ᵁ V)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M n hV (f.appTop r • x) =
      Y.presheaf.map V.leTop.op r • f.higherDirectImageBasicOpenSectionsAddEquiv M n hV x := by
  let e := f.higherDirectImagePresheafToPresheafIso M n
  let y : ((f.higherDirectImagePresheaf n).obj M).obj (.op V) := (e.app (.op V)).inv x
  have hy : e.hom.app (.op V) y = x := Iso.inv_hom_id_apply (e.app (.op V)) x
  let rV : Y.ringCatSheaf.obj.obj (.op V) := Y.presheaf.map V.leTop.op r
  have hsmul : e.hom.app (.op V) (rV • y) = f.appTop r • x :=
    (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r V y).trans
      (congrArg (f.appTop r • ·) hy)
  rw [← hsmul, ← hy,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    ((f.higherDirectImagePresheaf n).obj M)).app (.op V)
  let φ := ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op V)
  exact (congrArg φ (η.hom.map_smul rV y)).trans (φ.hom.map_smul rV (η y))

/-- At `V = ⊤ = D(1)`, the global-sections identification `Hⁿ(f⁻¹ ⊤, M) ≃+ Γ(Rⁿ f_* M, ⊤)` carries
the action of `f^* r` on cohomology to multiplication by `r` on global sections. -/
theorem higherDirectImageBasicOpenSectionsAddEquiv_top_smul (r : Γ(Y, ⊤))
    (x : cohomologyOn M n (f ⁻¹ᵁ ⊤)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩ (f.appTop r • x) =
      r • f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩ x := by
  refine (f.higherDirectImageBasicOpenSectionsAddEquiv_smul M n ⟨1, Y.basicOpen_one⟩ r x).trans ?_
  rw [Subsingleton.elim (⊤ : Y.Opens).leTop (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` over `Spec R` with affine target `Y`
and a quasi-coherent `𝒪_X`-module `M`, the cohomology `Hⁿ(X, M)` is `R`-linearly equivalent to the
global sections `Γ(Rⁿ f_* M, ⊤)`. -/
def cohomologyHigherDirectImageGlobalSectionsLinearEquiv (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))] :
    Cohomology M n ≃ₗ[R] Γ((f.higherDirectImage n).obj M, ⊤) :=
  let e := f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩
  let e' : cohomologyOn M n (f ⁻¹ᵁ ⊤) ≃ₗ[R] Γ((f.higherDirectImage n).obj M, ⊤) :=
    e.toLinearEquiv fun r x ↦ by
      have hr : f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
        rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
          ← CommRingCat.comp_apply, ← comp_appTop, HomIsOver.comp_over]
      rw [base_smul_cohomologyOn, ← hr,
        f.higherDirectImageBasicOpenSectionsAddEquiv_top_smul, base_smul_globalSections]
  (cohomologyOnTopBaseLinearEquiv M R n).symm.trans e'

/-- Evaluation of `cohomologyHigherDirectImageGlobalSectionsLinearEquiv` via
`higherDirectImageBasicOpenSectionsAddEquiv` on `D(1) = ⊤`. -/
@[simp]
theorem cohomologyHigherDirectImageGlobalSectionsLinearEquiv_apply (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (x : Cohomology M n) :
    f.cohomologyHigherDirectImageGlobalSectionsLinearEquiv M n R x =
      f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩
        ((cohomologyOnTopBaseLinearEquiv M R n).symm x) :=
  (rfl)

/-- Evaluation of the inverse of `cohomologyHigherDirectImageGlobalSectionsLinearEquiv` via the
inverse of `higherDirectImageBasicOpenSectionsAddEquiv` on `D(1) = ⊤`. -/
@[simp]
theorem cohomologyHigherDirectImageGlobalSectionsLinearEquiv_symm_apply (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (y : Γ((f.higherDirectImage n).obj M, ⊤)) :
    (f.cohomologyHigherDirectImageGlobalSectionsLinearEquiv M n R).symm y =
      cohomologyOnTopBaseLinearEquiv M R n
        ((f.higherDirectImageBasicOpenSectionsAddEquiv M n ⟨1, Y.basicOpen_one⟩).symm y) :=
  (rfl)

end Affine

section AffineNaturality

variable [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]

/-- Over an affine base `Y`, `higherDirectImageBasicOpenSectionsAddEquiv` is natural in morphisms
`φ : M₁ ⟶ M₂` of quasi-coherent `𝒪_X`-modules. -/
theorem higherDirectImageBasicOpenSectionsAddEquiv_naturality
    {M₁ M₂ : X.Modules} [M₁.IsQuasicoherent] [M₂.IsQuasicoherent] (φ : M₁ ⟶ M₂) (n : ℕ)
    {V : Y.Opens} (hV : ∃ g : Γ(Y, ⊤), Y.basicOpen g = V) (x : cohomologyOn M₁ n (f ⁻¹ᵁ V)) :
    f.higherDirectImageBasicOpenSectionsAddEquiv M₂ n hV (cohomologyOnMap φ n (f ⁻¹ᵁ V) x) =
      ((f.higherDirectImage n).map φ).app V
        (f.higherDirectImageBasicOpenSectionsAddEquiv M₁ n hV x) := by
  let e₁ := f.higherDirectImagePresheafToPresheafIso M₁ n
  let e₂ := f.higherDirectImagePresheafToPresheafIso M₂ n
  let y : ((f.higherDirectImagePresheaf n).obj M₁).obj (.op V) := (e₁.app (.op V)).inv x
  have hy : e₁.hom.app (.op V) y = x := Iso.inv_hom_id_apply (e₁.app (.op V)) x
  let ψ := (f.higherDirectImagePresheaf n).map φ
  have hnat₀ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (f.higherDirectImagePresheafToPresheafIso_naturality φ n) (.op V)) y
  simp only [NatTrans.comp_app] at hnat₀
  have hφ : e₂.hom.app (.op V) (ψ.app (.op V) y) = cohomologyOnMap φ n (f ⁻¹ᵁ V) x :=
    hnat₀.trans (congrArg (cohomologyOnMap φ n (f ⁻¹ᵁ V)) hy)
  rw [← hφ, ← hy,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageBasicOpenSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  exact (congrArg (((f.higherDirectImagePresheafSheafificationIso n).app M₂).hom.val.app (.op V))
    (congrArg (fun g ↦ g.app (.op V) y) (adj.unit.naturality ψ))).trans
    (congrArg (fun g ↦ g.val.app (.op V) ((adj.unit.app _).app (.op V) y))
      ((f.higherDirectImagePresheafSheafificationIso n).hom.naturality φ))

/-- `cohomologyHigherDirectImageGlobalSectionsLinearEquiv` is natural in morphisms `φ : M₁ ⟶ M₂`
of quasi-coherent `𝒪_X`-modules, intertwining `cohomologyMapBaseLinear` with the map induced by
`Rⁿ f_* φ` on global sections. -/
theorem cohomologyHigherDirectImageGlobalSectionsLinearEquiv_naturality
    {M₁ M₂ : X.Modules} [M₁.IsQuasicoherent] [M₂.IsQuasicoherent] (φ : M₁ ⟶ M₂) (n : ℕ)
    (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    [f.IsOver (Spec (.of R))] (x : Cohomology M₁ n) :
    f.cohomologyHigherDirectImageGlobalSectionsLinearEquiv M₂ n R
        (cohomologyMapBaseLinear R X φ n x) =
      ((f.higherDirectImage n).map φ).app ⊤
        (f.cohomologyHigherDirectImageGlobalSectionsLinearEquiv M₁ n R x) := by
  let x₀ : cohomologyOn M₁ n ⊤ := (cohomologyOnTopBaseLinearEquiv M₁ R n).symm x
  have htop : (cohomologyOnTopBaseLinearEquiv M₂ R n).symm (cohomologyMapBaseLinear R X φ n x) =
      cohomologyOnMap φ n ⊤ x₀ := by
    apply (cohomologyOnTopBaseLinearEquiv M₂ R n).injective
    rw [LinearEquiv.apply_symm_apply, cohomologyMapBaseLinear_apply,
      cohomologyOnTopBaseLinearEquiv_apply, cohomologyOnTopIso_hom_cohomologyOnMap,
      ← cohomologyOnTopBaseLinearEquiv_apply M₁ R n, LinearEquiv.apply_symm_apply]
  exact (congrArg (f.higherDirectImageBasicOpenSectionsAddEquiv M₂ n ⟨1, Y.basicOpen_one⟩)
    htop).trans
    (f.higherDirectImageBasicOpenSectionsAddEquiv_naturality φ n ⟨1, Y.basicOpen_one⟩ x₀)

end AffineNaturality

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

end AlgebraicGeometry.Scheme.Hom
