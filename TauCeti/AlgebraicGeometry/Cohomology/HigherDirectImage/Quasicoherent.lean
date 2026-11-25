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
# Higher direct images of quasi-coherent modules

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and `M` a
quasi-coherent `𝒪_X`-module. Then every higher direct image `Rⁿ f_* M` is quasi-coherent
(`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_higherDirectImage`), and over every affine open `V`
of `Y` its sections are the cohomology `Hⁿ(f⁻¹ V, M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv`). The base `Y` need not be
affine. As a module over `Γ(Y, V)`, these sections are the sections over `V` of the presheaf of
modules `V ↦ Hⁿ(f⁻¹ V, M)` whose sheafification is `Rⁿ f_* M`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafSectionsLinearEquiv`). Both
identifications are natural in the quasi-coherent module `M`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv_naturality` and
`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafSectionsLinearEquiv_naturality`). Over an
affine base `Y` with `X` quasi-compact and quasi-separated, its global sections are identified with
`Hⁿ(X, M)` (`AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv`), compatibly
with the action of global functions (`higherDirectImageGlobalSectionsAddEquiv_smul`), giving a
`Γ(Y, ⊤)`-linear equivalence
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsLinearEquiv`). When `Y = Spec R`,
restricting scalars along `Scheme.ΓSpecIso.inv` promotes this to an `R`-linear equivalence
`Hⁿ(X, M) ≃ₗ[R] Γ(Rⁿ f_* M, ⊤)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyEquivHigherDirectImageSections`), and because
`Rⁿ f_* M` is quasi-coherent, the tilde–global-sections counit yields an isomorphism of
`𝒪_{Spec R}`-modules `Hⁿ(X, M)~ ≅ Rⁿ f_* M`
(`AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`). All of these comparisons
are natural in the coefficient module `M`.

The higher direct image is the sheafification of the presheaf of `𝒪_Y`-modules
`V ↦ Hⁿ(f⁻¹ V, M)` (`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheaf`). Let `W` be an open
of `Y` with `f⁻¹ W` quasi-compact and quasi-separated. The restriction of this presheaf from `W` to
the basic open `D(s)` of a function `s` on `W` is the localization at the powers of `s`
(`AlgebraicGeometry.Scheme.Hom.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen`). For
`W = Y` its underlying map is the restriction `Hⁿ(X, M) ⟶ Hⁿ(X_{f^* s}, M)`, which is a
localization because cohomology of quasi-coherent modules commutes with localization
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_inf_basicOpen`), and its
scalar action is the action through pullback of functions
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_smul`). For general
`W`, the function `s` acts on `Hⁿ(f⁻¹ W, M)` only through the module structure of the presheaf.
Restricting the presheaf to the open subscheme `W` gives the presheaf of `f ∣_ W`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafRestrictIso`), on which `s` is a global
function, so the case `W = Y` applies
(`Scheme.PresheafOfModules.isLocalizedModule_map_basicOpen_of_restrictFunctor_obj_iso`). When
the restrictions of a presheaf of modules from an affine open to its basic opens are
localizations, the presheaf has the same sections over that affine open as its sheafification
(`AlgebraicGeometry.IsAffineOpen.bijective_sheafificationAdjunction_unit_app_of_isLocalizedModule`),
and when this holds on an affine open cover, here all affine opens of `Y`, the sheafification is
quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sheafification_of_isLocalizedModule`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen`: for
  `f⁻¹ W` quasi-compact and quasi-separated and `M` quasi-coherent, the restriction of
  `V ↦ Hⁿ(f⁻¹ V, M)` from `W` to `D(s)` is the localization at the powers of `s`;
* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_higherDirectImage`: the higher direct images of a
  quasi-coherent module along a quasi-compact quasi-separated morphism are quasi-coherent;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafSectionsLinearEquiv` and
  `AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv`: over an affine open `V` of the
  target, the sections of `Rⁿ f_* M` are those of the presheaf `V ↦ Hⁿ(f⁻¹ V, M)`, linearly over
  `Γ(Y, V)`, hence are `Hⁿ(f⁻¹ V, M)`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv_naturality`: this identification
  is natural in the quasi-coherent module `M`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsAddEquiv` and
  `AlgebraicGeometry.Scheme.Hom.higherDirectImageGlobalSectionsLinearEquiv`: additive and
  `Γ(Y, ⊤)`-linear equivalences `Hⁿ(X, M) ≃ₗ[Γ(Y, ⊤)] Γ(Rⁿ f_* M, ⊤)` over an affine base, with
  evaluation, scalar compatibility, and naturality in `M`;
* `AlgebraicGeometry.Scheme.Modules.cohomologyEquivHigherDirectImageSections`: `R`-linear
  equivalence `Hⁿ(X, M) ≃ₗ[R] moduleSpecΓFunctor.obj (Rⁿ f_* M)` for `X` quasi-compact and
  quasi-separated over `Spec R`, natural in `M`;
* `AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage`: isomorphism
  `Hⁿ(X, M)~ ≅ Rⁿ f_* M` of `𝒪_{Spec R}`-modules, natural in `M`.

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

/-- At the top open `⊤`, `higherDirectImagePresheafToPresheafIso` intertwines the action of a
global function `r` on the presheaf with the action of `f^* r` on cohomology. -/
-- The explicit scalar type identifies `Γ(Y, ⊤)` with the ring presheaf at `op ⊤`.
private lemma higherDirectImagePresheafToPresheafIso_hom_app_top_smul (M : X.Modules) (n : ℕ)
    (r : Γ(Y, ⊤)) (y : ((f.higherDirectImagePresheaf n).obj M).obj (.op ⊤)) :
    (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤)
        ((show Y.ringCatSheaf.obj.obj (.op ⊤) from r) • y) =
      f.appTop r • (show cohomologyOn M n (f ⁻¹ᵁ ⊤) from
        (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤) y) := by
  simpa only [TopCat.Presheaf.map_eq_id, ConcreteCategory.id_apply] using
    f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r ⊤ y

/-- The case `W = ⊤` of `isLocalizedModule_higherDirectImagePresheaf_map_basicOpen`, where the
action of global functions on cohomology is known. -/
private lemma isLocalizedModule_higherDirectImagePresheaf_map_basicOpen_top [CompactSpace X]
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
  refine Iff.mpr (IsLocalizedModule.iff_of_bijective_semilinearMap (.powers g) _
    (cohomologyOnResLinear M n (f.preimage_mono (Y.basicOpen_le g)))
    { toFun := e.hom.app (.op ⊤)
      map_add' := map_add _
      map_smul' := fun r x ↦ f.higherDirectImagePresheafToPresheafIso_hom_app_top_smul M n r x }
    { toFun := e.hom.app (.op (Y.basicOpen g))
      map_add' := map_add _
      map_smul' := fun r x ↦
        f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r (Y.basicOpen g) x }
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op ⊤)))
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op (Y.basicOpen g)))) fun x ↦ ?_)
    inferInstance
  rw [cohomologyOnResLinear_apply]
  exact ConcreteCategory.congr_hom (e.hom.naturality (homOfLE (Y.basicOpen_le g)).op) x

/-- **Higher direct image presheaves commute with localization.** Let `W` be an open of `Y` whose
preimage `f⁻¹ W` is quasi-compact and quasi-separated, `M` a quasi-coherent module on `X` and `s` a
function on `W`. Then the restriction of the presheaf of modules `V ↦ Hⁿ(f⁻¹ V, M)` from `W` to
the basic open `D(s)` is the localization at the powers of `s`. The function `s` need not extend
to `Y`. -/
theorem isLocalizedModule_higherDirectImagePresheaf_map_basicOpen (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) {W : Y.Opens} (hc : IsCompact (f ⁻¹ᵁ W : Set X))
    (hqs : IsQuasiSeparated (f ⁻¹ᵁ W : Set X)) (s : Γ(Y, W)) :
    IsLocalizedModule (.powers s) (PresheafOfModulesOfCommRing.map (R := Y.presheaf)
      ((f.higherDirectImagePresheaf n).obj M) (homOfLE (Y.basicOpen_le s)).op).hom := by
  have : CompactSpace (f ⁻¹ᵁ W) := isCompact_iff_compactSpace.mp hc
  have : QuasiSeparatedSpace (f ⁻¹ᵁ W) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ W).isOpen).mp hqs
  -- The presheaf restricted to `W` is that of `f ∣_ W`, on which `s` is a global function.
  exact Scheme.PresheafOfModules.isLocalizedModule_map_basicOpen_of_restrictFunctor_obj_iso
    ((f.higherDirectImagePresheafRestrictIso W n).app M) s
    (isLocalizedModule_higherDirectImagePresheaf_map_basicOpen_top (f ∣_ W) _ n (W.topIso.inv s))

section QuasiCompactQuasiSeparated

variable [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)

/-- **Higher direct images over affine opens.** For a quasi-compact quasi-separated morphism `f` and
a quasi-coherent module `M`, the presheaf of modules `V ↦ Hⁿ(f⁻¹ V, M)` has the same sections as
its sheafification `Rⁿ f_* M` over every affine open of the target. -/
theorem bijective_higherDirectImagePresheaf_sheafificationAdjunction_unit_app {V : Y.Opens}
    (hV : IsAffineOpen V) : Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        ((f.higherDirectImagePresheaf n).obj M)).app (.op V)) :=
  hV.bijective_sheafificationAdjunction_unit_app_of_isLocalizedModule _ fun s ↦
    f.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen M n
      (f.isCompact_preimage hV.isCompact) (f.isQuasiSeparated_preimage hV.isQuasiSeparated) s

/-- **Higher direct images over affine opens, as modules.** For a quasi-compact quasi-separated
morphism `f`, a quasi-coherent module `M` and an affine open `V` of the target, the sections of
`Rⁿ f_* M` over `V` are, as a module over `Γ(Y, V)`, the sections over `V` of the presheaf of
modules `V ↦ Hⁿ(f⁻¹ V, M)` whose sheafification it is. -/
def higherDirectImagePresheafSectionsLinearEquiv {V : Y.Opens} (hV : IsAffineOpen V) :
    PresheafOfModulesOfCommRing.obj (R := Y.presheaf) ((f.higherDirectImagePresheaf n).obj M)
      (.op V) ≃ₗ[Γ(Y, V)] Γ((f.higherDirectImage n).obj M, V) :=
  LinearEquiv.ofBijective (((PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)).unit.app ((f.higherDirectImagePresheaf n).obj M)).app (.op V) ≫
        ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app (.op V)).hom
    ((ConcreteCategory.bijective_of_isIso ((PresheafOfModules.evaluation _ (.op V)).mapIso
      ((SheafOfModules.forget _).mapIso
        ((f.higherDirectImagePresheafSheafificationIso n).app M))).hom).comp
      (f.bijective_higherDirectImagePresheaf_sheafificationAdjunction_unit_app M n hV))

/-- The equivalence `higherDirectImagePresheafSectionsLinearEquiv` sends a section of the presheaf
`V ↦ Hⁿ(f⁻¹ V, M)` to the section of its sheafification `Rⁿ f_* M` that it defines. -/
@[simp]
lemma higherDirectImagePresheafSectionsLinearEquiv_apply {V : Y.Opens} (hV : IsAffineOpen V)
    (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    f.higherDirectImagePresheafSectionsLinearEquiv M n hV x =
      ((f.higherDirectImagePresheafSheafificationIso n).app M).hom.val.app _
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((f.higherDirectImagePresheaf n).obj M)).app _ x) :=
  (rfl)

/-- **Higher direct images over affine opens, as cohomology.** For a quasi-compact quasi-separated
morphism `f`, a quasi-coherent module `M` and an affine open `V` of the target, the sections of the
higher direct image `Rⁿ f_* M` over `V` are the cohomology `Hⁿ(f⁻¹ V, M)`. The equivalence sends a
class to the section of the sheafification of `V ↦ Hⁿ(f⁻¹ V, M)` that it defines
(`higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app`). -/
def higherDirectImageSectionsAddEquiv {V : Y.Opens} (hV : IsAffineOpen V) :
    cohomologyOn M n (f ⁻¹ᵁ V) ≃+ Γ((f.higherDirectImage n).obj M, V) :=
  ((f.higherDirectImagePresheafToPresheafIso M n).app (.op V)).symm.addCommGroupIsoToAddEquiv.trans
    (f.higherDirectImagePresheafSectionsLinearEquiv M n hV).toAddEquiv

/-- The equivalence `higherDirectImageSectionsAddEquiv` sends the class in `Hⁿ(f⁻¹ V, M)` of a
section `x` of the presheaf `V ↦ Hⁿ(f⁻¹ V, M)` to the section of its sheafification `Rⁿ f_* M`
defined by `x`. -/
-- Apply before simp normalizes the cohomology presheaf section type.
@[simp↓]
lemma higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
    {V : Y.Opens} (hV : IsAffineOpen V)
    (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    f.higherDirectImageSectionsAddEquiv M n hV
        ((f.higherDirectImagePresheafToPresheafIso M n).hom.app _ x) =
      f.higherDirectImagePresheafSectionsLinearEquiv M n hV x := by
  -- the equivalence first inverts the identification of the presheaf with cohomology
  exact congrArg (f.higherDirectImagePresheafSectionsLinearEquiv M n hV)
    (Iso.hom_inv_id_apply ((f.higherDirectImagePresheafToPresheafIso M n).app _) x)

/-- The identification `higherDirectImagePresheafSectionsLinearEquiv` of the sections of the
presheaf `V ↦ Hⁿ(f⁻¹ V, M)` over an affine open with those of `Rⁿ f_* M` is natural in the
quasi-coherent module `M`. -/
lemma higherDirectImagePresheafSectionsLinearEquiv_naturality {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (ψ : M ⟶ N) {V : Y.Opens} (hV : IsAffineOpen V)
    (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    f.higherDirectImagePresheafSectionsLinearEquiv N n hV
        (((f.higherDirectImagePresheaf n).map ψ).app _ x) =
      ((f.higherDirectImage n).map ψ).app V
        (f.higherDirectImagePresheafSectionsLinearEquiv M n hV x) := by
  simp only [higherDirectImagePresheafSectionsLinearEquiv_apply]
  have h₁ := ConcreteCategory.congr_hom (congrArg (fun g ↦ g.app (op V))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.naturality
      ((f.higherDirectImagePresheaf n).map ψ))) x
  have h₂ := congrArg (fun g ↦ Scheme.Modules.Hom.app g V)
    ((f.higherDirectImagePresheafSheafificationIso n).hom.naturality ψ)
  simp only [PresheafOfModules.comp_app, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, Functor.id_map] at h₁ h₂
  rw [h₁]
  exact ConcreteCategory.congr_hom h₂ _

/-- **Naturality of the sections of higher direct images over affine opens.** The identification
`higherDirectImageSectionsAddEquiv` of the sections of `Rⁿ f_* M` over an affine open `V` with
`Hⁿ(f⁻¹ V, M)` is natural in the quasi-coherent module `M`. -/
lemma higherDirectImageSectionsAddEquiv_naturality {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (ψ : M ⟶ N) {V : Y.Opens} (hV : IsAffineOpen V)
    (x : cohomologyOn M n (f ⁻¹ᵁ V)) :
    f.higherDirectImageSectionsAddEquiv N n hV (cohomologyOnMap ψ n (f ⁻¹ᵁ V) x) =
      ((f.higherDirectImage n).map ψ).app V (f.higherDirectImageSectionsAddEquiv M n hV x) := by
  obtain ⟨y, rfl⟩ : ∃ y, (f.higherDirectImagePresheafToPresheafIso M n).hom.app (op V) y = x :=
    ⟨_, Iso.inv_hom_id_apply ((f.higherDirectImagePresheafToPresheafIso M n).app _) x⟩
  have h := ConcreteCategory.congr_hom (congrArg (fun g ↦ g.app (op V))
    (f.higherDirectImagePresheafToPresheafIso_naturality ψ n)) y
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.whiskerLeft_app,
    Functor.op_obj] at h
  rw [← h]
  refine (f.higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
    N n hV _).trans ((f.higherDirectImagePresheafSectionsLinearEquiv_naturality n ψ hV y).trans ?_)
  exact congrArg _
    (f.higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
      M n hV y).symm

/-- Over an affine open `V`, the identification of `Hⁿ(f⁻¹ V, M)` with the sections of
`Rⁿ f_* M` sends a class to the section defined by the corresponding section of the presheaf
`V ↦ Hⁿ(f⁻¹ V, M)`. -/
lemma higherDirectImageSectionsAddEquiv_eq_presheafToSheaf {V : Y.Opens} (hV : IsAffineOpen V)
    (c : cohomologyOn M n (f ⁻¹ᵁ V)) :
    f.higherDirectImageSectionsAddEquiv M n hV c =
      ((f.higherDirectImagePresheafToSheaf n).app M).app (op V)
        ((f.higherDirectImagePresheafToPresheafIso M n).inv.app (op V) c) := by
  have e := f.higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
    M n hV ((f.higherDirectImagePresheafToPresheafIso M n).inv.app (op V) c)
  simp only [Iso.inv_hom_id_app_apply] at e
  refine e.trans ((f.higherDirectImagePresheafSectionsLinearEquiv_apply M n hV _).trans ?_)
  rw [higherDirectImagePresheafToSheaf_app]
  -- Both sides are the sheafification unit followed by the identification with `Rⁿ f_* M`;
  -- restricting scalars along the identity leaves the underlying maps of sections unchanged.
  rfl

/-- **Higher direct images of quasi-coherent modules are quasi-coherent.** For a quasi-compact
quasi-separated morphism `f : X ⟶ Y` and a quasi-coherent `𝒪_X`-module `M`, every higher direct
image `Rⁿ f_* M` is quasi-coherent. -/
instance isQuasicoherent_higherDirectImage :
    ((f.higherDirectImage n).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((f.higherDirectImagePresheafSheafificationIso n).app M)
    (Scheme.Modules.isQuasicoherent_sheafification_of_isLocalizedModule _
      (fun V : Y.affineOpens ↦ V.val) (fun V ↦ V.property) (iSup_affineOpens_eq_top Y) fun V s ↦
        f.isLocalizedModule_higherDirectImagePresheaf_map_basicOpen M n
          (f.isCompact_preimage V.property.isCompact)
              (f.isQuasiSeparated_preimage V.property.isQuasiSeparated)
          s)

end QuasiCompactQuasiSeparated

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
    (f.higherDirectImageSectionsAddEquiv M n (isAffineOpen_top Y))

/-- Evaluating `higherDirectImageGlobalSectionsAddEquiv` restricts a cohomology class along
`f ⁻¹ᵁ ⊤ = ⊤` and applies `higherDirectImageSectionsAddEquiv` on `⊤`. -/
@[simp]
lemma higherDirectImageGlobalSectionsAddEquiv_apply (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Cohomology M n) :
    f.higherDirectImageGlobalSectionsAddEquiv M n x =
      f.higherDirectImageSectionsAddEquiv M n (isAffineOpen_top Y)
        (cohomologyOnRes M n (le_of_eq f.preimage_top)
          ((cohomologyOnTopLinearEquiv M n).symm x)) := by
  simp only [higherDirectImageGlobalSectionsAddEquiv, cohomologyEquivPreimageTop,
    AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply,
    LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap, cohomologyOnResLinear_apply]

/-- The identification `Hⁿ(X, M) ≃+ Γ(Rⁿ f_* M, ⊤)` carries the action of a pulled-back global
function `f^* r` on cohomology to scalar multiplication by `r` on global sections of `Rⁿ f_* M`. -/
theorem higherDirectImageGlobalSectionsAddEquiv_smul (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (r : Γ(Y, ⊤)) (x : Cohomology M n) :
    f.higherDirectImageGlobalSectionsAddEquiv M n (f.appTop r • x) =
      r • f.higherDirectImageGlobalSectionsAddEquiv M n x := by
  -- The underlying abelian presheaf of `(f.higherDirectImagePresheaf n).obj M` has the same
  -- section carrier at `⊤`, so surjectivity yields `y` directly in that module.
  obtain ⟨(y : ((f.higherDirectImagePresheaf n).obj M).obj (.op ⊤)), hy⟩ :=
    (ConcreteCategory.bijective_of_isIso
      ((f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op ⊤))).2
      (cohomologyEquivPreimageTop f M n x)
  -- Apply the affine-open comparison at `⊤`, which is already `Γ(Y, ⊤)`-linear.
  simp only [higherDirectImageGlobalSectionsAddEquiv, AddEquiv.trans_apply,
    LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply, LinearEquiv.map_smul, ← hy]
  rw [← f.higherDirectImagePresheafToPresheafIso_hom_app_top_smul M n r y,
    f.higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app,
    f.higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  exact (f.higherDirectImagePresheafSectionsLinearEquiv M n (isAffineOpen_top Y)).map_smul r y

/-- The global-sections identification `higherDirectImageGlobalSectionsAddEquiv` is natural in
the coefficient sheaf `M`. -/
theorem higherDirectImageGlobalSectionsAddEquiv_naturality {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (n : ℕ) (x : Cohomology M n) :
    f.higherDirectImageGlobalSectionsAddEquiv N n ((cohomologyFunctor X n).map φ x) =
      ((f.higherDirectImage n).map φ).app ⊤ (f.higherDirectImageGlobalSectionsAddEquiv M n x) := by
  have htop :
      (cohomologyOnTopLinearEquiv N n).symm ((cohomologyFunctor X n).map φ x) =
        cohomologyOnMap φ n ⊤ ((cohomologyOnTopLinearEquiv M n).symm x) := by
    apply (cohomologyOnTopLinearEquiv N n).injective
    refine ((cohomologyOnTopLinearEquiv N n).apply_symm_apply _).trans ?_
    refine (congrArg ((cohomologyFunctor X n).map φ)
      ((cohomologyOnTopLinearEquiv M n).apply_symm_apply x)).symm.trans ?_
    rw [cohomologyOnTopLinearEquiv_apply, cohomologyOnTopLinearEquiv_apply]
    exact (cohomologyOnTopIso_hom_cohomologyOnMap M φ n
      ((cohomologyOnTopLinearEquiv M n).symm x)).symm
  have hL :
      f.higherDirectImageGlobalSectionsAddEquiv N n ((cohomologyFunctor X n).map φ x) =
        f.higherDirectImageSectionsAddEquiv N n (isAffineOpen_top Y)
          (cohomologyOnRes N n (le_of_eq f.preimage_top)
            ((cohomologyOnTopLinearEquiv N n).symm ((cohomologyFunctor X n).map φ x))) :=
    f.higherDirectImageGlobalSectionsAddEquiv_apply N n _
  rw [hL, higherDirectImageGlobalSectionsAddEquiv_apply f M n x, htop,
    ← cohomologyOnMap_cohomologyOnRes]
  exact f.higherDirectImageSectionsAddEquiv_naturality n φ (isAffineOpen_top Y) _

/-- **Global sections of a higher direct image over an affine base, linearly.** For a
quasi-compact, quasi-separated morphism `f : X ⟶ Y` to an affine scheme `Y` and a quasi-coherent
`𝒪_X`-module `M`, the cohomology `Hⁿ(X, M)` is `Γ(Y, ⊤)`-linearly equivalent to the global
sections of `Rⁿ f_* M`, where `Γ(Y, ⊤)` acts on `Hⁿ(X, M)` through `f.appTop`. -/
def higherDirectImageGlobalSectionsLinearEquiv (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    letI : Module Γ(Y, ⊤) (Cohomology M n) := Module.compHom (Cohomology M n) f.appTop.hom
    Cohomology M n ≃ₗ[Γ(Y, ⊤)] Γ((f.higherDirectImage n).obj M, ⊤) :=
  letI : Module Γ(Y, ⊤) (Cohomology M n) := Module.compHom (Cohomology M n) f.appTop.hom
  { __ := f.higherDirectImageGlobalSectionsAddEquiv M n
    map_smul' r x := f.higherDirectImageGlobalSectionsAddEquiv_smul M n r x }

/-- `higherDirectImageGlobalSectionsLinearEquiv` agrees on elements with
`higherDirectImageGlobalSectionsAddEquiv`. -/
@[simp]
lemma higherDirectImageGlobalSectionsLinearEquiv_apply (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (x : Cohomology M n) :
    (f.higherDirectImageGlobalSectionsLinearEquiv M n x :
        Γ((f.higherDirectImage n).obj M, ⊤)) =
      f.higherDirectImageGlobalSectionsAddEquiv M n x :=
  (rfl)

end AffineGlobalSections

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry.Scheme.Modules

/-- For `Spec R` viewed as a scheme over itself, `baseRingToGlobalSections` is
`(Scheme.ΓSpecIso (.of R)).inv`. -/
private lemma baseRingToGlobalSections_eq_ΓSpecIso_inv (R : Type u) [CommRing R] (r : R) :
    baseRingToGlobalSections R (Spec (.of R)) r = (Scheme.ΓSpecIso (.of R)).inv r := by
  rw [baseRingToGlobalSections_apply]
  -- `Spec (.of R) ↘ Spec (.of R)` is the identity morphism `𝟙 (Spec (.of R))`.
  change Scheme.Hom.appTop (𝟙 (Spec (.of R))) ((Scheme.ΓSpecIso (.of R)).inv r) = _
  simp

/-- The `R`-module structures on global sections of an `𝒪_{Spec R}`-module from
`globalSectionsBaseModule` and from `moduleSpecΓFunctor` coincide. -/
private def globalSectionsBaseEquivSpecΓ (R : Type u) [CommRing R]
    (N : (Spec (.of R)).Modules) :
    Γ(N, ⊤) ≃ₗ[R] moduleSpecΓFunctor.obj N where
  __ := AddEquiv.refl _
  map_smul' r y := by
    rw [base_smul_globalSections, baseRingToGlobalSections_eq_ΓSpecIso_inv]
    -- Cast `y` to the presheaf carrier `N.val.obj (.op ⊤)`, where `(Spec R).ringCatSheaf` acts
    -- directly; `modulesSpecToSheaf` twists that action by the terminal-open map `⊤ ⟶ ⊤`.
    have h := congrArg (fun g : _ →+* _ ↦ g ((Scheme.ΓSpecIso (.of R)).inv r) •
        (show N.val.obj (.op ⊤) from y))
      (show ((Spec (.of R)).ringCatSheaf.obj.map
          ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (.op ⊤))).hom =
          RingHom.id _ by
        rw [Limits.IsInitial.to_self, CategoryTheory.Functor.map_id, RingCat.hom_id])
    exact h.symm

@[simp]
private lemma globalSectionsBaseEquivSpecΓ_apply (R : Type u) [CommRing R]
    (N : (Spec (.of R)).Modules) (y : Γ(N, ⊤)) :
    (globalSectionsBaseEquivSpecΓ R N y : Γ(N, ⊤)) = y :=
  (rfl)

/-- **Cohomology as global sections of the higher direct image over `Spec R`.** For a
quasi-compact, quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`,
`Hⁿ(X, M)` is `R`-linearly equivalent to the global sections of `Rⁿ (X ↘ Spec R)_* M`. -/
def cohomologyEquivHigherDirectImageSections (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Cohomology M n ≃ₗ[R]
      moduleSpecΓFunctor.obj (((X ↘ Spec (.of R)).higherDirectImage n).obj M) :=
  let f := X ↘ Spec (.of R)
  letI : Algebra R Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom.toAlgebra
  letI : Module Γ(Spec (.of R), ⊤) (Cohomology M n) :=
    Module.compHom (Cohomology M n) f.appTop.hom
  letI : IsScalarTower R Γ(Spec (.of R), ⊤) (Cohomology M n) :=
    .of_algebraMap_smul fun r x ↦ by
      rw [RingHom.algebraMap_toAlgebra, base_smul_cohomology, baseRingToGlobalSections_apply,
        MulAction.compHom_smul_def]
      -- Both sides act via `f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv r)` on `Cohomology M n`.
      rfl
  letI : IsScalarTower R Γ(Spec (.of R), ⊤) Γ((f.higherDirectImage n).obj M, ⊤) :=
    .of_algebraMap_smul fun r y ↦ by
      rw [RingHom.algebraMap_toAlgebra, base_smul_globalSections,
        baseRingToGlobalSections_eq_ΓSpecIso_inv]
  ((f.higherDirectImageGlobalSectionsLinearEquiv M n).restrictScalars R).trans
    (globalSectionsBaseEquivSpecΓ R ((f.higherDirectImage n).obj M))

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
  simp only [cohomologyEquivHigherDirectImageSections, LinearEquiv.trans_apply,
    globalSectionsBaseEquivSpecΓ_apply, LinearEquiv.restrictScalars_apply,
    Scheme.Hom.higherDirectImageGlobalSectionsLinearEquiv_apply]
  -- `restrictScalars` does not change the underlying carrier element.
  rfl

/-- `cohomologyEquivHigherDirectImageSections` is natural in the coefficient sheaf `M`. -/
theorem cohomologyEquivHigherDirectImageSections_naturality (R : Type u) [CommRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) (n : ℕ) (x : Cohomology M n) :
    cohomologyEquivHigherDirectImageSections R N n (cohomologyMapBaseLinear R X φ n x) =
      (moduleSpecΓFunctor (R := .of R)).map (((X ↘ Spec (.of R)).higherDirectImage n).map φ)
        (cohomologyEquivHigherDirectImageSections R M n x) := by
  have h := (X ↘ Spec (.of R)).higherDirectImageGlobalSectionsAddEquiv_naturality φ n x
  rw [cohomologyEquivHigherDirectImageSections_apply,
    cohomologyEquivHigherDirectImageSections_apply, cohomologyMapBaseLinear_apply]
  exact h

/-- **Higher direct images over an affine base are associated to cohomology.** For a
quasi-compact, quasi-separated scheme `X` over `Spec R` and a quasi-coherent `𝒪_X`-module `M`,
the higher direct image `Rⁿ (X ↘ Spec R)_* M` is isomorphic as an `𝒪_{Spec R}`-module to the
quasi-coherent sheaf `Hⁿ(X, M)~`. -/
def tildeCohomologyIsoHigherDirectImage (R : Type u) [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    tilde (ModuleCat.of (CommRingCat.of R) (Cohomology M n)) ≅
      ((X ↘ Spec (.of R)).higherDirectImage n).obj M :=
  let e := asIso (((X ↘ Spec (.of R)).higherDirectImage n).obj M).fromTildeΓ
  (tilde.functor (.of R)).mapIso (cohomologyEquivHigherDirectImageSections R M n).toModuleIso ≪≫ e

/-- `tildeCohomologyIsoHigherDirectImage` is natural in the coefficient sheaf `M`. -/
@[reassoc]
theorem tildeCohomologyIsoHigherDirectImage_naturality (R : Type u) [CommRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [QuasiSeparated (X ↘ Spec (.of R))] {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) (n : ℕ) :
    (tilde.functor (.of R)).map
        (ModuleCat.ofHom (cohomologyMapBaseLinear R X φ n)) ≫
      (tildeCohomologyIsoHigherDirectImage R N n).hom =
    (tildeCohomologyIsoHigherDirectImage R M n).hom ≫
      ((X ↘ Spec (.of R)).higherDirectImage n).map φ := by
  let f := X ↘ Spec (.of R)
  have hΓ :
      ModuleCat.ofHom (cohomologyMapBaseLinear R X φ n) ≫
        (cohomologyEquivHigherDirectImageSections R N n).toModuleIso.hom =
      (cohomologyEquivHigherDirectImageSections R M n).toModuleIso.hom ≫
        (moduleSpecΓFunctor (R := .of R)).map ((f.higherDirectImage n).map φ) := by
    ext x
    exact cohomologyEquivHigherDirectImageSections_naturality R φ n x
  -- `simp`/`rw` on `Iso.trans_hom` fails at `implicit` transparency because `fromTildeΓ` is typed
  -- in `SheafOfModules (Spec (.of R)).ringCatSheaf` rather than `(Spec (.of R)).Modules`, so we
  -- assemble the square-plus-counit-naturality `calc` directly.
  have h1 :
      (tilde.functor (.of R)).map (ModuleCat.ofHom (cohomologyMapBaseLinear R X φ n)) ≫
          (tilde.functor (.of R)).map
            (cohomologyEquivHigherDirectImageSections R N n).toModuleIso.hom =
        (tilde.functor (.of R)).map
            (cohomologyEquivHigherDirectImageSections R M n).toModuleIso.hom ≫
          (tilde.functor (.of R)).map
            ((moduleSpecΓFunctor (R := .of R)).map ((f.higherDirectImage n).map φ)) := by
    rw [← Functor.map_comp, hΓ, Functor.map_comp]
  have h2 :
      (tilde.functor (.of R)).map
            ((moduleSpecΓFunctor (R := .of R)).map ((f.higherDirectImage n).map φ)) ≫
          ((f.higherDirectImage n).obj N).fromTildeΓ =
        ((f.higherDirectImage n).obj M).fromTildeΓ ≫ (f.higherDirectImage n).map φ :=
    (tilde.adjunction (R := .of R)).counit.naturality ((f.higherDirectImage n).map φ)
  calc
    (tilde.functor (.of R)).map (ModuleCat.ofHom (cohomologyMapBaseLinear R X φ n)) ≫
        ((tilde.functor (.of R)).map
            (cohomologyEquivHigherDirectImageSections R N n).toModuleIso.hom ≫
          ((f.higherDirectImage n).obj N).fromTildeΓ)
      = ((tilde.functor (.of R)).map (ModuleCat.ofHom (cohomologyMapBaseLinear R X φ n)) ≫
          (tilde.functor (.of R)).map
            (cohomologyEquivHigherDirectImageSections R N n).toModuleIso.hom) ≫
          ((f.higherDirectImage n).obj N).fromTildeΓ :=
        (Category.assoc _ _ _).symm
    _ = ((tilde.functor (.of R)).map
            (cohomologyEquivHigherDirectImageSections R M n).toModuleIso.hom ≫
          (tilde.functor (.of R)).map
            ((moduleSpecΓFunctor (R := .of R)).map ((f.higherDirectImage n).map φ))) ≫
          ((f.higherDirectImage n).obj N).fromTildeΓ :=
        congrArg (· ≫ ((f.higherDirectImage n).obj N).fromTildeΓ) h1
    _ = (tilde.functor (.of R)).map
            (cohomologyEquivHigherDirectImageSections R M n).toModuleIso.hom ≫
          (((f.higherDirectImage n).obj M).fromTildeΓ ≫ (f.higherDirectImage n).map φ) :=
        (Category.assoc _ _ _).trans (congrArg _ h2)
    _ = ((tilde.functor (.of R)).map
            (cohomologyEquivHigherDirectImageSections R M n).toModuleIso.hom ≫
          ((f.higherDirectImage n).obj M).fromTildeΓ) ≫ (f.higherDirectImage n).map φ :=
        (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.Modules
