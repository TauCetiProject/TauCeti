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
`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafSectionsLinearEquiv_naturality`).

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
  is natural in the quasi-coherent module `M`.

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
      map_smul' := fun r x ↦ ?_ }
    { toFun := e.hom.app (.op (Y.basicOpen g))
      map_add' := map_add _
      map_smul' := fun r x ↦
        f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r (Y.basicOpen g) x }
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op ⊤)))
    (ConcreteCategory.bijective_of_isIso (e.hom.app (.op (Y.basicOpen g)))) fun x ↦ ?_)
    inferInstance
  · refine (congrArg _ ?_).trans (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r ⊤ x)
    -- the inclusion of `⊤` into itself is the identity, as morphisms of a preorder are unique
    rw [show (⊤ : Y.Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  · rw [cohomologyOnResLinear_apply]
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

/-- The identification `higherDirectImageSectionsAddEquiv` of `Hⁿ(f⁻¹ V, M)` with the sections of
`Rⁿ f_* M` over an affine open `V` is linear over the global functions of `Y`, acting on
`Hⁿ(f⁻¹ V, M)` through their pullbacks along `f` and on sections through restriction to `V`. -/
lemma higherDirectImageSectionsAddEquiv_appTop_smul {V : Y.Opens} (hV : IsAffineOpen V)
    (r : Γ(Y, ⊤)) (c : cohomologyOn M n (f ⁻¹ᵁ V)) :
    f.higherDirectImageSectionsAddEquiv M n hV (f.appTop r • c) =
      Y.presheaf.map V.leTop.op r • f.higherDirectImageSectionsAddEquiv M n hV c := by
  obtain ⟨x, rfl⟩ : ∃ x : ((f.higherDirectImagePresheaf n).obj M).obj (op V),
      (f.higherDirectImagePresheafToPresheafIso M n).hom.app (op V) x = c :=
    ⟨_, Iso.inv_hom_id_apply ((f.higherDirectImagePresheafToPresheafIso M n).app _) c⟩
  refine (congrArg (f.higherDirectImageSectionsAddEquiv M n hV)
    (f.higherDirectImagePresheafToPresheafIso_hom_app_smul M n r V x).symm).trans ?_
  refine (higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
    f M n hV _).trans (((f.higherDirectImagePresheafSectionsLinearEquiv M n hV).map_smul _ x).trans
      (congrArg _ (higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
        f M n hV x).symm))

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

end AlgebraicGeometry.Scheme.Hom
