/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Colimits of quasicoherent sheaves

The colimit, in the category of all sheaves of modules on a scheme, of a small diagram of
quasicoherent sheaves is quasicoherent. On a spectrum it is the sheaf associated with the colimit
of the modules of global sections, since the associated-sheaf functor `M ↦ M~` is a left adjoint
and a quasicoherent sheaf is the sheaf associated with its global sections. Restriction to an
open subscheme is also a left adjoint, so restriction to affine opens gives the result on
arbitrary schemes, without Noetherian or separation assumptions.

In particular direct sums of quasicoherent sheaves are quasicoherent, such as the direct sum of
the homogeneous components of a graded quasicoherent algebra.

Taking sections over an affine open preserves these colimits: on `Spec R`, global sections
restrict to an equivalence between quasicoherent sheaves and `R`-modules (`tildeEquiv`), and an
affine open is the image of the affine chart `Spec Γ(X, U) ⟶ X`. So the sections over an affine
open of a direct sum of quasicoherent sheaves are the direct sum of their sections. This fails
over non-quasicompact opens, where a section of a direct sum may have infinitely many nonzero
components.

## Main declarations

* `TauCeti.AlgebraicGeometry.isQuasicoherent_of_isColimit`: a small colimit of quasicoherent
  sheaves is quasicoherent;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderColimitsOfShape`: quasicoherence
  is closed under small colimits;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.hasBinaryBiproducts`: quasicoherent sheaves have
  binary biproducts;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma`: a small coproduct of quasicoherent
  sheaves is quasicoherent;
* `AlgebraicGeometry.IsAffineOpen.restrictFromSpecCompModuleSpecΓFunctorIso`: over an affine
  open, sections are naturally global sections on the affine chart;
* `TauCeti.AlgebraicGeometry.isColimitMapCoconeSectionsFunctor`,
  `TauCeti.AlgebraicGeometry.preservesColimit_sectionsFunctor`, and
  `TauCeti.AlgebraicGeometry.preservesColimit_parallelPair_zero_sectionsFunctor`: sections over an
  affine open preserve small colimits, and in particular cokernels, of quasicoherent sheaves;
* `TauCeti.AlgebraicGeometry.cokernelSectionsEquiv`: sections of `cokernel φ` over an affine open
  are the quotient of the target sections by the range of `φ`;
* `TauCeti.AlgebraicGeometry.toModule_sectionsFunctor_map_bijective`: the sections over an affine
  open of a coproduct of quasicoherent sheaves are the direct sum of their sections.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (`M ↦ M~` commutes with direct sums)
  and Proposition II.5.7; Corollary II.5.5 (global sections on `Spec R` give an equivalence of
  quasicoherent sheaves with `R`-modules).
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe w w' u

noncomputable section

variable {J : Type w} [Category.{w'} J] [EssentiallySmall.{u} J]

/-- On a spectrum, a small colimit of quasicoherent sheaves is quasicoherent: it is the sheaf
associated with the colimit of their modules of global sections. -/
private theorem isQuasicoherent_of_isColimit_spec {R : CommRingCat.{u}}
    {K : J ⥤ (Spec R).Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent)
    {c : Cocone K} (hc : IsColimit c) : c.pt.IsQuasicoherent := by
  have := hasColimitsOfShape_of_essentiallySmall.{u} J (ModuleCat.{u} R)
  -- Each `K.obj j` is the sheaf associated with its global sections, and `M ↦ M~` preserves
  -- colimits, so `c.pt` is the sheaf associated with the colimit of the global sections.
  have (j : J) :
      IsIso ((Functor.whiskerLeft K (tilde.adjunction (R := R)).counit).app j) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (K.obj j)).1 (hK j)
  have : IsIso (Functor.whiskerLeft K (tilde.adjunction (R := R)).counit) :=
    NatIso.isIso_of_isIso_app _
  let e : K ⋙ moduleSpecΓFunctor ⋙ tilde.functor R ≅ K :=
    asIso (Functor.whiskerLeft K (tilde.adjunction (R := R)).counit)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves (tilde.functor R)
      (colimit.isColimit (K ⋙ moduleSpecΓFunctor))) hc e)
    (inferInstanceAs ((tilde.functor R).obj (colimit (K ⋙ moduleSpecΓFunctor))).IsQuasicoherent)

private theorem isQuasicoherent_of_isColimit_affine {X : Scheme.{u}} [IsAffine X]
    {K : J ⥤ X.Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent)
    {c : Cocone K} (hc : IsColimit c) : c.pt.IsQuasicoherent := by
  have : ((restrictFunctor X.isoSpec.inv).obj c.pt).IsQuasicoherent :=
    isQuasicoherent_of_isColimit_spec (K := K ⋙ restrictFunctor X.isoSpec.inv)
      (fun j ↦ have := hK j; isQuasicoherent_restrictFunctor _ _)
      (isColimitOfPreserves (restrictFunctor X.isoSpec.inv) hc)
  exact (c.pt.isQuasicoherent_restrict_iff_of_isIso X.isoSpec.inv).1 this

/-- On any scheme, the colimit, in the category of all sheaves of modules, of a small diagram of
quasicoherent sheaves is quasicoherent. -/
theorem isQuasicoherent_of_isColimit {X : Scheme.{u}} {K : J ⥤ X.Modules}
    (hK : ∀ j, (K.obj j).IsQuasicoherent) {c : Cocone K} (hc : IsColimit c) :
    c.pt.IsQuasicoherent := by
  -- Restriction to an open subscheme is a left adjoint, so it preserves the colimit.
  refine c.pt.isQuasicoherent_iff_forall_affineOpens.2 fun U ↦ ?_
  exact isQuasicoherent_of_isColimit_affine (K := K ⋙ restrictFunctor U.val.ι)
    (fun j ↦ have := hK j; isQuasicoherent_restrictFunctor _ _)
    (isColimitOfPreserves (restrictFunctor U.val.ι) hc)

variable (J) in
/-- Quasicoherence is closed under small colimits in the category of all sheaves of modules, so
the generic full-subcategory construction supplies these colimits in `QuasicoherentSheaf X`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderColimitsOfShape
    (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le _ := fun ⟨h⟩ ↦ isQuasicoherent_of_isColimit h.prop_diag_obj h.isColimit

/-- Quasicoherent sheaves are closed under binary coproducts in `X.Modules`, so the preadditive
category `QuasicoherentSheaf X` has binary biproducts. -/
instance QuasicoherentSheaf.hasBinaryBiproducts (X : Scheme.{u}) :
    HasBinaryBiproducts (QuasicoherentSheaf X) :=
  have : HasBinaryCoproducts (QuasicoherentSheaf X) :=
    hasColimitsOfShape_of_closedUnderColimits _ _
  HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The coproduct of a small family of quasicoherent sheaves on any scheme is quasicoherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma {X : Scheme.{u}}
    {ι : Type w} [Small.{u} ι] (M : ι → X.Modules) [HasCoproduct M]
    [∀ i, (M i).IsQuasicoherent] : (∐ M).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (fun i ↦ inferInstanceAs (M i.as).IsQuasicoherent)
    (colimit.isColimit _)

/-- On a spectrum, global sections send a colimit of a small diagram of quasicoherent sheaves to a
colimit of modules: the colimit is quasicoherent, so the colimit cocone lies in the full
subcategory of quasicoherent sheaves, where global sections are an equivalence. -/
private def isColimitMapCoconeModuleSpecΓFunctor {R : CommRingCat.{u}}
    {K : J ⥤ (Spec R).Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent)
    {c : Cocone K} (hc : IsColimit c) :
    IsColimit ((moduleSpecΓFunctor (R := R)).mapCocone c) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let c' : Cocone (P.lift K hK) :=
    { pt := ⟨c.pt, isQuasicoherent_of_isColimit hK hc⟩
      ι := { app j := ObjectProperty.homMk (c.ι.app j)
             naturality i j f := by ext1; exact (c.w f).trans (Category.comp_id _).symm } }
  have hc' : IsColimit c' :=
    isColimitOfReflects P.ι (IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _)))
  -- The inverse of `tildeEquiv` is the inclusion followed by global sections, so its image of
  -- `c'` is the image of `c` under global sections.
  exact isColimitOfPreserves (tildeEquiv (R := R)).inverse hc'

variable {X : Scheme.{u}} {U : X.Opens}

/-- Over an affine open `U`, the sections functor is global sections on the affine chart
`Spec Γ(X, U) ⟶ X`, naturally in the module: the components are `fromSpecSectionsEquiv`. -/
def _root_.AlgebraicGeometry.IsAffineOpen.restrictFromSpecCompModuleSpecΓFunctorIso
    (hU : IsAffineOpen U) :
    restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor ≅ sectionsFunctor U :=
  NatIso.ofComponents (fun M ↦ (M.fromSpecSectionsEquiv hU).toModuleIso.symm) fun {M N} f ↦ by
    ext x
    -- Display the components on sections: the two functors present the same modules with their
    -- scalar rings written differently, so `simp` lemmas for module morphisms do not apply.
    change (N.fromSpecSectionsEquiv hU).symm (((restrictFunctor hU.fromSpec).map f).app ⊤ x) =
      f.app U ((M.fromSpecSectionsEquiv hU).symm x)
    rw [LinearEquiv.symm_apply_eq, ← Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality]
    exact congrArg _ ((M.fromSpecSectionsEquiv hU).apply_symm_apply x).symm

/-- The components of `restrictFromSpecCompModuleSpecΓFunctorIso` are the inverses of
`fromSpecSectionsEquiv`. -/
@[simp]
theorem _root_.AlgebraicGeometry.IsAffineOpen.restrictFromSpecCompModuleSpecΓFunctorIso_hom_app
    (hU : IsAffineOpen U) (M : X.Modules) :
    hU.restrictFromSpecCompModuleSpecΓFunctorIso.hom.app M =
      ModuleCat.ofHom (M.fromSpecSectionsEquiv hU).symm.toLinearMap :=
  NatIso.ofComponents_hom_app _ _ M

/-- The components of the inverse of `restrictFromSpecCompModuleSpecΓFunctorIso` are
`fromSpecSectionsEquiv`. -/
@[simp]
theorem _root_.AlgebraicGeometry.IsAffineOpen.restrictFromSpecCompModuleSpecΓFunctorIso_inv_app
    (hU : IsAffineOpen U) (M : X.Modules) :
    hU.restrictFromSpecCompModuleSpecΓFunctorIso.inv.app M =
      ModuleCat.ofHom (M.fromSpecSectionsEquiv hU).toLinearMap :=
  NatIso.ofComponents_inv_app _ _ M

/-- Sections over an affine open send a colimit, in the category of all sheaves of modules, of a
small diagram of quasicoherent sheaves to a colimit of `Γ(X, U)`-modules. -/
def isColimitMapCoconeSectionsFunctor {K : J ⥤ X.Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent)
    {c : Cocone K} (hc : IsColimit c) (hU : IsAffineOpen U) :
    IsColimit ((sectionsFunctor U).mapCocone c) :=
  have := hU.isOpenImmersion_fromSpec
  IsColimit.mapCoconeEquiv hU.restrictFromSpecCompModuleSpecΓFunctorIso
    (isColimitMapCoconeModuleSpecΓFunctor (K := K ⋙ restrictFunctor hU.fromSpec)
      (fun j ↦ have := hK j; isQuasicoherent_restrictFunctor _ _)
      (isColimitOfPreserves (restrictFunctor hU.fromSpec) hc))

/-- Sections over an affine open `U` preserve the colimit of any small diagram of quasicoherent
`𝒪_X`-modules. -/
theorem preservesColimit_sectionsFunctor {K : J ⥤ X.Modules}
    (hK : ∀ j, (K.obj j).IsQuasicoherent) (hU : IsAffineOpen U) :
    PreservesColimit K (sectionsFunctor U) :=
  ⟨fun hc ↦ ⟨isColimitMapCoconeSectionsFunctor hK hc hU⟩⟩

/-- Sections over an affine open `U` preserve the cokernel of a morphism of quasicoherent
`𝒪_X`-modules. -/
theorem preservesColimit_parallelPair_zero_sectionsFunctor {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (hU : IsAffineOpen U) :
    PreservesColimit (parallelPair φ 0) (sectionsFunctor U) :=
  preservesColimit_sectionsFunctor (K := parallelPair φ 0)
    (by rintro (_ | _) <;> dsimp <;> infer_instance) hU

/-- Over an affine open `U`, the sections of the cokernel of a morphism `φ : M ⟶ N` of
quasicoherent `𝒪_X`-modules identify with
`Γ(N, U) ⧸ LinearMap.range (ModuleCat.Hom.hom (R := Γ(X, U)) (φ.val.app (Opposite.op U)))`. -/
def cokernelSectionsEquiv {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) (U : X.affineOpens) :
    (Γ(N, U.val) ⧸ LinearMap.range
        (ModuleCat.Hom.hom (R := Γ(X, U.val)) (φ.val.app (Opposite.op U.val)))) ≃ₗ[Γ(X, U)]
      Γ(cokernel φ, U.val) := by
  haveI := preservesColimit_parallelPair_zero_sectionsFunctor φ U.property
  exact (PreservesCokernel.iso (sectionsFunctor U.val) φ ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((sectionsFunctor U.val).map φ)).symm.toLinearEquiv

/-- `cokernelSectionsEquiv` sends the quotient class of a section `s ∈ Γ(N, U)` to its image under
the cokernel projection `(cokernel.π φ).app U`. -/
@[simp]
theorem cokernelSectionsEquiv_mk {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) (U : X.affineOpens) (s : Γ(N, U.val)) :
    cokernelSectionsEquiv φ U (Submodule.Quotient.mk s) = (cokernel.π φ).app U.val s := by
  have := preservesColimit_parallelPair_zero_sectionsFunctor φ U.property
  let F := sectionsFunctor U.val
  let e := PreservesCokernel.iso F φ ≪≫ ModuleCat.cokernelIsoRangeQuotient (F.map φ)
  have hπ : ModuleCat.ofHom (LinearMap.range (F.map φ).hom).mkQ ≫ e.inv = F.map (cokernel.π φ) := by
    rw [Iso.comp_inv_eq]
    exact ((PreservesCokernel.π_iso_hom_assoc F φ _).trans
      (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (F.map φ))).symm
  exact congrArg (fun ψ : F.obj N ⟶ F.obj (cokernel φ) ↦ ψ s) hπ

/-- The inverse of `cokernelSectionsEquiv` sends the image of `s ∈ Γ(N, U)` under `cokernel.π φ`
to its quotient class modulo the range of `φ` on `U`. -/
@[simp]
theorem cokernelSectionsEquiv_symm_π {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) (U : X.affineOpens) (s : Γ(N, U.val)) :
    (cokernelSectionsEquiv φ U).symm ((cokernel.π φ).app U.val s) = Submodule.Quotient.mk s :=
  (LinearEquiv.symm_apply_eq _).mpr (cokernelSectionsEquiv_mk φ U s).symm

/-- If `P` is the coproduct of a family of quasicoherent sheaves `Mᵢ`, with coprojections `gᵢ`,
then over an affine open `U` the induced map `⨁ᵢ Γ(Mᵢ, U) → Γ(P, U)` is bijective. The scheme
lives in a universe at least that of the index type, so that the direct sum is a module in the
universe of the sections. -/
theorem toModule_sectionsFunctor_map_bijective {ι : Type w} [DecidableEq ι]
    {X : Scheme.{max w u}} {U : X.Opens} {M : ι → X.Modules} [∀ i, (M i).IsQuasicoherent]
    {P : X.Modules} {g : ∀ i, M i ⟶ P} (hc : IsColimit (Cofan.mk P g)) (hU : IsAffineOpen U) :
    Function.Bijective (DirectSum.toModule Γ(X, U) ι ((sectionsFunctor U).obj P)
      fun i ↦ ((sectionsFunctor U).map (g i)).hom) := by
  let F := sectionsFunctor U
  let φ := DirectSum.toModule Γ(X, U) ι (F.obj P) fun i ↦ (F.map (g i)).hom
  have hF := isColimitMapCoconeCofanMkEquiv F M g
    (isColimitMapCoconeSectionsFunctor (fun i ↦ inferInstanceAs (M i.as).IsQuasicoherent) hc hU)
  -- `φ` is the comparison map from the concrete direct sum to the colimit `F.obj P`.
  let e := (ModuleCat.coproductCoconeIsColimit fun i ↦ F.obj (M i)).coconePointUniqueUpToIso hF
  have he : e.hom = ModuleCat.ofHom φ :=
    Cofan.IsColimit.hom_ext (ModuleCat.coproductCoconeIsColimit fun i ↦ F.obj (M i)) _ _ fun i ↦
      ((ModuleCat.coproductCoconeIsColimit _).comp_coconePointUniqueUpToIso_hom hF ⟨i⟩).trans
        (ModuleCat.hom_ext (LinearMap.ext fun x ↦ by simp [φ, ModuleCat.coproductCocone])).symm
  have : IsIso (ModuleCat.ofHom φ) := he ▸ e.isIso_hom
  exact ConcreteCategory.bijective_of_isIso (ModuleCat.ofHom φ)

end

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry

universe w w' u

variable {J : Type w} [Category.{w'} J] [EssentiallySmall.{u} J] {X : Scheme.{u}} {U : X.Opens}

/-- Sections over an affine open preserve the colimit of any small diagram of quasicoherent
sheaves. -/
theorem preservesColimit_sectionsFunctor_of_isAffineOpen
    {K : J ⥤ X.Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent) (hU : IsAffineOpen U) :
    PreservesColimit K (sectionsFunctor U) :=
  ⟨fun hc ↦ ⟨isColimitMapCoconeSectionsFunctor hK hc hU⟩⟩

/-- Sections over an affine open preserve the colimit of any parallel pair of morphisms between
quasicoherent sheaves (in particular coequalizers and cokernels). -/
theorem preservesColimit_parallelPair_sectionsFunctor_of_isAffineOpen
    {M N : X.Modules} (f g : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : PreservesColimit (parallelPair f g) (sectionsFunctor U) :=
  preservesColimit_sectionsFunctor_of_isAffineOpen
    (by rintro (_ | _) <;> dsimp <;> infer_instance) hU

end AlgebraicGeometry.Scheme.Modules
