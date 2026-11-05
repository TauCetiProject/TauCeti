/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocallyConstant.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Functors

/-!
# Open restriction of the constant-ring module equivalence

Restriction to an open subspace commutes with the equivalence between sheaves of
`R`-modules and modules over the sheaf of locally constant `R`-valued functions.
The ring comparison transports functions along the homeomorphism from an open
to its image under the open embedding. Both module comparisons are the identity
on sections, and are natural in the coefficient sheaf.

We use Mathlib's `Topology.IsOpenEmbedding.sheafPullback` for ordinary sheaves and
`SheafOfModules.pushforward` for ring-sheaf modules. The latter is precomposition
by the image functor on opens, with scalars transported by the ring comparison.
The scalar-action characterization is that of `TopCat.Sheaf.eq_smul_iff`.

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.30 (tag 0FKR),
  for the equivalence between module sheaves and constant-ring-sheaf modules.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)
  (R : Type u) [Ring R]

attribute [local instance] functor_isContinuous

/-- Restricting the locally constant ring sheaf to an open subspace gives the
locally constant ring sheaf of that subspace. The forward map pulls functions
back along the open embedding. -/
def locallyConstantRingCatSheafIso :
    (hf.sheafPullback RingCat).obj (TopCat.locallyConstantRingCatSheaf X R) ≅
      TopCat.locallyConstantRingCatSheaf Y R :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
    let e := hf.isEmbedding.homeomorphImage (U.unop : Set Y)
    RingEquiv.toRingCatIso
      { toFun := LocallyConstant.comap ⟨e, e.continuous⟩
        invFun := LocallyConstant.comap ⟨e.symm, e.symm.continuous⟩
        left_inv := fun a ↦ LocallyConstant.ext fun x ↦ congrArg a (e.apply_symm_apply x)
        right_inv := fun a ↦ LocallyConstant.ext fun x ↦ congrArg a (e.symm_apply_apply x)
        map_mul' := fun _ _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }) (fun i ↦ by
          ext a
          exact LocallyConstant.ext fun x ↦ rfl))

/-- The ring comparison is pullback of locally constant functions. The type
ascription identifies the ring sheaf's sections with locally constant functions. -/
@[simp]
theorem locallyConstantRingCatSheafIso_hom_app_apply (U : Opens Y)
    (a : LocallyConstant (hf.functor.obj U) R) (y : U) :
    (show LocallyConstant U R from
      (hf.locallyConstantRingCatSheafIso R).hom.hom.app (op U) a) y =
      a ⟨f y, ⟨y, y.2, rfl⟩⟩ :=
  (rfl)

/-- The inverse ring comparison extends a locally constant function to its image.
The type ascription identifies the restricted ring sheaf's sections with functions. -/
@[simp]
theorem locallyConstantRingCatSheafIso_inv_app_apply (U : Opens Y)
    (a : LocallyConstant U R) (y : U) :
    (show LocallyConstant (hf.functor.obj U) R from
      (hf.locallyConstantRingCatSheafIso R).inv.hom.app (op U) a)
      ⟨f y, ⟨y, y.2, rfl⟩⟩ = a y := by
  let e := hf.isEmbedding.homeomorphImage (U : Set Y)
  exact congrArg a (e.symm_apply_apply y)

/-- Restriction of modules over the locally constant ring sheaf along an open
embedding, with the restricted ring identified with the subspace's ring sheaf. -/
abbrev locallyConstantModuleRestriction :
    SheafOfModules.{u} (TopCat.locallyConstantRingCatSheaf X R) ⥤
      SheafOfModules.{u} (TopCat.locallyConstantRingCatSheaf Y R) :=
  SheafOfModules.pushforward (F := hf.functor) (hf.locallyConstantRingCatSheafIso R).inv

end Topology.IsOpenEmbedding

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} {f : Y ⟶ X} {R : Type u} [Ring R]
  (F : X.Sheaf (ModuleCat.{u} R))
  (hf : Topology.IsOpenEmbedding f)

/-- Passing from `R`-module sheaves to modules over the locally constant ring
commutes with open restriction. The comparison is the identity on sections. -/
def toLocallyConstantModuleRestrictionIso :
    (toLocallyConstantModuleFunctor Y R).obj ((hf.sheafPullback (ModuleCat R)).obj F) ≅
      (hf.locallyConstantModuleRestriction R).obj ((toLocallyConstantModuleFunctor X R).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk (Iso.refl _) fun a ↦ by
          ext s
          -- Explicit scalar structures distinguish the two actions on the same
          -- section group; typeclass inference otherwise picks the restricted one.
          change @SMul.smul (LocallyConstant (hf.functor.obj U.unop) R)
            (F.presheaf.obj (op (hf.functor.obj U.unop))) (instSMulLocallyConstant F _)
              ((hf.locallyConstantRingCatSheafIso R).inv.hom.app U a) s =
            @SMul.smul (LocallyConstant U.unop R)
              (((hf.sheafPullback (ModuleCat R)).obj F).presheaf.obj U)
              (instSMulLocallyConstant _ _) a s
          refine (eq_smul_iff ((hf.sheafPullback (ModuleCat R)).obj F) a s _).2
            fun V i r hr ↦ ?_
          erw [map_smul_locallyConstant F (hf.functor.map i)]
          erw [← const_smul F r]
          congr 1
          refine LocallyConstant.ext fun x ↦ ?_
          rcases x with ⟨x, hx⟩
          obtain ⟨y, hy, rfl⟩ := hx
          exact (hf.locallyConstantRingCatSheafIso_inv_app_apply R U.unop a
            ⟨y, i.le hy⟩).trans (hr ⟨y, hy⟩)) fun _ _ _ ↦ rfl)

@[simp]
theorem toLocallyConstantModuleRestrictionIso_hom_val_app_apply (U : (Opens Y)ᵒᵖ)
    (s : ((toLocallyConstantModuleFunctor Y R).obj
      ((hf.sheafPullback (ModuleCat R)).obj F)).val.obj U) :
    (F.toLocallyConstantModuleRestrictionIso hf).hom.val.app U s = s :=
  (rfl)

@[simp]
theorem toLocallyConstantModuleRestrictionIso_inv_val_app_apply (U : (Opens Y)ᵒᵖ)
    (s : ((hf.locallyConstantModuleRestriction R).obj
      ((toLocallyConstantModuleFunctor X R).obj F)).val.obj U) :
    (F.toLocallyConstantModuleRestrictionIso hf).inv.val.app U s = s :=
  (rfl)

end TopCat.Sheaf

namespace SheafOfModules

variable {X Y : TopCat.{u}} {f : Y ⟶ X} {R : Type u} [Ring R]
  (M : SheafOfModules.{u} (TopCat.locallyConstantRingCatSheaf X R))
  (hf : Topology.IsOpenEmbedding f)

/-- Restricting the locally constant scalar action to constant scalars commutes
with open restriction. The comparison is the identity on sections. -/
def restrictToConstantsRestrictionIso :
    (restrictToConstantsFunctor Y R).obj ((hf.locallyConstantModuleRestriction R).obj M) ≅
      (hf.sheafPullback (ModuleCat R)).obj ((restrictToConstantsFunctor X R).obj M) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
    ModuleCat.isoMk (Iso.refl _) fun r ↦ by
      ext s
      rfl) (fun _ ↦ rfl))

@[simp]
theorem restrictToConstantsRestrictionIso_hom_hom_app_apply (U : (Opens Y)ᵒᵖ)
    (s : ((restrictToConstantsFunctor Y R).obj
      ((hf.locallyConstantModuleRestriction R).obj M)).presheaf.obj U) :
    (M.restrictToConstantsRestrictionIso hf).hom.hom.app U s = s :=
  (rfl)

@[simp]
theorem restrictToConstantsRestrictionIso_inv_hom_app_apply (U : (Opens Y)ᵒᵖ)
    (s : ((hf.sheafPullback (ModuleCat R)).obj
      ((restrictToConstantsFunctor X R).obj M)).presheaf.obj U) :
    (M.restrictToConstantsRestrictionIso hf).inv.hom.app U s = s :=
  (rfl)

end SheafOfModules

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)
  (R : Type u) [Ring R]

/-- The constant-ring module adapter commutes naturally with open restriction. -/
def toLocallyConstantModuleRestrictionNatIso :
    hf.sheafPullback (ModuleCat R) ⋙ TopCat.Sheaf.toLocallyConstantModuleFunctor Y R ≅
      TopCat.Sheaf.toLocallyConstantModuleFunctor X R ⋙ hf.locallyConstantModuleRestriction R :=
  NatIso.ofComponents (fun F ↦ F.toLocallyConstantModuleRestrictionIso hf) fun α ↦ by
    ext U s
    rfl

@[simp]
theorem toLocallyConstantModuleRestrictionNatIso_hom_app (F : X.Sheaf (ModuleCat.{u} R)) :
    (hf.toLocallyConstantModuleRestrictionNatIso R).hom.app F =
      (F.toLocallyConstantModuleRestrictionIso hf).hom :=
  (rfl)

@[simp]
theorem toLocallyConstantModuleRestrictionNatIso_inv_app (F : X.Sheaf (ModuleCat.{u} R)) :
    (hf.toLocallyConstantModuleRestrictionNatIso R).inv.app F =
      (F.toLocallyConstantModuleRestrictionIso hf).inv :=
  (rfl)

/-- Restriction to constant scalars commutes naturally with open restriction. -/
def restrictToConstantsRestrictionNatIso :
    hf.locallyConstantModuleRestriction R ⋙ SheafOfModules.restrictToConstantsFunctor Y R ≅
      SheafOfModules.restrictToConstantsFunctor X R ⋙ hf.sheafPullback (ModuleCat R) :=
  NatIso.ofComponents (fun M ↦ M.restrictToConstantsRestrictionIso hf) fun α ↦ by
    ext U s
    rfl

@[simp]
theorem restrictToConstantsRestrictionNatIso_hom_app
    (M : SheafOfModules.{u} (TopCat.locallyConstantRingCatSheaf X R)) :
    (hf.restrictToConstantsRestrictionNatIso R).hom.app M =
      (M.restrictToConstantsRestrictionIso hf).hom :=
  (rfl)

@[simp]
theorem restrictToConstantsRestrictionNatIso_inv_app
    (M : SheafOfModules.{u} (TopCat.locallyConstantRingCatSheaf X R)) :
    (hf.restrictToConstantsRestrictionNatIso R).inv.app M =
      (M.restrictToConstantsRestrictionIso hf).inv :=
  (rfl)

/-- The unit of the constant-ring module equivalence is compatible with open
restriction and the two adapter comparisons. -/
@[reassoc]
theorem sheafModuleCatEquivLocallyConstant_unit_restriction
    (F : X.Sheaf (ModuleCat.{u} R)) :
    ((TopCat.sheafModuleCatEquivLocallyConstant Y R).unitIso.app
        ((hf.sheafPullback (ModuleCat R)).obj F)).hom ≫
      (SheafOfModules.restrictToConstantsFunctor Y R).map
        (F.toLocallyConstantModuleRestrictionIso hf).hom ≫
      (F.toLocallyConstantModule.restrictToConstantsRestrictionIso hf).hom =
    (hf.sheafPullback (ModuleCat R)).map
      ((TopCat.sheafModuleCatEquivLocallyConstant X R).unitIso.app F).hom := by
  ext U s
  rfl

/-- The counit of the constant-ring module equivalence is compatible with open
restriction and the two adapter comparisons. -/
@[reassoc]
theorem sheafModuleCatEquivLocallyConstant_counit_restriction
    (M : SheafOfModules.{u} (TopCat.locallyConstantRingCatSheaf X R)) :
    (TopCat.Sheaf.toLocallyConstantModuleFunctor Y R).map
        (M.restrictToConstantsRestrictionIso hf).hom ≫
      (M.restrictToConstants.toLocallyConstantModuleRestrictionIso hf).hom ≫
      (hf.locallyConstantModuleRestriction R).map
        ((TopCat.sheafModuleCatEquivLocallyConstant X R).counitIso.app M).hom =
    ((TopCat.sheafModuleCatEquivLocallyConstant Y R).counitIso.app
      ((hf.locallyConstantModuleRestriction R).obj M)).hom := by
  ext U s
  rfl

end Topology.IsOpenEmbedding
