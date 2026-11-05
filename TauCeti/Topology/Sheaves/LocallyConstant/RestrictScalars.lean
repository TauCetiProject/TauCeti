/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import TauCeti.Topology.Sheaves.LocallyConstant.Basic

/-!
# Restriction of scalars for the locally constant module equivalence

A ring homomorphism `φ : R →+* S` induces a morphism `R_X ⟶ S_X` of the sheaves of locally
constant functions. The equivalence between sheaves of modules over a ring and modules over its
locally constant ring sheaf commutes with these two restrictions of scalars. The comparison is
the identity on sections, hence also on the underlying additive sheaves and on sections over
the whole space. No flatness assumption is needed for restriction of scalars.

The substantive compatibility is `TopCat.Sheaf.restrictScalars_locallyConstant_smul`: gluing the
actions of the values of an `R`-valued locally constant function after restricting scalars is
the same as acting by the corresponding `S`-valued function. The natural isomorphism
`TopCat.Sheaf.toLocallyConstantModuleRestrictScalarsIso` packages this compatibility for the
native restriction-of-scalars functors.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace TopCat

variable (X : TopCat.{u}) {R S : Type u} [Ring R] [Ring S]

namespace Sheaf

variable {X} (F : X.Sheaf (ModuleCat.{u} S)) (φ : R →+* S)

/-- After restriction of scalars, the action of a locally constant `R`-valued function is the
action of its image under `φ`. -/
@[simp]
lemma restrictScalars_locallyConstant_smul {U : Opens X} (f : LocallyConstant U R)
    (s : F.presheaf.obj (op U)) :
    @HSMul.hSMul (LocallyConstant U R)
        (((sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars φ)).obj F).obj.obj
          (op U)) _ _ f s =
      (f.map φ : LocallyConstant U S) • s := by
  symm
  refine (eq_smul_iff
    ((sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars φ)).obj F)
    f s _).mpr fun V i r hr ↦ ?_
  have h : (f.map φ).comap ⟨Set.inclusion i.le, continuous_inclusion i.le⟩ =
      LocallyConstant.const V (φ r) := by
    ext x
    exact congrArg φ (hr x)
  -- The two restrictions have identical underlying functions, while the restricted
  -- `R`-action is the `S`-action of `φ r`; using the original sheaf avoids rewriting
  -- through the different module structures carried by these wrappers.
  exact (map_smul_locallyConstant F i (f.map φ) s).trans
    ((congrArg (fun g : LocallyConstant V S ↦ g • F.presheaf.map i.op s) h).trans
      (const_smul F (φ r) _))

/-- Restricting scalars on an `S`-module sheaf and then letting locally constant functions act
agrees with restricting scalars along `R_X ⟶ S_X`. The comparison fixes every section. -/
def toLocallyConstantModuleRestrictScalarsObjIso :
    toLocallyConstantModule
      ((sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars φ)).obj F) ≅
    (SheafOfModules.restrictScalars (locallyConstantRingCatSheafMap X φ)).obj
      F.toLocallyConstantModule :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk (Iso.refl _) fun f ↦ by
      ext s
      -- The additive-group wrappers in `Iso.refl` are only definitionally equal, preventing
      -- direct rewriting with the smul bridge lemmas. Select `F`'s locally constant `S`-action
      -- explicitly to identify the restricted action as the action of the image under `φ`.
      exact (congrArg (fun g : LocallyConstant U.unop S ↦
        @SMul.smul _ _ (instSMulLocallyConstant F U.unop) g s)
        (locallyConstantRingCatSheafMap_app_apply X φ U f)).trans
        (restrictScalars_locallyConstant_smul F φ f s).symm) fun {_ _} _ ↦ rfl)

@[simp]
lemma toLocallyConstantModuleRestrictScalarsObjIso_hom_val_app_apply (U : (Opens X)ᵒᵖ)
    (s : F.presheaf.obj U) :
    dsimp% only [Functor.comp_obj]
      ((F.toLocallyConstantModuleRestrictScalarsObjIso φ).hom.val.app U s = s) :=
  (rfl)

@[simp]
lemma toLocallyConstantModuleRestrictScalarsObjIso_inv_val_app_apply (U : (Opens X)ᵒᵖ)
    (s : F.presheaf.obj U) :
    dsimp% only [Functor.comp_obj]
      ((F.toLocallyConstantModuleRestrictScalarsObjIso φ).inv.val.app U s = s) :=
  (rfl)

variable (X)

/-- The constant-ring module adapter commutes naturally with restriction of scalars. Its
components are the identity on sections over every open, including the whole space. -/
def toLocallyConstantModuleRestrictScalarsIso :
    sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars φ) ⋙
        toLocallyConstantModuleFunctor X R ≅
      toLocallyConstantModuleFunctor X S ⋙
        SheafOfModules.restrictScalars (locallyConstantRingCatSheafMap X φ) :=
  NatIso.ofComponents (fun F ↦ toLocallyConstantModuleRestrictScalarsObjIso F φ)
    fun _ ↦ by ext; rfl

@[simp]
lemma toLocallyConstantModuleRestrictScalarsIso_hom_app :
    (toLocallyConstantModuleRestrictScalarsIso X φ).hom.app F =
      (F.toLocallyConstantModuleRestrictScalarsObjIso φ).hom :=
  (rfl)

@[simp]
lemma toLocallyConstantModuleRestrictScalarsIso_inv_app :
    (toLocallyConstantModuleRestrictScalarsIso X φ).inv.app F =
      (F.toLocallyConstantModuleRestrictScalarsObjIso φ).inv :=
  (rfl)

end Sheaf

end TopCat

namespace SheafOfModules

open TopCat

variable (X : TopCat.{u}) {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)

/-- Restricting a module over `S_X` first to `R_X` and then to constant scalars agrees with
restricting first to `S` and then along `φ : R →+* S`. This is the scalar-change comparison for
the inverse of the constant-ring module equivalence. -/
def restrictToConstantsRestrictScalarsIso :
    restrictScalars (locallyConstantRingCatSheafMap X φ) ⋙ restrictToConstantsFunctor X R ≅
      restrictToConstantsFunctor X S ⋙
        sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars φ) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) fun r ↦ by
      ext m
      -- Both actions are by the constant `S`-valued function with value `φ r`.
      exact (congrArg (fun f : LocallyConstant U.unop S ↦
        @HSMul.hSMul ((locallyConstantRingCatSheaf X S).obj.obj U) (M.val.obj U) _ _ f m)
        (locallyConstantRingCatSheafMap_app_apply X φ U
          (LocallyConstant.const U.unop r))).symm) fun _ ↦ rfl)) fun _ ↦ by ext; rfl

/-- The comparison for restriction to constants fixes each section. -/
@[simp]
lemma restrictToConstantsRestrictScalarsIso_hom_app_hom_app_apply
    (M : SheafOfModules.{u} (locallyConstantRingCatSheaf X S)) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) :
    dsimp% only [Functor.comp_obj]
      (((restrictToConstantsRestrictScalarsIso X φ).hom.app M).hom.app U m = m) :=
  (rfl)

/-- The reverse comparison for restriction to constants fixes each section. -/
@[simp]
lemma restrictToConstantsRestrictScalarsIso_inv_app_hom_app_apply
    (M : SheafOfModules.{u} (locallyConstantRingCatSheaf X S)) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) :
    dsimp% only [Functor.comp_obj]
      (((restrictToConstantsRestrictScalarsIso X φ).inv.app M).hom.app U m = m) :=
  (rfl)

end SheafOfModules
