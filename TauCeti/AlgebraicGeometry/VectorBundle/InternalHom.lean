/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.InternalHom.Quasicoherent
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Internal Hom from a finite locally free sheaf in quasicoherent sheaves

For a finite locally free sheaf `E` on a scheme `X`, the ordinary sheaf internal Hom
`𝓗om(E, -)` preserves quasicoherence and is right adjoint to tensoring with `E` inside
`QuasicoherentSheaf X`. It is naturally isomorphic to tensoring with the internal-Hom dual
`𝓗om(E, 𝒪_X)`. Evaluation and coevaluation are those of the ambient tensor--Hom adjunction;
the target sheaf is arbitrary quasicoherent, without a finiteness hypothesis.

The adjunction is restricted using Mathlib's `Adjunction.restrictFullyFaithful`. The dual-tensor
isomorphism lifts `TauCeti.dualTensorIhom`, retaining its canonical evaluation equation.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X)

/-- Internal Hom from `E`, restricted to quasicoherent target sheaves. -/
def internalHom : QuasicoherentSheaf X ⥤ QuasicoherentSheaf X :=
  (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
    ((ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙ ihom (C := X.Modules) E.obj)
    fun F ↦ by
      have : F.obj.IsQuasicoherent := F.property
      exact _root_.SheafOfModules.isQuasicoherent_ihom_of_isLocallyFree
        (R := X.sheaf) E.obj F.obj

/-- The underlying sheaf of the quasicoherent internal Hom is the ordinary sheaf internal Hom. -/
@[simp]
theorem internalHom_obj_obj (F : QuasicoherentSheaf X) :
    ((internalHom E).obj F).obj = (ihom (C := X.Modules) E.obj).obj F.obj :=
  (rfl)

/-- The internal-Hom functor acts by the ordinary sheaf internal-Hom map. -/
@[simp]
theorem internalHom_map_hom {F G : QuasicoherentSheaf X} (f : F ⟶ G) :
    ((internalHom E).map f).hom =
      eqToHom (internalHom_obj_obj E F) ≫ (ihom (C := X.Modules) E.obj).map f.hom ≫
        eqToHom (internalHom_obj_obj E G).symm := by
  cases internalHom_obj_obj E F
  cases internalHom_obj_obj E G
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Tensoring with `E` is left adjoint to the ordinary internal Hom from `E`, within
quasicoherent sheaves. -/
def tensorInternalHomAdjunction :
    tensorLeft ((toQuasicoherent X).obj E) ⊣ internalHom E :=
  (ihom.adjunction E.obj).restrictFullyFaithful
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- Evaluation of the restricted tensor--Hom adjunction is ordinary internal-Hom evaluation. -/
@[simp]
theorem tensorInternalHomAdjunction_counit_app_hom (F : QuasicoherentSheaf X) :
    ((tensorInternalHomAdjunction E).counit.app F).hom =
      E.obj ◁ eqToHom (internalHom_obj_obj E F) ≫ (ihom.ev E.obj).app F.obj := by
  cases internalHom_obj_obj E F
  have h := (ihom.adjunction E.obj).map_restrictFullyFaithful_counit_app
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (L := tensorLeft ((toQuasicoherent X).obj E)) (R := internalHom E)
    (Iso.refl _) (Iso.refl _) F
  dsimp only [Iso.refl_inv, NatTrans.id_app] at h
  exact h.trans (Category.id_comp _)

/-- Coevaluation of the restricted adjunction is ordinary tensor--Hom coevaluation. -/
@[simp]
theorem tensorInternalHomAdjunction_unit_app_hom (F : QuasicoherentSheaf X) :
    ((tensorInternalHomAdjunction E).unit.app F).hom =
      (ihom.coev E.obj).app F.obj ≫
        eqToHom (internalHom_obj_obj E (((toQuasicoherent X).obj E) ⊗ F)).symm := by
  cases internalHom_obj_obj E (((toQuasicoherent X).obj E) ⊗ F)
  have h := (ihom.adjunction E.obj).map_restrictFullyFaithful_unit_app
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (L := tensorLeft ((toQuasicoherent X).obj E)) (R := internalHom E)
    (Iso.refl _) (Iso.refl _) F
  dsimp only [Iso.refl_hom, NatTrans.id_app] at h
  exact h.trans (congrArg (_ ≫ ·)
    ((congrArg (· ≫ 𝟙 _) ((ihom (C := X.Modules) E.obj).map_id _)).trans
      (Category.id_comp _)))

-- The sheaf-level instance is stated on `X.Modules`, whose definition instance search
-- does not unfold when inferring invertibility of a component at an underlying sheaf.
local instance : IsIso (dualTensorIhom (C := X.Modules) E.obj) :=
  Scheme.Modules.isIso_dualTensorIhom_of_isLocallyFree E.obj

/-- Tensoring with the internal-Hom dual of `E` is naturally isomorphic to internal Hom
from `E`, on arbitrary quasicoherent target sheaves. -/
def dualTensorInternalHomIso :
    tensorLeft ((toQuasicoherent X).obj (dual E)) ≅ internalHom E :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _
      ((asIso (dualTensorIhom (C := X.Modules) E.obj)).app F.obj ≪≫
        eqToIso (internalHom_obj_obj E F).symm))
    (fun {F G} f ↦ by
      apply ObjectProperty.hom_ext
      cases internalHom_obj_obj E F
      cases internalHom_obj_obj E G
      exact ((dualTensorIhom (C := X.Modules) E.obj).naturality f.hom))

/-- The dual-tensor isomorphism is the canonical comparison on underlying sheaves. -/
@[simp]
theorem dualTensorInternalHomIso_hom_app_hom (F : QuasicoherentSheaf X) :
    ((dualTensorInternalHomIso E).hom.app F).hom =
      (dualTensorIhom (C := X.Modules) E.obj).app F.obj ≫
        eqToHom (internalHom_obj_obj E F).symm :=
  (rfl)

/-- The inverse dual-tensor isomorphism inverts the canonical comparison. -/
@[simp]
theorem dualTensorInternalHomIso_inv_app_hom (F : QuasicoherentSheaf X) :
    ((dualTensorInternalHomIso E).inv.app F).hom =
      eqToHom (internalHom_obj_obj E F) ≫
        (asIso (dualTensorIhom (C := X.Modules) E.obj)).inv.app F.obj :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
