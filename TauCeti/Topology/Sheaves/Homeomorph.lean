/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Whiskering
public import TauCeti.CategoryTheory.Sites.Whiskering

/-!
# Sheaves under a homeomorphism across universes

The order equivalence on opens supplied by a homeomorphism identifies their covering sieves.
The resulting equivalence of sheaf categories keeps the coefficient objects unchanged.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits CategoryTheory.Functor

universe u v a b

namespace Homeomorph

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y] (h : X ≃ₜ Y)

/-- Transporting opens by a homeomorphism preserves and reflects covering sieves. -/
instance opensCongr_isDenseSubsite :
    h.opensCongr.equivalence.functor.IsDenseSubsite
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) where
  functorPushforward_mem_iff := by
    intro U S
    constructor
    · intro hS x hx
      obtain ⟨W, f, ⟨V, g, k, hg, _⟩, hw⟩ := hS (h x) (by simpa using hx)
      refine ⟨V, g, hg, ?_⟩
      have hxV := k.le hw
      simpa using hxV
    · intro hS y hy
      obtain ⟨V, f, hf, hv⟩ := hS (h.symm y) hy
      exact ⟨h.opensCongr V, h.opensCongr.equivalence.functor.map f,
        ⟨V, f, 𝟙 _, hf, (Category.id_comp _).symm⟩, hv⟩

/-- Sheaves on homeomorphic spaces are equivalent, including across base universes. -/
def sheafCongr (A : Type a) [Category.{b} A] :
    TopCat.Sheaf A (TopCat.of X) ≌ TopCat.Sheaf A (TopCat.of Y) := by
  let : h.opensCongr.equivalence.inverse.IsDenseSubsite
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    opensCongr_isDenseSubsite h.symm
  exact h.opensCongr.equivalence.sheafCongr
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A

/-- The sheaf equivalence acts on sections by the existing inverse equivalence on opens. -/
def sheafCongrForgetIso (A : Type a) [Category.{b} A] :
    (h.sheafCongr A).functor ⋙ sheafToPresheaf (Opens.grothendieckTopology Y) A ≅
      sheafToPresheaf (Opens.grothendieckTopology X) A ⋙
        (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
          h.opensCongr.symm.equivalence.functor.op :=
  Iso.refl _

/-- Transporting sheaves through a homeomorphism preserves addition of morphisms. -/
instance sheafCongr_additive (A : Type a) [Category.{b} A] [Preadditive A] :
    (h.sheafCongr A).functor.Additive where
  map_add := by intros; ext U; rfl

variable (A : Type a) [Category.{b} A]
  [HasSheafify (Opens.grothendieckTopology X) A]
  [HasSheafify (Opens.grothendieckTopology Y) A]

private def sectionsHomeomorphIso :
    (sheafSections (Opens.grothendieckTopology X) A).obj (op ⊤) ≅
      (sheafToPresheaf (Opens.grothendieckTopology X) A ⋙
        (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
          h.opensCongr.symm.equivalence.functor.op) ⋙
        (evaluation (Opens Y)ᵒᵖ A).obj (op ⊤) :=
  NatIso.ofComponents (fun F ↦ F.obj.mapIso (eqToIso h.opensCongr.symm.map_top).op)
    (fun f ↦ (f.hom.naturality _).symm)

/-- A homeomorphism preserves the original coefficient object of global sections. -/
def globalSectionsIso :
    Sheaf.Γ (Opens.grothendieckTopology X) A ≅
      (h.sheafCongr A).functor ⋙ Sheaf.Γ (Opens.grothendieckTopology Y) A :=
  Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop ≪≫
    sectionsHomeomorphIso h A ≪≫
    isoWhiskerRight (h.sheafCongrForgetIso A).symm ((evaluation _ A).obj (op ⊤)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (h.sheafCongr A).functor
      (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).symm

/-- The homeomorphism comparison preserves the section over the whole space, with the native
map of the top open and the underlying-presheaf comparison. -/
@[reassoc]
theorem globalSectionsIso_hom_app_comp_ΓNatIsoSheafSections_hom
    (F : Sheaf (Opens.grothendieckTopology X) A) :
    (h.globalSectionsIso A).hom.app F ≫
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).hom.app
          ((h.sheafCongr A).functor.obj F) =
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) A isTerminalTop).hom.app F ≫
        F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫
        ((h.sheafCongrForgetIso A).inv.app F).app (op ⊤) := by
  simp only [flip_obj_obj, ObjectProperty.ι_obj, comp_obj, globalSectionsIso, opensCongr_symm,
    sectionsHomeomorphIso, op_obj, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, whiskeringLeft_obj_obj, evaluation_obj_obj,
    NatIso.ofComponents_hom_app, whiskerRight_app, evaluation_obj_map, associator_hom_app,
    whiskerLeft_app, Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    NatIso.cancel_natIso_hom_left]
  exact congrArg₂ (fun f g ↦ f ≫ g)
    ((Functor.mapIso_hom F.obj (eqToIso h.opensCongr.symm.map_top).op).trans
      (congrArg F.obj.map ((Iso.op_hom (eqToIso h.opensCongr.symm.map_top)).trans
        (congrArg Quiver.Hom.op (eqToIso.hom h.opensCongr.symm.map_top)))))
    (congrArg (fun η ↦ (η.app F).app (op ⊤)) (Iso.symm_hom (h.sheafCongrForgetIso A)))

end Homeomorph
