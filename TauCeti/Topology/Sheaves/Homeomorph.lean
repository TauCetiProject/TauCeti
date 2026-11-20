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
def sheafCongrSheafToPresheafIso (A : Type a) [Category.{b} A] :
    (h.sheafCongr A).functor ⋙ sheafToPresheaf (Opens.grothendieckTopology Y) A ≅
      sheafToPresheaf (Opens.grothendieckTopology X) A ⋙
        (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
          h.opensCongr.symm.equivalence.functor.op :=
  -- Mathlib sheafCongr is inverse precomposition on the identical presheaf;
  -- sheafToPresheaf only forgets the sheaf-condition proof.
  Iso.refl _

/-- Transporting sheaves through a homeomorphism preserves addition of morphisms. -/
instance sheafCongr_additive (A : Type a) [Category.{b} A] [Preadditive A] :
    (h.sheafCongr A).functor.Additive where
  map_add := by
    intros
    -- Precomposition evaluates the original natural transformation at the inverse open.
    ext U
    rfl

variable (A : Type a) [Category.{b} A]
  [HasWeakSheafify (Opens.grothendieckTopology X) A]
  [HasWeakSheafify (Opens.grothendieckTopology Y) A]

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
    isoWhiskerRight (h.sheafCongrSheafToPresheafIso A).symm ((evaluation _ A).obj (op ⊤)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (h.sheafCongr A).functor
      (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).symm

/-- The global-section comparison is the native top-open map, conjugated by the section
identifications on both spaces. -/
@[reassoc]
theorem globalSectionsIso_hom_app (F : Sheaf (Opens.grothendieckTopology X) A) :
    (h.globalSectionsIso A).hom.app F =
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) A isTerminalTop).hom.app F ≫
        F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫
        ((h.sheafCongrSheafToPresheafIso A).inv.app F).app (op ⊤) ≫
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).inv.app
          ((h.sheafCongr A).functor.obj F) := by
  have hs : (sectionsHomeomorphIso h A).hom.app F =
      F.obj.map (eqToHom h.opensCongr.symm.map_top).op :=
    (NatIso.ofComponents_hom_app _ _ F).trans
      (F.obj.mapIso_hom ((eqToIso h.opensCongr.symm.map_top).op))
  have hg : (h.globalSectionsIso A).hom.app F =
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) A isTerminalTop).hom.app F ≫
        (sectionsHomeomorphIso h A).hom.app F ≫
        ((h.sheafCongrSheafToPresheafIso A).inv.app F).app (op ⊤) ≫ 𝟙 _ ≫
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).inv.app
          ((h.sheafCongr A).functor.obj F) :=
    -- The five defining iso fields; the middle identity is the functor associator.
    rfl
  exact hg.trans
    (((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) A isTerminalTop).hom.app F ≫=
      (hs =≫ (((h.sheafCongrSheafToPresheafIso A).inv.app F).app (op ⊤) ≫ 𝟙 _ ≫
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).inv.app
          ((h.sheafCongr A).functor.obj F)))).trans
      ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) A isTerminalTop).hom.app F ≫=
        (F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫=
          (((h.sheafCongrSheafToPresheafIso A).inv.app F).app (op ⊤) ≫=
            Category.id_comp _))))

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
        ((h.sheafCongrSheafToPresheafIso A).inv.app F).app (op ⊤) := by
  apply (Iso.eq_comp_inv
    ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).app
      ((h.sheafCongr A).functor.obj F))).mp
  exact (globalSectionsIso_hom_app h A F).trans
    ((_ ≫= (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)

end Homeomorph
