/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import TauCeti.CategoryTheory.Sites.Preadditive

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

/-- Inverse-image transport of opens preserves and reflects their covering sieves.
The inverse leg is the hypothesis of Mathlib's native sheaf equivalence; Mathlib derives
its forward-leg instance from this one. -/
instance opensCongr_isDenseSubsite :
    h.opensCongr.equivalence.inverse.IsDenseSubsite
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) where
  functorPushforward_mem_iff := by
    intro U S
    constructor
    · intro hS x hx
      obtain ⟨W, f, ⟨V, g, k, hg, _⟩, hw⟩ := hS (h.symm x) (by simpa using hx)
      refine ⟨V, g, hg, ?_⟩
      have hxV := k.le hw
      simpa using hxV
    · intro hS y hy
      obtain ⟨V, f, hf, hv⟩ := hS (h y) hy
      exact ⟨h.symm.opensCongr V, h.symm.opensCongr.equivalence.functor.map f,
        ⟨V, f, 𝟙 _, hf, (Category.id_comp _).symm⟩, hv⟩

/-- The inverse-opens functor of the identity homeomorphism is the native identity functor. -/
theorem opensCongr_inverse_refl :
    (Homeomorph.refl X).opensCongr.equivalence.inverse = 𝟭 (Opens X) := by
  rfl

/-- Inverse-opens transport follows the actual composite in the contravariant order. -/
theorem opensCongr_inverse_trans {Z : Type*} [TopologicalSpace Z] (k : Y ≃ₜ Z) :
    (h.trans k).opensCongr.equivalence.inverse =
      k.opensCongr.equivalence.inverse ⋙ h.opensCongr.equivalence.inverse := by
  rfl

/-- The actual inverse-opens precomposition functors compose in the same order after `op`. -/
theorem opensCongr_inverse_op_trans {Z : Type*} [TopologicalSpace Z] (k : Y ≃ₜ Z) :
    (h.trans k).opensCongr.equivalence.inverse.op =
      k.opensCongr.equivalence.inverse.op ⋙ h.opensCongr.equivalence.inverse.op := by
  rfl

variable (A : Type a) [Category.{b} A]

private def sectionsHomeomorphIso :
    (sheafSections (Opens.grothendieckTopology X) A).obj (op ⊤) ≅
      (h.opensCongr.equivalence.sheafCongr
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor ⋙
        (sheafSections (Opens.grothendieckTopology Y) A).obj (op ⊤) :=
  NatIso.ofComponents
    (fun F ↦ F.obj.mapIso (eqToIso h.opensCongr.symm.map_top).op)
    (fun α ↦ (α.hom.naturality _).symm)

variable [HasWeakSheafify (Opens.grothendieckTopology X) A]
  [HasWeakSheafify (Opens.grothendieckTopology Y) A]

/-- A homeomorphism preserves global sections in the original coefficient category. -/
def globalSectionsIso :
    Sheaf.Γ (Opens.grothendieckTopology X) A ≅
      (h.opensCongr.equivalence.sheafCongr
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor ⋙
        Sheaf.Γ (Opens.grothendieckTopology Y) A :=
  Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop ≪≫
    sectionsHomeomorphIso h A ≪≫
    isoWhiskerLeft (h.opensCongr.equivalence.sheafCongr
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor
      (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).symm

/-- The native comparison reads the same top-open section after transport. -/
@[reassoc]
theorem globalSectionsIso_hom_app_comp_ΓNatIsoSheafSections_hom
    (F : Sheaf (Opens.grothendieckTopology X) A) :
    (h.globalSectionsIso A).hom.app F ≫
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).hom.app
          ((h.opensCongr.equivalence.sheafCongr
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F) =
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) A isTerminalTop).hom.app F ≫
        F.obj.map (eqToHom h.opensCongr.symm.map_top).op := by
  have hs : (sectionsHomeomorphIso h A).hom.app F =
      F.obj.map (eqToHom h.opensCongr.symm.map_top).op :=
    (NatIso.ofComponents_hom_app _ _ F).trans
      (F.obj.mapIso_hom ((eqToIso h.opensCongr.symm.map_top).op))
  let F' := (h.opensCongr.equivalence.sheafCongr
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F
  have hg : (h.globalSectionsIso A).hom.app F =
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) A isTerminalTop).hom.app F ≫
        F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).inv.app F' := by
    simp only [globalSectionsIso, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
      whiskerLeft_app, Iso.symm_hom]
    exact _ ≫= (hs =≫ _)
  exact (Iso.eq_comp_inv
    ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) A isTerminalTop).app F')).mp
      (hg.trans (Category.assoc _ _ _).symm)

end Homeomorph
