/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Coends over essentially small categories

A coend can be computed after restricting both arguments to a small model. This allows coends
in a target category with small colimits even when the indexing category has a larger object
universe.
-/

public section

open Opposite

namespace CategoryTheory.Limits

universe w

variable {J K D : Type*} [Category* J] [Category* K] [Category* D]

namespace Cowedge

/-- Restrict a cowedge along a functor in both arguments of its diagram. -/
abbrev whisker {F : Jᵒᵖ ⥤ J ⥤ D} (c : Cowedge F) (H : K ⥤ J) :
    Cowedge ((((Functor.whiskeringLeft₂ D).obj H.op).obj H).obj F) :=
  Cowedge.mk c.pt (fun k ↦ c.π (H.obj k)) fun _ _ f ↦ c.condition (H.map f)

@[simp]
lemma whisker_π {F : Jᵒᵖ ⥤ J ⥤ D} (c : Cowedge F) (H : K ⥤ J) (k : K) :
    (c.whisker H).π k = c.π (H.obj k) :=
  (rfl)

variable {F : Jᵒᵖ ⥤ J ⥤ D} {e : K ≌ J}

/-- The leg at `j` obtained from the leg at the chosen representative of `j`. -/
private def extendLeg (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj e.functor.op).obj
    e.functor).obj F)) (j : J) : (F.obj (op j)).obj j ⟶ c.pt :=
  (F.map (e.counit.app j).op).app j ≫ (F.obj (op (e.functor.obj (e.inverse.obj j)))).map
    (e.counitInv.app j) ≫ c.π (e.inverse.obj j)

private lemma extendLeg_condition (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj
    e.functor.op).obj e.functor).obj F)) {i j : J} (f : i ⟶ j) :
    (F.map f.op).app i ≫ extendLeg c i = (F.obj (op j)).map f ≫ extendLeg c j := by
  have h' :
      (F.map (e.functor.map (e.inverse.map f)).op).app (e.functor.obj (e.inverse.obj i)) ≫
          c.π (e.inverse.obj i) =
        (F.obj (op (e.functor.obj (e.inverse.obj j)))).map (e.functor.map (e.inverse.map f)) ≫
          c.π (e.inverse.obj j) := c.condition (e.inverse.map f)
  have naturality := (F.map (e.functor.map (e.inverse.map f)).op).naturality (e.counitInv.app i)
  have naturality' := (F.map (e.counit.app j).op).naturality f
  unfold extendLeg
  -- The legs of the restricted cowedge are indexed by the right objects of its multispan.
  erw [← NatTrans.comp_app_assoc, ← F.map_comp, ← op_comp, ← e.counit_naturality f,
    op_comp, F.map_comp, NatTrans.comp_app, Category.assoc,
    ← reassoc_of% naturality, h',
    ← Functor.map_comp_assoc, e.counitInv_naturality, Functor.map_comp, Category.assoc,
    reassoc_of% naturality']

private lemma extendLeg_whisker (c : Cowedge F) (j : J) :
    extendLeg (c.whisker e.functor) j = c.π j := by
  have naturality := (F.map (e.counit.app j).op).naturality (e.counitInv.app j)
  unfold extendLeg
  erw [whisker_π, ← reassoc_of% naturality,
    c.condition (e.counit.app j),
    ← Functor.map_comp_assoc, e.counitIso_inv_hom_id_app, Functor.map_id, Category.id_comp]
  rfl

private lemma extendLeg_obj (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj
    e.functor.op).obj e.functor).obj F)) (k : K) :
    extendLeg c (e.functor.obj k) = c.π k := by
  have h :
      (F.map (e.functor.map (e.unitInv.app k)).op).app (e.functor.obj (e.inverse.obj
          (e.functor.obj k))) ≫ c.π (e.inverse.obj (e.functor.obj k)) =
        (F.obj (op (e.functor.obj k))).map (e.functor.map (e.unitInv.app k)) ≫ c.π k :=
    c.condition (e.unitInv.app k)
  have naturality := (F.map (e.functor.map (e.unitInv.app k)).op).naturality
    (e.counitInv.app (e.functor.obj k))
  unfold extendLeg
  erw [e.counit_app_functor, ← reassoc_of% naturality,
    h, ← Functor.map_comp_assoc,
    ← e.counit_app_functor, e.counitIso_inv_hom_id_app, Functor.map_id, Category.id_comp]

/-- A colimiting cowedge for the restriction along an equivalence gives a colimiting cowedge
for the original diagram. -/
theorem hasCoend_of_equivalence (F : Jᵒᵖ ⥤ J ⥤ D) (e : K ≌ J)
    [HasCoend ((((Functor.whiskeringLeft₂ D).obj e.functor.op).obj e.functor).obj F)] :
    HasCoend F := by
  let c : Cowedge ((((Functor.whiskeringLeft₂ D).obj e.functor.op).obj e.functor).obj F) :=
    colimit.cocone _
  have hc : IsColimit c := colimit.isColimit _
  let c' : Cowedge F := Cowedge.mk c.pt (extendLeg c) (fun _ _ f ↦ extendLeg_condition c f)
  have fac (s : Cowedge F) (j : J) :
      c'.π j ≫ hc.desc (s.whisker e.functor) = s.π j := by
    have h : c.π (e.inverse.obj j) ≫ hc.desc (s.whisker e.functor) =
        (s.whisker e.functor).π (e.inverse.obj j) :=
      hc.fac (s.whisker e.functor) (.right (e.inverse.obj j))
    rw [Cowedge.mk_π]
    unfold extendLeg
    erw [Category.assoc, Category.assoc, h]
    exact extendLeg_whisker (e := e) s j
  refine ⟨⟨c', Multicofork.IsColimit.mk _ (fun s ↦ hc.desc (Cowedge.whisker s e.functor)) fac ?_⟩⟩
  intro s m hm
  apply Cowedge.IsColimit.hom_ext hc
  intro k
  rw [← extendLeg_obj c k]
  exact (hm (e.functor.obj k)).trans (fac s (e.functor.obj k)).symm

end Cowedge

/-- A bifunctor on an essentially small category has a coend in a category with colimits
in the universe of the small model. -/
theorem hasCoend_of_essentiallySmall [EssentiallySmall.{w} J] [HasColimitsOfSize.{w, w} D]
    (F : Jᵒᵖ ⥤ J ⥤ D) : HasCoend F :=
  Cowedge.hasCoend_of_equivalence F (equivSmallModel.{w} J).symm

end CategoryTheory.Limits
