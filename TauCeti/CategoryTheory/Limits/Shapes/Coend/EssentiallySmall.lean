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

/-- The cowedge relation for a diagram restricted in both arguments along a functor. -/
private lemma condition_whiskeringLeft₂ {H : K ⥤ J}
    (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj H.op).obj H).obj F))
    {i j : K} (f : i ⟶ j) :
    (F.map (H.map f).op).app (H.obj i) ≫ c.π i =
      (F.obj (op (H.obj j))).map (H.map f) ≫ c.π j :=
  c.condition f

/-- Extend a cowedge on the restriction along an equivalence to the original diagram,
using the same vertex. The vertex is definitionally preserved so that the legs have the
same codomain. -/
@[expose] def ofWhiskerEquivalence (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj
    e.functor.op).obj e.functor).obj F)) : Cowedge F :=
  Cowedge.mk c.pt
    (fun j ↦ (F.map (e.counit.app j).op).app j ≫ (F.obj (op (e.functor.obj (e.inverse.obj j)))).map
      (e.counitInv.app j) ≫ c.π (e.inverse.obj j)) (fun i j f ↦ by
    have naturality := (F.map (e.functor.map (e.inverse.map f)).op).naturality (e.counitInv.app i)
    have naturality' := (F.map (e.counit.app j).op).naturality f
    simp only [Functor.id_obj, Functor.comp_obj] at naturality naturality'
    rw [← NatTrans.comp_app_assoc, ← F.map_comp, ← op_comp, ← e.counit_naturality f]
    simp only [op_comp, F.map_comp, NatTrans.comp_app, Category.assoc]
    rw [← (reassoc_of% naturality) (c.π (e.inverse.obj i))]
    rw [condition_whiskeringLeft₂ (H := e.functor) c (e.inverse.map f)]
    let T := F.obj (op (e.functor.obj (e.inverse.obj j)))
    rw [← T.map_comp_assoc (e.counitInv.app i) (e.functor.map (e.inverse.map f))
      (c.π (e.inverse.obj j)), e.counitInv_naturality f]
    rw [T.map_comp_assoc f (e.counitInv.app j) (c.π (e.inverse.obj j))]
    exact ((reassoc_of% naturality') (_ ≫ c.π (e.inverse.obj j))).symm)

@[simp]
lemma ofWhiskerEquivalence_pt (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj
    e.functor.op).obj e.functor).obj F)) : c.ofWhiskerEquivalence.pt = c.pt :=
  (rfl)

/-- The extended leg at `j` is obtained by applying the counit to the two diagram variables. -/
lemma ofWhiskerEquivalence_π (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj
    e.functor.op).obj e.functor).obj F)) (j : J) :
    c.ofWhiskerEquivalence.π j =
      (F.map (e.counit.app j).op).app j ≫ (F.obj (op (e.functor.obj (e.inverse.obj j)))).map
        (e.counitInv.app j) ≫ c.π (e.inverse.obj j) :=
  (rfl)

private lemma map_counitInv_comp_map_counit (T : J ⥤ D) (j : J) {P : D}
    (leg : T.obj j ⟶ P) :
    T.map (e.counitInv.app j) ≫ T.map (e.counit.app j) ≫ leg = leg := by
  have h : e.counitInv.app j ≫ e.counit.app j = 𝟙 j := e.counitIso_inv_hom_id_app j
  rw [← T.map_comp_assoc, h]
  exact (congrArg (· ≫ leg) (T.map_id j)).trans (Category.id_comp leg)

private lemma ofWhiskerEquivalence_whisker_π (c : Cowedge F) (j : J) :
    ((c.whisker e.functor).ofWhiskerEquivalence (e := e)).π j = c.π j := by
  have naturality := (F.map (e.counit.app j).op).naturality (e.counitInv.app j)
  have h := c.condition (e.counit.app j)
  simp only [Functor.id_obj, Functor.comp_obj] at naturality
  simp only [Functor.id_obj, Functor.comp_obj] at h
  have h' : (F.map (e.counit.app j).op).app (e.functor.obj (e.inverse.obj j)) ≫
        (c.whisker e.functor).π (e.inverse.obj j) = (F.obj (op j)).map (e.counit.app j) ≫ c.π j :=
    (congrArg (_ ≫ ·) (whisker_π c e.functor (e.inverse.obj j))).trans h
  rw [ofWhiskerEquivalence_π (e := e),
    ← (reassoc_of% naturality) ((c.whisker e.functor).π (e.inverse.obj j)), h']
  exact map_counitInv_comp_map_counit (e := e) (F.obj (op j)) j (c.π j)

/-- On the image of the equivalence, the extended legs are the original legs. -/
@[simp]
lemma ofWhiskerEquivalence_π_obj (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj
    e.functor.op).obj e.functor).obj F)) (k : K) :
    c.ofWhiskerEquivalence.π (e.functor.obj k) = c.π k := by
  have naturality := (F.map (e.functor.map (e.unitInv.app k)).op).naturality
    (e.counitInv.app (e.functor.obj k))
  simp only [Functor.id_obj, Functor.comp_obj] at naturality
  have h := condition_whiskeringLeft₂ (H := e.functor) c (e.unitInv.app k)
  simp only [Functor.id_obj, Functor.comp_obj] at h
  rw [ofWhiskerEquivalence_π (e := e), e.counit_app_functor,
    ← (reassoc_of% naturality) (c.π (e.inverse.obj (e.functor.obj k))),
    h, ← e.counit_app_functor]
  exact map_counitInv_comp_map_counit (e := e)
    (F.obj (op (e.functor.obj k))) (e.functor.obj k) (c.π k)

/-- A colimiting cowedge stays colimiting when extended along the equivalence. -/
def isColimitOfWhiskerEquivalence (c : Cowedge ((((Functor.whiskeringLeft₂ D).obj
    e.functor.op).obj e.functor).obj F)) (hc : IsColimit c) :
    IsColimit c.ofWhiskerEquivalence := by
  have fac (s : Cowedge F) (j : J) :
      c.ofWhiskerEquivalence.π j ≫ hc.desc (s.whisker e.functor) = s.π j := by
    have h : c.π (e.inverse.obj j) ≫ hc.desc (s.whisker e.functor) =
        (s.whisker e.functor).π (e.inverse.obj j) :=
      hc.fac (s.whisker e.functor) (.right (e.inverse.obj j))
    rw [ofWhiskerEquivalence_π (e := e)]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h)) |>.trans ?_
    exact ofWhiskerEquivalence_whisker_π (e := e) s j
  refine Multicofork.IsColimit.mk _ (fun s ↦ hc.desc (Cowedge.whisker s e.functor)) fac ?_
  intro s m hm
  apply Cowedge.IsColimit.hom_ext hc
  intro k
  rw [← ofWhiskerEquivalence_π_obj (e := e) c k]
  exact (hm (e.functor.obj k)).trans (fac s (e.functor.obj k)).symm

end Cowedge

/-- A colimiting cowedge for the restriction along an equivalence gives a colimiting cowedge
for the original diagram. -/
theorem hasCoend_of_equivalence (F : Jᵒᵖ ⥤ J ⥤ D) (e : K ≌ J)
    [HasCoend ((((Functor.whiskeringLeft₂ D).obj e.functor.op).obj e.functor).obj F)] :
    HasCoend F :=
  ⟨⟨_, Cowedge.isColimitOfWhiskerEquivalence (e := e) _ (colimit.isColimit _)⟩⟩

/-- A bifunctor on an essentially small category has a coend in a category with colimits
in the universe of the small model. -/
theorem hasCoend_of_essentiallySmall [EssentiallySmall.{w} J] [HasColimitsOfSize.{w, w} D]
    (F : Jᵒᵖ ⥤ J ⥤ D) : HasCoend F :=
  hasCoend_of_equivalence F (equivSmallModel.{w} J).symm

end CategoryTheory.Limits
