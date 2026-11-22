/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Topology.Sheaves.Cech.Colimit
public import TauCeti.Topology.Sheaves.Homeomorph
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Reindex
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.LongExactSequence
public import Mathlib.CategoryTheory.Limits.Final
public import TauCeti.Topology.Sheaves.Cech.Functoriality
public import TauCeti.Topology.Sheaves.Cech.LongExactSequence

import Mathlib.CategoryTheory.CommSq

/-!
# Čech cohomology under a homeomorphism

Homeomorphisms identify native point-neighborhood covers and their Čech cohomology,
including when the spaces belong to different universes.

## Main constructions

* `cechComplexHomeomorphIso` identifies tuple complexes, with hom and inverse component laws.
* `cechCohomologyHomeomorphIso` identifies the cover-colimit cohomology, preserving native
  augmentation, refinement, degree-zero global sections and connecting maps.
-/

public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open CategoryTheory.Functor

universe u v

namespace TauCeti.Topology

universe a b

open TauCeti.CategoryTheory

variable {A : Type a} [Category.{b} A] [Preadditive A]

variable {X : TopCat.{u}} {Y : TopCat.{v}} (h : X ≃ₜ Y)
  [HasProducts.{u} A] [HasProducts.{v} A]
  (U : PointOpenCover X) (P : (Opens X)ᵒᵖ ⥤ A)

private lemma inverseOpens_mapHomeomorph :
    (fun y ↦ h.opensCongr.equivalence.inverse.obj ((U.mapHomeomorph h).opens y)) =
      U.opens ∘ h.symm.toEquiv :=
  funext fun y ↦ by
    rw [PointOpenCover.mapHomeomorph_opens]
    exact h.opensCongr.symm_apply_apply _

omit [HasProducts.{u} A] in
@[reassoc]
private lemma cechComplex_eqToIso_hom_app_f_π (V W : Y → Opens X) (q : V = W)
    (n : ℕ) (a : Fin (n + 1) → Y) :
    ((eqToIso (congrArg (fun V ↦ cechComplexFunctor (A := A) V) q)).hom.app P).f n ≫
        (cechXIso W P n).hom ≫ Pi.π _ a =
      (cechXIso V P n).hom ≫ Pi.π _ a ≫
        P.map (eqToHom (congrArg (fun V ↦ ∏ᶜ fun j ↦ V (a j)) q.symm)).op := by
  subst W
  simp

/-- The native Čech complex of a cover is unchanged after transporting the points, opens and
presheaf through a homeomorphism, even across different base universes. -/
def cechComplexHomeomorphIso :
    cechComplexFunctor.{u} (A := A) U.opens ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
          h.opensCongr.equivalence.inverse.op ⋙
        cechComplexFunctor.{v} (U.mapHomeomorph h).opens :=
  (cechComplexReindexIso h.symm.toEquiv U.opens).symm ≪≫
    (eqToIso (congrArg (fun V : Y → Opens X ↦ cechComplexFunctor (A := A) V)
      (inverseOpens_mapHomeomorph h U).symm)) ≪≫
    NatIso.ofComponents (fun P ↦
      cechComplexCompIso h.opensCongr.equivalence.inverse (U.mapHomeomorph h).opens P
        (fun _ _ ↦ inferInstance))
      (fun φ ↦ cechComplexFunctor_map_comp_cechComplexCompIso_hom
        h.opensCongr.equivalence.inverse (U.mapHomeomorph h).opens _
        (fun _ _ ↦ inferInstance) φ)

/-- The inverse image of a finite intersection maps to the intersection of inverse images. -/
def homeomorphTupleComparison (n : ℕ) (a : Fin (n + 1) → Y) :
    h.opensCongr.equivalence.inverse.obj (∏ᶜ fun j ↦ (U.mapHomeomorph h).opens (a j)) ⟶
      ∏ᶜ fun j ↦ U.opens (h.symm (a j)) :=
  (Pi.lift fun j ↦ h.opensCongr.equivalence.inverse.map
    (Pi.π (fun j ↦ (U.mapHomeomorph h).opens (a j)) j)) ≫
      eqToHom (congrArg (fun V ↦ ∏ᶜ fun j ↦ V (a j)) (inverseOpens_mapHomeomorph h U))

/-- Inverse-image transport preserves finite intersections. -/
instance homeomorphTupleComparison_isIso (n : ℕ) (a : Fin (n + 1) → Y) :
    IsIso (homeomorphTupleComparison h U n a) := by
  -- The first factor is the native product comparison of the opens equivalence.
  change IsIso (piComparison h.opensCongr.equivalence.inverse
    (fun j ↦ (U.mapHomeomorph h).opens (a j)) ≫ _)
  infer_instance

/-- The native component reads a transported tuple by the corresponding original tuple. -/
@[reassoc]
theorem cechComplexHomeomorphIso_hom_app_f_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((cechComplexHomeomorphIso (A := A) h U).hom.app P).f n ≫ Pi.π _ a =
      Pi.π _ (h.symm.toEquiv ∘ a) ≫ P.map (homeomorphTupleComparison h U n a).op := by
  let G := h.opensCongr.equivalence.inverse
  let V := (U.mapHomeomorph h).opens
  -- Compose the native projection laws as terms: rewriting the hidden tuple carrier can
  -- otherwise choose a different product-cone presentation of the dependent codomain.
  have hc : (cechComplexCompIso G V P (fun _ _ ↦ inferInstance)).hom.f n ≫
      (cechXIso V (G.op ⋙ P) n).hom ≫ Pi.π _ a =
      (cechXIso (fun i ↦ G.obj (V i)) P n).hom ≫ Pi.π _ a ≫
        P.map (Pi.lift fun j ↦ G.map (Pi.π (fun j ↦ V (a j)) j)).op :=
    (_ ≫= cechXIso_hom_π V (G.op ⋙ P) n a).trans <|
      (cechComplexCompIso_hom_f_π G V P (fun _ _ ↦ inferInstance) n a).trans
        (cechXIso_hom_π_assoc _ P n a _).symm
  have hi : ((cechComplexReindexIso h.symm.toEquiv U.opens).inv.app P).f n ≫
      (cechXIso (U.opens ∘ h.symm.toEquiv) P n).hom ≫ Pi.π _ a =
      (cechXIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a) :=
    (_ ≫= cechXIso_hom_π _ P n a).trans
      ((cechComplexReindexIso_inv_app_f_π h.symm.toEquiv U.opens P n a).trans
        (cechXIso_hom_π U.opens P n (h.symm.toEquiv ∘ a)).symm)
  have hr : ((cechComplexHomeomorphIso (A := A) h U).hom.app P).f n ≫
      (cechXIso V (G.op ⋙ P) n).hom ≫ Pi.π _ a =
      (cechXIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a) ≫
        P.map (homeomorphTupleComparison h U n a).op := by
    dsimp only [G, V] at hc
    simp only [cechComplexHomeomorphIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      NatIso.ofComponents_hom_app, HomologicalComplex.comp_f, Category.assoc]
    rw [hc, cechComplex_eqToIso_hom_app_f_π_assoc P (U.opens ∘ h.symm.toEquiv)
      (fun y ↦ G.obj (V y)) (inverseOpens_mapHomeomorph h U).symm n a,
      reassoc_of% hi]
    simp only [homeomorphTupleComparison, op_comp, Functor.map_comp]
  exact (_ ≫= (cechXIso_hom_π V (G.op ⋙ P) n a).symm).trans
    (hr.trans (cechXIso_hom_π_assoc U.opens P n (h.symm.toEquiv ∘ a) _))

/-- The inverse component reads each original tuple through the inverse open comparison. -/
@[reassoc]
theorem cechComplexHomeomorphIso_inv_app_f_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((cechComplexHomeomorphIso (A := A) h U).inv.app P).f n ≫
        Pi.π _ (h.symm.toEquiv ∘ a) =
      Pi.π _ a ≫ P.map (inv (homeomorphTupleComparison h U n a)).op := by
  apply (Iso.eq_comp_inv (P.mapIso (asIso (homeomorphTupleComparison h U n a)).op)).mpr
  let j := (HomologicalComplex.eval A (ComplexShape.up ℕ) n).mapIso
    ((cechComplexHomeomorphIso (A := A) h U).app P)
  have hread := j.inv ≫= cechComplexHomeomorphIso_hom_app_f_π h U P n a
  exact (Category.assoc _ _ _).trans (hread.symm.trans (j.inv_hom_id_assoc _))

/-- Transport through a homeomorphism preserves restriction of a global section to its cover. -/
@[reassoc]
theorem cechAugmentation_comp_cechComplexHomeomorphIso_hom_app [HasZeroObject A] :
    cechAugmentation U.opens isTerminalTop P ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P =
      (CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op) ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop
          (h.opensCongr.equivalence.inverse.op ⋙ P) := by
  let G := h.opensCongr.equivalence.inverse
  let B := fun y ↦ G.obj ((U.mapHomeomorph h).opens y)
  let r := cechComplexReindexIso (A := A) h.symm.toEquiv U.opens
  let q := eqToIso (congrArg (cechComplexFunctor.{v} (A := A))
    (inverseOpens_mapHomeomorph h U).symm)
  let c := cechComplexCompIso G (U.mapHomeomorph h).opens P (fun _ _ ↦ inferInstance)
  -- Give the terminal comparison the same native G.obj carrier as the augmentation.
  let α : P.obj (op ⊤) ⟶ P.obj (op (G.obj ⊤)) :=
    P.map (eqToHom h.opensCongr.symm.map_top).op
  let hGT : IsTerminal (G.obj (⊤ : Opens Y)) :=
    isTerminalTop.ofIso (eqToIso h.opensCongr.symm.map_top).symm
  have ht : (CochainComplex.single₀ A).map α ≫ cechAugmentation B hGT P =
      cechAugmentation B isTerminalTop P := by
    apply HomologicalComplex.from_single_hom_ext
    refine Pi.hom_ext _ _ fun a ↦ ?_
    rw [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero]
    have hmap : α ≫ P.map (hGT.from (∏ᶜ fun j ↦ B (a j))).op =
        P.map (isTerminalTop.from (∏ᶜ fun j ↦ B (a j))).op :=
      (P.map_comp _ _).symm.trans (congrArg P.map (Subsingleton.elim _ _))
    exact (Category.assoc _ _ _).trans
      ((α ≫= cechAugmentation_f_zero_comp_π B hGT P a).trans
        (hmap.trans (cechAugmentation_f_zero_comp_π B isTerminalTop P a).symm))
  have hq (V W : Y → Opens X) (q : V = W) :
      cechAugmentation V isTerminalTop P ≫
        (eqToIso (congrArg (cechComplexFunctor.{v} (A := A)) q)).hom.app P =
          cechAugmentation W isTerminalTop P := by
    subst W
    exact Category.comp_id _
  have hr := (Iso.eq_comp_inv (r.app P)).mpr
    (cechAugmentation_comp_cechComplexReindexIso_hom_app h.symm.toEquiv U.opens P isTerminalTop)
  have hc := cechAugmentation_comp_cechComplexCompIso_hom G (U.mapHomeomorph h).opens P
    (fun _ _ ↦ inferInstance) isTerminalTop hGT
  change cechAugmentation U.opens isTerminalTop P ≫
    (r.inv.app P ≫ q.hom.app P ≫ c.hom) =
      (CochainComplex.single₀ A).map α ≫ _
  calc
    _ = (cechAugmentation U.opens isTerminalTop P ≫ r.inv.app P) ≫
        q.hom.app P ≫ c.hom := (Category.assoc _ _ _).symm
    _ = cechAugmentation (U.opens ∘ h.symm.toEquiv) isTerminalTop P ≫
        q.hom.app P ≫ c.hom := hr.symm =≫ _
    _ = cechAugmentation B isTerminalTop P ≫ c.hom :=
      (Category.assoc _ _ _).symm.trans
        (hq _ _ (inverseOpens_mapHomeomorph h U).symm =≫ _)
    _ = ((CochainComplex.single₀ A).map α ≫ cechAugmentation B hGT P) ≫ c.hom := ht.symm =≫ _
    _ = (CochainComplex.single₀ A).map α ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop (G.op ⋙ P) :=
      (Category.assoc _ _ _).trans (_ ≫= hc)


private lemma cechAugmentation_comp_homeomorph_map [HasZeroObject A]
    (Q : (Opens Y)ᵒᵖ ⥤ A)
    (φ : h.opensCongr.equivalence.inverse.op ⋙ P ⟶ Q) :
    cechAugmentation U.opens isTerminalTop P ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P ≫
        (cechComplexFunctor (U.mapHomeomorph h).opens).map φ =
      (CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤)) ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop Q := by
  -- The native restriction lands in the top-open value of inverse precomposition.
  let α : P.obj (op ⊤) ⟶ (h.opensCongr.equivalence.inverse.op ⋙ P).obj (op ⊤) :=
    P.map (eqToHom h.opensCongr.symm.map_top).op
  have hs : CommSq _ _ _ _ :=
    ⟨cechAugmentation_comp_cechComplexHomeomorphIso_hom_app h U P⟩
  have hn : CommSq _ _ _ _ := ⟨cechAugmentation_naturality (U.mapHomeomorph h).opens
    isTerminalTop (h.opensCongr.equivalence.inverse.op ⋙ P) φ⟩
  exact (hs.vert_comp hn).w.trans
    (((CochainComplex.single₀ A).map_comp α (φ.app (op ⊤))).symm =≫ _)

@[reassoc]
private lemma cechAugmentationClass_comp_homeomorph_map
    [CategoryWithHomology A] [HasZeroObject A] (Q : (Opens Y)ᵒᵖ ⥤ A)
    (φ : h.opensCongr.equivalence.inverse.op ⋙ P ⟶ Q) :
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
        (P.obj (op ⊤))).inv ≫
        HomologicalComplex.homologyMap (cechAugmentation U.opens isTerminalTop P) 0 ≫
        HomologicalComplex.homologyMap
          ((cechComplexHomeomorphIso (A := A) h U).hom.app P) 0 ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor (U.mapHomeomorph h).opens).map φ) 0 =
      (P.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤)) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          (Q.obj (op ⊤))).inv ≫
        HomologicalComplex.homologyMap
          (cechAugmentation (U.mapHomeomorph h).opens isTerminalTop Q) 0 := by
  have ha := congrArg ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0).map)
    (cechAugmentation_comp_homeomorph_map h U P Q φ)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp] at ha
  have hs := HomologicalComplex.singleObjHomologySelfIso_inv_naturality (ComplexShape.up ℕ) 0
    (P.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤))
  calc
    _ = (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          (P.obj (op ⊤))).inv ≫
        HomologicalComplex.homologyMap ((CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤))) 0 ≫
        HomologicalComplex.homologyMap
          (cechAugmentation (U.mapHomeomorph h).opens isTerminalTop Q) 0 := _ ≫= ha
    _ = _ := by rw [← Category.assoc, hs, Category.assoc]

/-- Native transport of Čech complexes commutes with every actual refinement function. -/
@[reassoc]
theorem cechComplexMap_comp_cechComplexHomeomorphIso_hom_app {V : PointOpenCover X}
    (φ : U.toFormalCoproduct ⟶ V.toFormalCoproduct) :
    cechComplexMap.{u, u, b, u, a} (U := U.opens) (V := V.opens) P φ ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P =
      (cechComplexHomeomorphIso (A := A) h V).hom.app P ≫
        cechComplexMap.{v, v, b, v, a}
          (U := (U.mapHomeomorph h).opens) (V := (V.mapHomeomorph h).opens)
          (h.opensCongr.equivalence.inverse.op ⋙ P) (U.mapHomeomorphHom h φ) := by
  let G := h.opensCongr.equivalence.inverse
  let ψ := U.mapHomeomorphHom h φ
  let r (T : PointOpenCover X) :
      cechComplexFunctor.{v} (A := A) (fun y ↦ G.obj ((T.mapHomeomorph h).opens y)) ≅
        cechComplexFunctor.{u} (A := A) T.opens :=
    eqToIso (congrArg (cechComplexFunctor.{v} (A := A))
      (inverseOpens_mapHomeomorph h T)) ≪≫ cechComplexReindexIso h.symm.toEquiv T.opens
  let ψG : FormalCoproduct.mk Y (fun y ↦ G.obj ((U.mapHomeomorph h).opens y)) ⟶
      FormalCoproduct.mk Y (fun y ↦ G.obj ((V.mapHomeomorph h).opens y)) :=
    ⟨ψ.f, fun y ↦ G.map (ψ.φ y)⟩
  have hf : φ.f ∘ h.symm.toEquiv = h.symm.toEquiv ∘ ψG.f := by
    funext y
    simp [ψG, ψ, PointOpenCover.mapHomeomorphHom_f]
  have hr := cechComplexMap_comp_cechComplexReindexIso_hom_app (A := A)
    h.symm.toEquiv U.opens P
    h.symm.toEquiv V.opens _ _ (inverseOpens_mapHomeomorph h U)
    (inverseOpens_mapHomeomorph h V) φ ψG hf (fun _ ↦ Subsingleton.elim _ _)
  have hs : CommSq ((r V).app P).hom (cechComplexMap.{v, u, b, u, a} P ψG)
      (cechComplexMap.{u, u, b, u, a} P φ) ((r U).app P).hom := ⟨hr.symm⟩
  have hc := cechComplexMap_comp_cechComplexCompIso_hom G (U.mapHomeomorph h).opens P
    (fun _ _ ↦ inferInstance) ψ (fun _ _ ↦ inferInstance)
  have hw := (hs.horiz_inv.horiz_comp ⟨hc.symm⟩).w.symm
  simpa only [r, G, ψ, Iso.app_inv, Iso.trans_inv, NatTrans.comp_app,
    cechComplexHomeomorphIso, Iso.trans_hom, Iso.symm_hom,
    NatIso.ofComponents_hom_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    Category.assoc] using hw

section Cohomology

-- The cover order equivalence is opaque outside CoverSystems.
-- Mathlib's changeFunctor retains that equivalence and gives its functor the literal
-- native cover-map object function, so diagram components need no dependent casts.
private def coverHomeomorphEquivalence : PointOpenCover X ≌ PointOpenCover Y :=
  let G : PointOpenCover X ⥤ PointOpenCover Y :=
    { obj := fun U ↦ U.mapHomeomorph h
      map := fun f ↦ homOfLE
        ((PointOpenCover.mapHomeomorph_le_mapHomeomorph_iff h _ _).mpr (leOfHom f)) }
  (PointOpenCover.orderIsoOfHomeomorph h).equivalence.changeFunctor
    (NatIso.ofComponents (fun U ↦ eqToIso (by
      simp only [OrderIso.equivalence_functor, Monotone.functor_obj,
        PointOpenCover.orderIsoOfHomeomorph_apply, G])) (fun _ ↦ Subsingleton.elim _ _)
      : (PointOpenCover.orderIsoOfHomeomorph h).equivalence.functor ≅ G)

variable [CategoryWithHomology A] (n : ℕ)

private def cechHomeomorphDiagramIso :
    (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := X))
      (fun _ _ hf ↦ hf) n).flip.obj P ≅
      (coverHomeomorphEquivalence h).functor ⋙
        (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := Y))
          (fun _ _ hf ↦ hf) n).flip.obj
          (h.opensCongr.equivalence.inverse.op ⋙ P) := by
  refine NatIso.ofComponents (fun U ↦
    (HomologicalComplex.homologyFunctor A _ n).mapIso
      ((cechComplexHomeomorphIso (A := A) h U).app P)) ?_
  intro U V f
  let φ := (leOfHom f).some
  let ψ := V.mapHomeomorphHom h φ
  dsimp only [Functor.flip_obj_map, Functor.comp_map]
  rw [cechCohomologyDiagram_map A (PointOpenCover.toFormalCoproduct (X := X))
    (fun _ _ hf ↦ hf) n f φ,
    cechCohomologyDiagram_map A (PointOpenCover.toFormalCoproduct (X := Y)) (fun _ _ hf ↦ hf) n
      ((coverHomeomorphEquivalence h).functor.map f) ψ]
  have hc := congrArg ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n).map)
    (cechComplexMap_comp_cechComplexHomeomorphIso_hom_app h V P φ)
  simp only [Functor.map_comp] at hc
  exact (cechComplexHomologyMap_app A n φ P =≫ _).trans
    (hc.trans (_ ≫= (cechComplexHomologyMap_app A n ψ
      (h.opensCongr.equivalence.inverse.op ⋙ P)).symm))

variable [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]

private def cechHomeomorphDiagramsIso :
    (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := X))
      (fun _ _ hf ↦ hf) n).flip ≅
    (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
      h.opensCongr.equivalence.inverse.op ⋙
      (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := Y))
        (fun _ _ hf ↦ hf) n).flip ⋙
      (Functor.whiskeringLeft _ _ A).obj (coverHomeomorphEquivalence h).functor := by
  refine NatIso.ofComponents (fun P ↦ cechHomeomorphDiagramIso h P n) ?_
  intro P Q φ
  ext U
  exact (Functor.isoWhiskerRight (cechComplexHomeomorphIso (A := A) h U)
    (HomologicalComplex.homologyFunctor A _ n)).hom.naturality φ

/-- Native cover-colimit Čech cohomology is preserved by a homeomorphism across universes. -/
def cechCohomologyHomeomorphIso :
    cechCohomology X A n ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
        h.opensCongr.equivalence.inverse.op ⋙ cechCohomology Y A n :=
  isoWhiskerRight (cechHomeomorphDiagramsIso h n) colim ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (Functor.Final.colimIso (coverHomeomorphEquivalence h).functor))

/-- Read the native colimit map underlying the transport comparison. -/
private lemma cechCohomologyHomeomorphIso_hom_app_eq :
    (cechCohomologyHomeomorphIso (A := A) h n).hom.app P =
      colimMap (cechHomeomorphDiagramIso h P n).hom ≫
        (Functor.Final.colimitIso (coverHomeomorphEquivalence h).functor
          ((cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := Y))
            (fun _ _ hf ↦ hf) n).flip.obj
              (h.opensCongr.equivalence.inverse.op ⋙ P))).hom := by
  let W := (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
    h.opensCongr.equivalence.inverse.op
  let D := (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := Y))
    (fun _ _ hf ↦ hf) n).flip
  let E := (Functor.whiskeringLeft _ _ A).obj (coverHomeomorphEquivalence h).functor
  -- Spell out the native colimit functors before reading identity associator components.
  change ((isoWhiskerRight (cechHomeomorphDiagramsIso h n) colim ≪≫
    Functor.associator W (D ⋙ E) colim ≪≫
    isoWhiskerLeft W (Functor.associator D E colim) ≪≫
    isoWhiskerLeft W (isoWhiskerLeft D
      (Functor.Final.colimIso (coverHomeomorphEquivalence h).functor))) :
      (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := X))
        (fun _ _ hf ↦ hf) n).flip ⋙ colim ≅ W ⋙ D ⋙ colim).hom.app P = _
  dsimp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerLeft_app, Functor.associator_hom_app]
  let α := (whiskerRight (cechHomeomorphDiagramsIso h n).hom colim).app P
  let β := (Functor.Final.colimIso (coverHomeomorphEquivalence h).functor).hom.app
    (D.obj (W.obj P))
  exact (α ≫= ((Category.id_comp _).trans (Category.id_comp β))).trans (by rfl)

/-- The transported native class of each cover is its original class followed by the comparison. -/
@[reassoc]
theorem cechCohomologyHomeomorphIso_hom_app_ι (V : PointOpenCover X) :
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app P ≫
        (cechCohomologyHomeomorphIso (A := A) h n).hom.app P =
      HomologicalComplex.homologyMap ((cechComplexHomeomorphIso (A := A) h V).hom.app P) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n
          (V.mapHomeomorph h)).app (h.opensCongr.equivalence.inverse.op ⋙ P) := by
  have hi := ι_colimMap_assoc (cechHomeomorphDiagramIso h P n).hom V
    (Functor.Final.colimitIso (coverHomeomorphEquivalence h).functor
      ((cechCohomologyDiagram A PointOpenCover.toFormalCoproduct
        (fun _ _ hf ↦ hf) n).flip.obj (h.opensCongr.equivalence.inverse.op ⋙ P))).hom
  have hf := Functor.Final.ι_colimitIso_hom (coverHomeomorphEquivalence h).functor
    ((cechCohomologyDiagram A PointOpenCover.toFormalCoproduct
      (fun _ _ hf ↦ hf) n).flip.obj (h.opensCongr.equivalence.inverse.op ⋙ P)) V
  have hd : (cechHomeomorphDiagramIso h P n).hom.app V =
      HomologicalComplex.homologyMap ((cechComplexHomeomorphIso (A := A) h V).hom.app P) n :=
    (NatIso.ofComponents_hom_app _ _ V).trans
      ((HomologicalComplex.homologyFunctor A _ n).mapIso_hom _)
  exact ((cechCohomologyι_app PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n V P) =≫ _).trans
      ((_ ≫= cechCohomologyHomeomorphIso_hom_app_eq h P n).trans
        (hi.trans ((_ ≫= hf).trans ((hd =≫ _).trans
          (_ ≫= (cechCohomologyι_app PointOpenCover.toFormalCoproduct
            (fun _ _ hf ↦ hf) n (V.mapHomeomorph h)
            (h.opensCongr.equivalence.inverse.op ⋙ P)).symm)))))

end Cohomology

section ZeroComparison

variable [CategoryWithHomology A] [HasZeroObject A]
  [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]
  (F : Sheaf (Opens.grothendieckTopology X) A)

/-- Transport through a homeomorphism preserves the native degree-zero Čech class of a
section, including the actual comparison with the transported sheaf. -/
@[reassoc]
theorem cechCohomologyZeroIso_hom_comp_cechCohomologyHomeomorphIso_hom_app_comp_map
    (F' : Sheaf (Opens.grothendieckTopology Y) A)
    (φ : h.opensCongr.equivalence.inverse.op ⋙ F.obj ⟶ F'.obj) :
    (cechCohomologyZeroIso F).hom ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj ≫
        (cechCohomology Y A 0).map φ =
      (F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤)) ≫
        (cechCohomologyZeroIso F').hom := by
  let U : PointOpenCover X := default
  have hs := cechCohomologyZeroIso_hom F U
  have ht := cechCohomologyZeroIso_hom F' (U.mapHomeomorph h)
  have hi := cechCohomologyHomeomorphIso_hom_app_ι h F.obj 0 U
  have hn : (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) 0
        (U.mapHomeomorph h)).app (h.opensCongr.equivalence.inverse.op ⋙ F.obj) ≫
        (cechCohomology Y A 0).map φ =
      HomologicalComplex.homologyMap
          ((cechComplexFunctor (U.mapHomeomorph h).opens).map φ) 0 ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) 0
          (U.mapHomeomorph h)).app F'.obj :=
    ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) 0
      (U.mapHomeomorph h)).naturality φ).symm
  have hc := cechAugmentationClass_comp_homeomorph_map_assoc h U F.obj F'.obj φ
    ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) 0
      (U.mapHomeomorph h)).app F'.obj)
  have hp := (Category.assoc _ _ _).symm.trans
    ((hi =≫ (cechCohomology Y A 0).map φ).trans
      ((Category.assoc _ _ _).trans (_ ≫= hn)))
  let c := (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
    (F.obj.obj (op ⊤))).inv
  let a := HomologicalComplex.homologyMap (cechAugmentation U.opens isTerminalTop F.obj) 0
  calc
    _ = (c ≫ a ≫ (cechCohomologyι PointOpenCover.toFormalCoproduct
          (fun _ _ hf ↦ hf) 0 U).app F.obj) ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj ≫
          (cechCohomology Y A 0).map φ := hs =≫ _
    _ = c ≫ a ≫ (HomologicalComplex.homologyMap
          ((cechComplexHomeomorphIso (A := A) h U).hom.app F.obj) 0 ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor (U.mapHomeomorph h).opens).map φ) 0 ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) 0
          (U.mapHomeomorph h)).app F'.obj) :=
      (Category.assoc _ _ _).trans
        ((_ ≫= Category.assoc _ _ _).trans (_ ≫= (_ ≫= hp)))
    _ = (F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤)) ≫
        (cechCohomologyZeroIso F').hom := hc.trans (_ ≫= ht.symm)

/-- The native degree-zero class of a section is preserved in the transported sheaf. -/
@[reassoc]
theorem cechCohomologyZeroIso_hom_comp_cechCohomologyHomeomorphIso_hom_app :
    (cechCohomologyZeroIso F).hom ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj =
      F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫
        (cechCohomologyZeroIso ((h.opensCongr.equivalence.sheafCongr
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F)).hom := by
  have hz := cechCohomologyZeroIso_hom_comp_cechCohomologyHomeomorphIso_hom_app_comp_map h F
    ((h.opensCongr.equivalence.sheafCongr
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F) (𝟙 _)
  -- Normalize the identity coefficient morphism in the native inverse-precomposed sheaf.
  let z := (cechCohomologyZeroIso F).hom
  let τ := (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj
  let Q := h.opensCongr.equivalence.inverse.op ⋙ F.obj
  let g := F.obj.map (eqToHom h.opensCongr.symm.map_top).op
  have hi := (τ ≫= (cechCohomology Y A 0).map_id Q).trans (Category.comp_id τ)
  exact ((z ≫= hi).symm.trans hz).trans
    (((g ≫= NatTrans.id_app Q (op ⊤)).trans (Category.comp_id g)) =≫ _)

variable [HasWeakSheafify (Opens.grothendieckTopology X) A]
  [HasWeakSheafify (Opens.grothendieckTopology Y) A]

/-- The existing homeomorphism comparison of global sections commutes with the native
identifications of global sections and degree-zero Čech cohomology. -/
@[reassoc]
theorem sectionsIsoCechZero_hom_comp_cechCohomologyHomeomorphIso_hom_app :
    (sectionsIsoCechZero F).hom ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj =
      (h.globalSectionsIso A).hom.app F ≫
        (sectionsIsoCechZero ((h.opensCongr.equivalence.sheafCongr
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F)).hom := by
  let F' := (h.opensCongr.equivalence.sheafCongr
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F
  have hz := cechCohomologyZeroIso_hom_comp_cechCohomologyHomeomorphIso_hom_app h F
  have hg := h.globalSectionsIso_hom_app_comp_ΓNatIsoSheafSections_hom_assoc A F
    (cechCohomologyZeroIso F').hom
  exact (sectionsIsoCechZero_hom F =≫ _).trans
    ((Category.assoc _ _ _).trans ((_ ≫= hz).trans
      ((Category.assoc _ _ _).symm.trans
        (hg.symm.trans (_ ≫= (sectionsIsoCechZero_hom F').symm)))))

end ZeroComparison

end TauCeti.Topology

namespace TauCeti.Topology

universe a b

open TauCeti.CategoryTheory

variable {A : Type a} [Category.{b} A] [Abelian A]
  {X : TopCat.{u}} {Y : TopCat.{v}} (h : X ≃ₜ Y)
  [HasProducts.{u} A] [HasProducts.{v} A] (U : PointOpenCover X)

/-- Transport of the actual Čech complex through a homeomorphism preserves short exactness. -/
theorem cechComplexHomeomorphIso_shortExact
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)}
    (hT : (T.map (cechComplexFunctor U.opens)).ShortExact) :
    ((T.map ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
      h.opensCongr.equivalence.inverse.op)).map
        (cechComplexFunctor (U.mapHomeomorph h).opens)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso
    (T.mapNatIso (cechComplexHomeomorphIso (A := A) h U))).mp hT

/-- The fixed-cover homeomorphism comparison commutes with native connecting maps. -/
@[reassoc]
theorem δ_comp_homologyMap_cechComplexHomeomorphIso_hom_app
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)}
    (hT : (T.map (cechComplexFunctor U.opens)).ShortExact) (n : ℕ) :
    hT.δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap
          ((cechComplexHomeomorphIso (A := A) h U).hom.app T.X₁) (n + 1) =
      HomologicalComplex.homologyMap
          ((cechComplexHomeomorphIso (A := A) h U).hom.app T.X₃) n ≫
        (cechComplexHomeomorphIso_shortExact h U hT).δ n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (T.mapNatTrans (cechComplexHomeomorphIso (A := A) h U).hom)
    hT (cechComplexHomeomorphIso_shortExact h U hT) n (n + 1) rfl

variable [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → X)) A]
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → Y)) A]

variable [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]

omit [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → X)) A]
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → Y)) A] in
/-- Coverwise short exactness suffices for the native connecting-map transport square. -/
@[reassoc]
theorem cechCohomologyδ_comp_cechCohomologyHomeomorphIso_hom_app_of_shortExact
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)}
    (hX : ∀ V : PointOpenCover X, (T.map (cechComplexFunctor V.opens)).ShortExact)
    (hY : ∀ V : PointOpenCover Y,
      ((T.map ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
        h.opensCongr.equivalence.inverse.op)).map (cechComplexFunctor V.opens)).ShortExact)
    (n : ℕ) :
    TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
        (fun _ _ hf ↦ hf) hX n ≫
        (cechCohomologyHomeomorphIso (A := A) h (n + 1)).hom.app T.X₁ =
      (cechCohomologyHomeomorphIso (A := A) h n).hom.app T.X₃ ≫
        TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
          (fun _ _ hf ↦ hf) hY n := by
  apply colimit.hom_ext
  intro V
  have hi := cechCohomologyι_app PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n V T.X₃
  refine (hi.symm =≫ _).trans (Eq.trans ?_ (hi =≫ _))
  have hsource := cechCohomologyι_app_δ PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) hX n V
  have hlocal := δ_comp_homologyMap_cechComplexHomeomorphIso_hom_app h V
    (hX V) n
  have htarget := cechCohomologyι_app_δ PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf)
    hY n (V.mapHomeomorph h)
  have hq₁ := cechCohomologyHomeomorphIso_hom_app_ι h T.X₁ (n + 1) V
  have hq₃ := cechCohomologyHomeomorphIso_hom_app_ι h T.X₃ n V
  have sourceSquare : CommSq _ _ _ _ := ⟨hsource⟩
  have targetSquare : CommSq _ _ _ _ := ⟨htarget⟩
  have upperSquare : CommSq _ _ _ _ := ⟨hq₃⟩
  have lowerSquare : CommSq _ _ _ _ := ⟨hq₁⟩
  exact (sourceSquare.vert_comp lowerSquare).w.trans
    ((hlocal =≫ _).trans (upperSquare.vert_comp targetSquare).w.symm)


/-- Transport through a homeomorphism commutes with native cover-colimit connecting maps. -/
@[reassoc]
theorem cechCohomologyδ_comp_cechCohomologyHomeomorphIso_hom_app
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)} (hT : T.ShortExact) (n : ℕ) :
    TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
        (fun _ _ hf ↦ hf) (fun V ↦ hT.map_of_exact (cechComplexFunctor V.opens)) n ≫
        (cechCohomologyHomeomorphIso (A := A) h (n + 1)).hom.app T.X₁ =
      (cechCohomologyHomeomorphIso (A := A) h n).hom.app T.X₃ ≫
        TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
          (fun _ _ hf ↦ hf)
          (fun V : PointOpenCover Y ↦ (hT.map_of_exact
            ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
              h.opensCongr.equivalence.inverse.op)).map_of_exact
                (cechComplexFunctor V.opens)) n :=
  cechCohomologyδ_comp_cechCohomologyHomeomorphIso_hom_app_of_shortExact h
    (fun V ↦ hT.map_of_exact (cechComplexFunctor V.opens))
    (fun V ↦ (hT.map_of_exact ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
      h.opensCongr.equivalence.inverse.op)).map_of_exact (cechComplexFunctor V.opens)) n

end TauCeti.Topology

namespace CategoryTheory.ShortComplex.ShortExact

open TauCeti.Topology TauCeti.CategoryTheory

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} R)]
  [CompactSpace X] [NormalSpace X]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective (ModuleCat.{u} R)]

/-- The native sheaf connecting map is preserved by transport through a homeomorphism. -/
@[reassoc]
theorem cechCohomologyδ_comp_cechCohomologyHomeomorphIso_hom_app
    {Y : TopCat.{u}} [CompactSpace Y] [NormalSpace Y]
    (h : X ≃ₜ Y) (hS : S.ShortExact) (n : ℕ) :
    hS.cechCohomologyδ n ≫
        (cechCohomologyHomeomorphIso (A := ModuleCat.{u} R) h (n + 1)).hom.app S.X₁.obj =
      (cechCohomologyHomeomorphIso (A := ModuleCat.{u} R) h n).hom.app S.X₃.obj ≫
        (hS.map_of_exact (h.opensCongr.equivalence.sheafCongr
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
          (ModuleCat.{u} R)).functor).cechCohomologyδ n := by
  let W := (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj
    h.opensCongr.equivalence.inverse.op
  let S' := S.map (h.opensCongr.equivalence.sheafCongr
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (ModuleCat.{u} R)).functor
  let c := cokernel.desc S.f.hom S.g.hom (S.map (sheafToPresheaf _ _)).zero
  let T := ShortComplex.mk S.f.hom (cokernel.π S.f.hom) (cokernel.condition _)
  have := hS.mono_f
  have : Mono S.f.hom := (sheafToPresheaf _ _).map_mono S.f
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel S.f.hom }
  let μ : T ⟶ S.map (sheafToPresheaf _ _) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := c
      comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (cokernel.π_desc _ _ _).symm }
  let φ : T.map W ⟶ S'.map (sheafToPresheaf _ _) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := W.map c
      comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans
        ((W.map_comp _ _).symm.trans (congrArg W.map (cokernel.π_desc _ _ _))).symm }
  have hs := hS.cechCohomologyδ_naturality_of_presheaf hT μ n
  have ht := (hS.map_of_exact _).cechCohomologyδ_naturality_of_presheaf
    (hT.map_of_exact W) φ n
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hs ht
  have : IsIso ((cechCohomology X (ModuleCat.{u} R) n).map c) := by
    have := hS.isIso_presheafToSheaf_map_cokernelDesc
    refine isIso_cechCohomology_map_of_isIso_sheafification _ ?_ ?_ n
    · exact IsZero.of_epi ((cokernel.π S.f.hom).app (Opposite.op ⊥))
        (TopCat.Sheaf.isTerminalOfEqEmpty S.X₂ rfl).isZero
    · exact (TopCat.Sheaf.isTerminalOfEqEmpty S.X₃ rfl).isZero
  have hd := TauCeti.Topology.cechCohomologyδ_comp_cechCohomologyHomeomorphIso_hom_app h hT n
  have hc := (cechCohomologyHomeomorphIso (A := ModuleCat.{u} R) h n).hom.naturality c
  dsimp only [Functor.comp_map] at hc
  apply (cancel_epi ((cechCohomology X (ModuleCat.{u} R) n).map c)).mp
  -- First transport the presheaf connecting map, then use its comparison with sheaves.
  have htransport := hd.trans (_ ≫= ht)
  exact ((Category.assoc _ _ _).symm.trans (hs.symm =≫ _)).trans
    (htransport.trans ((Category.assoc _ _ _).symm.trans (hc.symm =≫ _)))


end CategoryTheory.ShortComplex.ShortExact

namespace TauCeti.Topology

universe a b

open TauCeti.CategoryTheory

variable {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{u} A]
  {X Y : TopCat.{u}} (h : X ≃ₜ Y) (U : PointOpenCover X) (P : (Opens X)ᵒᵖ ⥤ A)

/-- The original cover refines the inverse image of its transported cover. -/
def homeomorphPullbackRefinement :
    FormalCoproduct.mk Y (fun y ↦ (Opens.map (TopCat.isoOfHomeo h).hom).obj
      ((U.mapHomeomorph h).opens y)) ⟶ U.toFormalCoproduct :=
  ⟨h.symm, fun y ↦ homOfLE (by
    change (Opens.map (TopCat.isoOfHomeo h).hom).obj ((U.mapHomeomorph h).opens y) ≤
      U.opens (h.symm y)
    rw [PointOpenCover.mapHomeomorph_opens]
    exact le_of_eq (h.opensCongr.symm_apply_apply _))⟩

/-- The inverse continuous-map pullback agrees with native transport at each cover. -/
theorem cechComplexHomeomorphIso_hom_app_comp_cechComplexPullback :
    (cechComplexHomeomorphIso (A := A) h U).hom.app P ≫
        (TopCat.isoOfHomeo h).hom.cechComplexPullback (U.mapHomeomorph h).opens
          (𝟙 ((TopCat.Presheaf.pushforward A (TopCat.isoOfHomeo h).hom).obj P)) =
      cechComplexMap P (homeomorphPullbackRefinement h U) := by
  ext n : 2
  let f := (TopCat.isoOfHomeo h).hom
  let V := (U.mapHomeomorph h).opens
  let Q : (Opens Y)ᵒᵖ ⥤ A := (TopCat.Presheaf.pushforward A f).obj P
  let B := fun y ↦ (Opens.map f).obj (V y)
  let g : (cechComplexFunctor U.opens).obj P ⟶ (cechComplexFunctor V).obj Q :=
    (cechComplexHomeomorphIso (A := A) h U).hom.app P
  let k := f.cechComplexPullback V (𝟙 Q)
  apply (cancel_mono (cechXIso B P n).hom).mp
  apply Pi.hom_ext
  intro a
  have hp : k.f n ≫ (cechXIso B P n).hom ≫ Pi.π _ a =
      Pi.π (fun b : Fin (n + 1) → Y ↦ Q.obj (op (∏ᶜ fun j ↦ V (b j)))) a ≫
        NatTrans.app (𝟙 Q) (op (∏ᶜ fun j ↦ V (a j))) ≫
        P.map (inv (piComparison (Opens.map f) (fun j ↦ V (a j)))).op :=
    (_ ≫= cechXIso_hom_π B P n a).trans
      (TopCat.Hom.cechComplexPullback_f_π f V (𝟙 Q) n a)
  rw [NatTrans.id_app, Category.id_comp] at hp
  have hg := cechComplexHomeomorphIso_hom_app_f_π h U P n a
  have hm := (_ ≫= cechXIso_hom_π B P n a).trans
    (cechComplexMap_f_π P (homeomorphPullbackRefinement h U) n a)
  have hc : P.map (homeomorphTupleComparison h U n a).op ≫
      P.map (inv (piComparison (Opens.map f) (fun j ↦ V (a j)))).op =
      P.map (Limits.Pi.map (fun j ↦ (homeomorphPullbackRefinement h U).φ (a j))).op :=
    (P.map_comp _ _).symm.trans (congrArg P.map (Subsingleton.elim _ _))
  have htuples := ((Category.assoc _ _ _).symm.trans (hg =≫ _)).trans
    ((Category.assoc _ _ _).trans (_ ≫= hc))
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun z ↦ z ≫ (cechXIso B P n).hom ≫ Pi.π _ a)
      (HomologicalComplex.comp_f g k n))).trans
    ((Category.assoc _ _ _).trans ((g.f n ≫= hp).trans
      (htuples.trans (hm.symm.trans (Category.assoc _ _ _).symm))))


variable [CategoryWithHomology A] [HasColimitsOfShape (PointOpenCover X) A]
  [HasColimitsOfShape (PointOpenCover Y) A] (n : ℕ)

/-- In the same base universe the inverse is exactly native continuous-map pullback. -/
theorem cechCohomologyHomeomorphIso_inv_app_eq_pullback :
    (cechCohomologyHomeomorphIso (A := A) h n).inv.app P =
      (TopCat.isoOfHomeo h).hom.cechCohomologyPullback n
        (𝟙 ((TopCat.Presheaf.pushforward A (TopCat.isoOfHomeo h).hom).obj P)) := by
  apply (cancel_epi ((cechCohomologyHomeomorphIso (A := A) h n).hom.app P)).mp
  rw [Iso.hom_inv_id_app]
  symm
  apply cechCohomology_obj_hom_ext
  intro U
  let f := (TopCat.isoOfHomeo h).hom
  let V := U.mapHomeomorph h
  let Q : (Opens Y)ᵒᵖ ⥤ A := (TopCat.Presheaf.pushforward A f).obj P
  let B := fun y ↦ (Opens.map f).obj (V.opens y)
  have hi := cechCohomologyHomeomorphIso_hom_app_ι h P n U
  have hp := f.toCechCohomology_app_comp_cechCohomologyPullback n (𝟙 Q)
    V.opens V.isOpenCover
  have hι := congrArg (fun α ↦ α.app Q) (toCechCohomology_opens A n V)
  have hcomp := (HomologicalComplex.homologyMap_comp
    ((cechComplexHomeomorphIso (A := A) h U).hom.app P)
    (f.cechComplexPullback V.opens (𝟙 Q)) n).symm.trans
      (congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
        (cechComplexHomeomorphIso_hom_app_comp_cechComplexPullback h U P))
  have hr := homologyMap_cechComplexMap_comp_toCechCohomology_app A n
    (homeomorphPullbackRefinement h U) U.isOpenCover (V.isOpenCover.comap f.hom) P
  have hx := congrArg (fun α ↦ α.app P) (toCechCohomology_opens A n U)
  calc
    _ = HomologicalComplex.homologyMap
        ((cechComplexHomeomorphIso (A := A) h U).hom.app P) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app Q ≫
          f.cechCohomologyPullback n (𝟙 Q) :=
      (Category.assoc _ _ _).symm.trans ((hi =≫ _).trans (Category.assoc _ _ _))
    _ = HomologicalComplex.homologyMap
        ((cechComplexHomeomorphIso (A := A) h U).hom.app P) n ≫
        HomologicalComplex.homologyMap (f.cechComplexPullback V.opens (𝟙 Q)) n ≫
          (toCechCohomology A n B (V.isOpenCover.comap f.hom)).app P :=
      _ ≫= ((hι.symm =≫ _).trans hp)
    _ = HomologicalComplex.homologyMap (cechComplexMap P (homeomorphPullbackRefinement h U)) n ≫
        (toCechCohomology A n B (V.isOpenCover.comap f.hom)).app P :=
      (Category.assoc _ _ _).symm.trans (hcomp =≫ _)
    _ = (toCechCohomology A n U.opens U.isOpenCover).app P := hr
    _ = _ := hx.trans (Category.comp_id _).symm

end TauCeti.Topology
