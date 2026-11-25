/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Final
public import TauCeti.CategoryTheory.EqToHom
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.LongExactSequence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Reindex
public import TauCeti.Topology.Sheaves.Cech.Colimit
public import TauCeti.Topology.Sheaves.Cech.Functoriality
public import TauCeti.Topology.Sheaves.Cech.LongExactSequence
public import TauCeti.Topology.Sheaves.Homeomorph

/-!
# Čech cohomology under a homeomorphism

Homeomorphisms transport point-neighborhood covers and Čech cohomology across base universes.
`cechComplexIso` gives tuple-complex hom and inverse component laws;
`cechCohomologyIso` preserves cover-colimit cohomology, augmentation, refinement,
degree-zero global sections and connecting maps.
-/

public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.Topology
open CategoryTheory.Functor

universe u v

namespace Homeomorph

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

/-- Transport along a homeomorphism naturally identifies the Čech complex of a cover with that
of the transported cover and inverse-image presheaf, even across different base universes. -/
def cechComplexIso :
    cechComplexFunctor.{u} (A := A) U.opens ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
          h.opensCongr.equivalence.inverse.op ⋙
        cechComplexFunctor.{v} (U.mapHomeomorph h).opens :=
  (Equiv.cechComplexReindexIso h.symm.toEquiv U.opens).symm ≪≫
    (eqToIso (congrArg (fun V : Y → Opens X ↦ cechComplexFunctor (A := A) V)
      (inverseOpens_mapHomeomorph h U).symm)) ≪≫
    NatIso.ofComponents (fun P ↦
      cechComplexCompIso h.opensCongr.equivalence.inverse (U.mapHomeomorph h).opens P
        (fun _ _ ↦ inferInstance))
      (fun φ ↦ cechComplexFunctor_map_comp_cechComplexCompIso_hom
        h.opensCongr.equivalence.inverse (U.mapHomeomorph h).opens _
        (fun _ _ ↦ inferInstance) φ)

/-- The inverse image of a finite intersection maps to the intersection of inverse images. -/
def cechTupleComparison (n : ℕ) (a : Fin (n + 1) → Y) :
    h.opensCongr.equivalence.inverse.obj (∏ᶜ fun j ↦ (U.mapHomeomorph h).opens (a j)) ⟶
      ∏ᶜ fun j ↦ U.opens (h.symm (a j)) :=
  (piComparison h.opensCongr.equivalence.inverse
    (fun j ↦ (U.mapHomeomorph h).opens (a j))) ≫
      eqToHom (congrArg (fun V ↦ ∏ᶜ fun j ↦ V (a j)) (inverseOpens_mapHomeomorph h U))

/-- Inverse-image transport preserves finite intersections. -/
instance cechTupleComparison_isIso (n : ℕ) (a : Fin (n + 1) → Y) :
    IsIso (h.cechTupleComparison U n a) := by
  -- The first factor is the native product comparison of the opens equivalence.
  change IsIso (piComparison h.opensCongr.equivalence.inverse
    (fun j ↦ (U.mapHomeomorph h).opens (a j)) ≫ _)
  infer_instance

private lemma cechComplexIso_hom_app_f_commSq (n : ℕ) (a : Fin (n + 1) → Y) :
    CommSq (((h.cechComplexIso (A := A) U).hom.app P).f n)
      ((cechXIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a))
      ((cechXIso (U.mapHomeomorph h).opens (h.opensCongr.equivalence.inverse.op ⋙ P) n).hom ≫
        Pi.π _ a) (P.map (h.cechTupleComparison U n a).op) := by
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
  have hi : ((Equiv.cechComplexReindexIso h.symm.toEquiv U.opens).inv.app P).f n ≫
      (cechXIso (U.opens ∘ h.symm.toEquiv) P n).hom ≫ Pi.π _ a =
      (cechXIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a) :=
    (_ ≫= cechXIso_hom_π _ P n a).trans
      ((Equiv.cechComplexReindexIso_inv_app_f_π h.symm.toEquiv U.opens P n a).trans
        (cechXIso_hom_π U.opens P n (h.symm.toEquiv ∘ a)).symm)
  have hr : ((h.cechComplexIso (A := A) U).hom.app P).f n ≫
      (cechXIso V (G.op ⋙ P) n).hom ≫ Pi.π _ a =
      (cechXIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a) ≫
        P.map (h.cechTupleComparison U n a).op := by
    dsimp only [G, V] at hc
    simp only [cechComplexIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      NatIso.ofComponents_hom_app, HomologicalComplex.comp_f, Category.assoc]
    rw [hc, cechComplex_eqToIso_hom_app_f_π_assoc P (U.opens ∘ h.symm.toEquiv)
      (fun y ↦ G.obj (V y)) (inverseOpens_mapHomeomorph h U).symm n a,
      reassoc_of% hi]
    simp only [cechTupleComparison, piComparison, op_comp, Functor.map_comp]
  exact ⟨hr.trans (Category.assoc _ _ _).symm⟩

/-- The tuple-reading square holds for any original tuple equal to `h.symm ∘ a`, with
transport along that equality appended to the product restriction. -/
theorem cechComplexIso_hom_app_f_commSq_of_eq (n : ℕ) (a : Fin (n + 1) → Y)
    (b : Fin (n + 1) → X) (q : b = h.symm.toEquiv ∘ a) :
    CommSq (((h.cechComplexIso (A := A) U).hom.app P).f n)
      ((cechXIso U.opens P n).hom ≫ Pi.π _ b)
      ((cechXIso (U.mapHomeomorph h).opens (h.opensCongr.equivalence.inverse.op ⋙ P) n).hom ≫
        Pi.π _ a) (P.map (h.cechTupleComparison U n a ≫
          eqToHom (congrArg (fun b ↦ ∏ᶜ fun j ↦ U.opens (b j)) q.symm)).op) := by
  subst b
  simpa only [eqToHom_refl, Category.comp_id] using
    (cechComplexIso_hom_app_f_commSq h U P n a)

/-- The native component reads a transported tuple by the corresponding original tuple. -/
@[reassoc]
theorem cechComplexIso_hom_app_f_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((h.cechComplexIso (A := A) U).hom.app P).f n ≫ Pi.π _ a =
      Pi.π _ (h.symm.toEquiv ∘ a) ≫ P.map (h.cechTupleComparison U n a).op := by
  exact (_ ≫= (cechXIso_hom_π (U.mapHomeomorph h).opens
      (h.opensCongr.equivalence.inverse.op ⋙ P) n a).symm).trans
    (((cechComplexIso_hom_app_f_commSq h U P n a).w.trans (Category.assoc _ _ _)).trans
      (cechXIso_hom_π_assoc U.opens P n (h.symm.toEquiv ∘ a) _))

/-- The inverse component reads each original tuple through the inverse open comparison. -/
@[reassoc]
theorem cechComplexIso_inv_app_f_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((h.cechComplexIso (A := A) U).inv.app P).f n ≫
        Pi.π _ (h.symm.toEquiv ∘ a) =
      Pi.π _ a ≫ P.map (inv (h.cechTupleComparison U n a)).op := by
  apply (Iso.eq_comp_inv (P.mapIso (asIso (h.cechTupleComparison U n a)).op)).mpr
  let j := (HomologicalComplex.eval A (ComplexShape.up ℕ) n).mapIso
    ((h.cechComplexIso (A := A) U).app P)
  have hread := j.inv ≫= cechComplexIso_hom_app_f_π h U P n a
  exact (Category.assoc _ _ _).trans (hread.symm.trans (j.inv_hom_id_assoc _))

/-- Transport through a homeomorphism preserves restriction of a global section to its cover. -/
@[reassoc]
theorem cechAugmentation_comp_cechComplexIso_hom_app [HasZeroObject A] :
    cechAugmentation U.opens isTerminalTop P ≫
        (h.cechComplexIso (A := A) U).hom.app P =
      (CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op) ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop
          (h.opensCongr.equivalence.inverse.op ⋙ P) := by
  let G := h.opensCongr.equivalence.inverse
  let B := fun y ↦ G.obj ((U.mapHomeomorph h).opens y)
  let r := Equiv.cechComplexReindexIso (A := A) h.symm.toEquiv U.opens
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
  have hr := (Iso.eq_comp_inv (r.app P)).mpr
    (Equiv.cechAugmentation_comp_cechComplexReindexIso_hom_app
      h.symm.toEquiv U.opens P isTerminalTop)
  have hc := cechAugmentation_comp_cechComplexCompIso_hom G (U.mapHomeomorph h).opens P
    (fun _ _ ↦ inferInstance) isTerminalTop hGT
  -- Unfold Iso.trans and NatIso.ofComponents to read the composite as r⁻¹ ≫ q ≫ c.
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
        (P.cechAugmentation_comp_cechComplex_eqToIso_hom_app _ _
          (inverseOpens_mapHomeomorph h U).symm isTerminalTop =≫ _)
    _ = ((CochainComplex.single₀ A).map α ≫ cechAugmentation B hGT P) ≫ c.hom := ht.symm =≫ _
    _ = (CochainComplex.single₀ A).map α ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop (G.op ⋙ P) :=
      (Category.assoc _ _ _).trans (_ ≫= hc)

private lemma cechAugmentation_comp_homeomorph_map [HasZeroObject A]
    (Q : (Opens Y)ᵒᵖ ⥤ A)
    (φ : h.opensCongr.equivalence.inverse.op ⋙ P ⟶ Q) :
    cechAugmentation U.opens isTerminalTop P ≫
        (h.cechComplexIso (A := A) U).hom.app P ≫
        (cechComplexFunctor (U.mapHomeomorph h).opens).map φ =
      (CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤)) ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop Q := by
  -- The native restriction lands in the top-open value of inverse precomposition.
  let α : P.obj (op ⊤) ⟶ (h.opensCongr.equivalence.inverse.op ⋙ P).obj (op ⊤) :=
    P.map (eqToHom h.opensCongr.symm.map_top).op
  have hs : CommSq _ _ _ _ :=
    ⟨cechAugmentation_comp_cechComplexIso_hom_app h U P⟩
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
          ((h.cechComplexIso (A := A) U).hom.app P) 0 ≫
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
theorem cechComplexMap_comp_cechComplexIso_hom_app {V : PointOpenCover X}
    (φ : U.toFormalCoproduct ⟶ V.toFormalCoproduct) :
    cechComplexMap.{u, u, b, u, a} (U := U.opens) (V := V.opens) P φ ≫
        (h.cechComplexIso (A := A) U).hom.app P =
      (cechComplexIso (A := A) h V).hom.app P ≫
        cechComplexMap.{v, v, b, v, a}
          (U := (U.mapHomeomorph h).opens) (V := (V.mapHomeomorph h).opens)
          (h.opensCongr.equivalence.inverse.op ⋙ P) (U.mapHomeomorphHom h φ) := by
  let G := h.opensCongr.equivalence.inverse
  let ψ := U.mapHomeomorphHom h φ
  let r (T : PointOpenCover X) :
      cechComplexFunctor.{v} (A := A) (fun y ↦ G.obj ((T.mapHomeomorph h).opens y)) ≅
        cechComplexFunctor.{u} (A := A) T.opens :=
    eqToIso (congrArg (cechComplexFunctor.{v} (A := A))
      (inverseOpens_mapHomeomorph h T)) ≪≫ Equiv.cechComplexReindexIso h.symm.toEquiv T.opens
  let ψG : FormalCoproduct.mk Y (fun y ↦ G.obj ((U.mapHomeomorph h).opens y)) ⟶
      FormalCoproduct.mk Y (fun y ↦ G.obj ((V.mapHomeomorph h).opens y)) :=
    ⟨ψ.f, fun y ↦ G.map (ψ.φ y)⟩
  have hf : φ.f ∘ h.symm.toEquiv = h.symm.toEquiv ∘ ψG.f := by
    funext y
    simp [ψG, ψ, PointOpenCover.mapHomeomorphHom_f]
  have hr := Equiv.cechComplexMap_comp_cechComplexReindexIso_hom_app (A := A)
    h.symm.toEquiv U.opens P
    h.symm.toEquiv V.opens _ _ (inverseOpens_mapHomeomorph h U)
    (inverseOpens_mapHomeomorph h V) φ ψG hf (fun _ ↦ Subsingleton.elim _ _)
  have hs : CommSq ((r V).app P).hom (cechComplexMap.{v, u, b, u, a} P ψG)
      (cechComplexMap.{u, u, b, u, a} P φ) ((r U).app P).hom := ⟨hr.symm⟩
  have hc := cechComplexMap_comp_cechComplexCompIso_hom G (U.mapHomeomorph h).opens P
    (fun _ _ ↦ inferInstance) ψ (fun _ _ ↦ inferInstance)
  have hw := (hs.horiz_inv.horiz_comp ⟨hc.symm⟩).w.symm
  simpa only [r, G, ψ, Iso.app_inv, Iso.trans_inv, NatTrans.comp_app,
    cechComplexIso, Iso.trans_hom, Iso.symm_hom,
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
        ((PointOpenCover.mapHomeomorph_le_mapHomeomorph_iff _ _ h).mpr (leOfHom f)) }
  (h.pointOpenCoverOrderIso).equivalence.changeFunctor
    (NatIso.ofComponents (fun U ↦ eqToIso (by
      simp only [OrderIso.equivalence_functor, Monotone.functor_obj,
        Homeomorph.pointOpenCoverOrderIso_apply, G])) (fun _ ↦ Subsingleton.elim _ _)
      : (h.pointOpenCoverOrderIso).equivalence.functor ≅ G)

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
      ((h.cechComplexIso (A := A) U).app P)) ?_
  intro U V f
  let φ := (leOfHom f).some
  let ψ := V.mapHomeomorphHom h φ
  dsimp only [Functor.flip_obj_map, Functor.comp_map]
  rw [cechCohomologyDiagram_map A (PointOpenCover.toFormalCoproduct (X := X))
    (fun _ _ hf ↦ hf) n f φ,
    cechCohomologyDiagram_map A (PointOpenCover.toFormalCoproduct (X := Y)) (fun _ _ hf ↦ hf) n
      ((coverHomeomorphEquivalence h).functor.map f) ψ]
  have hc := congrArg ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n).map)
    (cechComplexMap_comp_cechComplexIso_hom_app h V P φ)
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
  exact (Functor.isoWhiskerRight (h.cechComplexIso (A := A) U)
    (HomologicalComplex.homologyFunctor A _ n)).hom.naturality φ

/-- Native cover-colimit Čech cohomology is preserved by a homeomorphism across universes. -/
def cechCohomologyIso :
    cechCohomology X A n ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
        h.opensCongr.equivalence.inverse.op ⋙ cechCohomology Y A n :=
  isoWhiskerRight (cechHomeomorphDiagramsIso h n) colim ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (Functor.Final.colimIso (coverHomeomorphEquivalence h).functor))

/-- Read the native colimit map underlying the transport comparison. -/
private lemma cechCohomologyIso_hom_app_eq :
    (h.cechCohomologyIso (A := A) n).hom.app P =
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
theorem cechCohomologyIso_hom_app_ι (V : PointOpenCover X) :
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app P ≫
        (h.cechCohomologyIso (A := A) n).hom.app P =
      HomologicalComplex.homologyMap ((cechComplexIso (A := A) h V).hom.app P) n ≫
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
      HomologicalComplex.homologyMap ((cechComplexIso (A := A) h V).hom.app P) n :=
    (NatIso.ofComponents_hom_app _ _ V).trans
      ((HomologicalComplex.homologyFunctor A _ n).mapIso_hom _)
  exact ((cechCohomologyι_app PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n V P) =≫ _).trans
      ((_ ≫= cechCohomologyIso_hom_app_eq h P n).trans
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
theorem cechCohomologyZeroIso_hom_comp_cechCohomologyIso_hom_app_comp_map
    (F' : Sheaf (Opens.grothendieckTopology Y) A)
    (φ : h.opensCongr.equivalence.inverse.op ⋙ F.obj ⟶ F'.obj) :
    (cechCohomologyZeroIso F).hom ≫
        (h.cechCohomologyIso (A := A) 0).hom.app F.obj ≫
        (cechCohomology Y A 0).map φ =
      (F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤)) ≫
        (cechCohomologyZeroIso F').hom := by
  let U : PointOpenCover X := default
  have hs := cechCohomologyZeroIso_hom F U
  have ht := cechCohomologyZeroIso_hom F' (U.mapHomeomorph h)
  have hi := cechCohomologyIso_hom_app_ι h F.obj 0 U
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
  have hp := ((reassoc_of% hi) ((cechCohomology Y A 0).map φ)).trans
    ((Category.assoc _ _ _).trans
      (HomologicalComplex.homologyMap
        ((h.cechComplexIso (A := A) U).hom.app F.obj) 0 ≫= hn))
  let c := (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
    (F.obj.obj (op ⊤))).inv
  let a := HomologicalComplex.homologyMap (cechAugmentation U.opens isTerminalTop F.obj) 0
  calc
    _ = (c ≫ a ≫ (cechCohomologyι PointOpenCover.toFormalCoproduct
          (fun _ _ hf ↦ hf) 0 U).app F.obj) ≫
        (h.cechCohomologyIso (A := A) 0).hom.app F.obj ≫
          (cechCohomology Y A 0).map φ := hs =≫ _
    _ = c ≫ a ≫ (HomologicalComplex.homologyMap
          ((h.cechComplexIso (A := A) U).hom.app F.obj) 0 ≫
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
theorem cechCohomologyZeroIso_hom_comp_cechCohomologyIso_hom_app :
    (cechCohomologyZeroIso F).hom ≫
        (h.cechCohomologyIso (A := A) 0).hom.app F.obj =
      F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫
        (cechCohomologyZeroIso ((h.opensCongr.equivalence.sheafCongr
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F)).hom := by
  have hz := cechCohomologyZeroIso_hom_comp_cechCohomologyIso_hom_app_comp_map h F
    ((h.opensCongr.equivalence.sheafCongr
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F) (𝟙 _)
  -- These typed identity equations avoid rewriting through the protected colimit functor.
  let z := (cechCohomologyZeroIso F).hom
  let τ := (h.cechCohomologyIso (A := A) 0).hom.app F.obj
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
theorem sectionsIsoCechZero_hom_comp_cechCohomologyIso_hom_app :
    (sectionsIsoCechZero F).hom ≫
        (h.cechCohomologyIso (A := A) 0).hom.app F.obj =
      (h.globalSectionsIso A).hom.app F ≫
        (sectionsIsoCechZero ((h.opensCongr.equivalence.sheafCongr
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) A).functor.obj F)).hom := by
  have hz := cechCohomologyZeroIso_hom_comp_cechCohomologyIso_hom_app h F
  simp only [sectionsIsoCechZero_hom, Category.assoc, hz,
    globalSectionsIso_hom_app_comp_ΓNatIsoSheafSections_hom_assoc]
  exact (Category.assoc _ _ _).symm

end ZeroComparison

end Homeomorph

namespace Homeomorph

universe a b

open TauCeti.CategoryTheory

variable {A : Type a} [Category.{b} A] [Abelian A]
  {X : TopCat.{u}} {Y : TopCat.{v}} (h : X ≃ₜ Y)
  [HasProducts.{u} A] [HasProducts.{v} A] (U : PointOpenCover X)

/-- Transport of the actual Čech complex through a homeomorphism preserves short exactness. -/
theorem cechComplexIso_shortExact
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)}
    (hT : (T.map (cechComplexFunctor U.opens)).ShortExact) :
    ((T.map ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
      h.opensCongr.equivalence.inverse.op)).map
        (cechComplexFunctor (U.mapHomeomorph h).opens)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso
    (T.mapNatIso (h.cechComplexIso (A := A) U))).mp hT

/-- The fixed-cover homeomorphism comparison commutes with native connecting maps. -/
@[reassoc]
theorem δ_comp_homologyMap_cechComplexIso_hom_app
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)}
    (hT : (T.map (cechComplexFunctor U.opens)).ShortExact) (n : ℕ) :
    hT.δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap
          ((h.cechComplexIso (A := A) U).hom.app T.X₁) (n + 1) =
      HomologicalComplex.homologyMap
          ((h.cechComplexIso (A := A) U).hom.app T.X₃) n ≫
        (cechComplexIso_shortExact h U hT).δ n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (T.mapNatTrans (h.cechComplexIso (A := A) U).hom)
    hT (cechComplexIso_shortExact h U hT) n (n + 1) rfl

/-- Exactness on all source covers supplies exactness on every target cover by transporting
its inverse-image cover through the actual homeomorphism comparison. -/
theorem cechComplexIso_shortExact_of_forall
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)}
    (hX : ∀ V : PointOpenCover X, (T.map (cechComplexFunctor V.opens)).ShortExact)
    (V : PointOpenCover Y) :
    ((T.map ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
      h.opensCongr.equivalence.inverse.op)).map (cechComplexFunctor V.opens)).ShortExact := by
  have ht := cechComplexIso_shortExact h (V.mapHomeomorph h.symm) (hX _)
  exact Eq.mp (congrArg (fun V : PointOpenCover Y ↦
    ((T.map ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
      h.opensCongr.equivalence.inverse.op)).map (cechComplexFunctor V.opens)).ShortExact)
    (PointOpenCover.mapHomeomorph_symm_mapHomeomorph V h.symm)) ht

variable [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → X)) A]

variable [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]

omit [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → X)) A] in
/-- Coverwise short exactness suffices for the native connecting-map transport square. -/
@[reassoc]
theorem cechCohomologyδ_comp_cechCohomologyIso_hom_app_of_forall_shortExact
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)}
    (hX : ∀ V : PointOpenCover X, (T.map (cechComplexFunctor V.opens)).ShortExact)
    (n : ℕ) :
    TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
        (fun _ _ hf ↦ hf) hX n ≫
        (h.cechCohomologyIso (A := A) (n + 1)).hom.app T.X₁ =
      (h.cechCohomologyIso (A := A) n).hom.app T.X₃ ≫
        TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
          (fun _ _ hf ↦ hf) (cechComplexIso_shortExact_of_forall h hX) n := by
  apply colimit.hom_ext
  intro V
  have hi := cechCohomologyι_app PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n V T.X₃
  refine (hi.symm =≫ _).trans (Eq.trans ?_ (hi =≫ _))
  have hsource := cechCohomologyι_app_δ PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) hX n V
  have hlocal := δ_comp_homologyMap_cechComplexIso_hom_app h V
    (hX V) n
  have htarget := cechCohomologyι_app_δ PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf)
    (cechComplexIso_shortExact_of_forall h hX) n (V.mapHomeomorph h)
  have hq₁ := cechCohomologyIso_hom_app_ι h T.X₁ (n + 1) V
  have hq₃ := cechCohomologyIso_hom_app_ι h T.X₃ n V
  have sourceSquare : CommSq _ _ _ _ := ⟨hsource⟩
  have targetSquare : CommSq _ _ _ _ := ⟨htarget⟩
  have upperSquare : CommSq _ _ _ _ := ⟨hq₃⟩
  have lowerSquare : CommSq _ _ _ _ := ⟨hq₁⟩
  exact (sourceSquare.vert_comp lowerSquare).w.trans
    ((hlocal =≫ _).trans (upperSquare.vert_comp targetSquare).w.symm)

/-- Transport through a homeomorphism commutes with native cover-colimit connecting maps.
Exact products are required only on the source: every target cover is transported from one. -/
@[reassoc]
theorem cechCohomologyδ_comp_cechCohomologyIso_hom_app
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ A)} (hT : T.ShortExact) (n : ℕ) :
    TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
        (fun _ _ hf ↦ hf) (fun V ↦ hT.map_of_exact (cechComplexFunctor V.opens)) n ≫
        (h.cechCohomologyIso (A := A) (n + 1)).hom.app T.X₁ =
      (h.cechCohomologyIso (A := A) n).hom.app T.X₃ ≫
        TauCeti.CategoryTheory.cechCohomologyδ PointOpenCover.toFormalCoproduct
          (fun _ _ hf ↦ hf) (cechComplexIso_shortExact_of_forall h
            (fun V ↦ hT.map_of_exact (cechComplexFunctor V.opens))) n :=
  cechCohomologyδ_comp_cechCohomologyIso_hom_app_of_forall_shortExact h
    (fun V ↦ hT.map_of_exact (cechComplexFunctor V.opens)) n

end Homeomorph

namespace CategoryTheory.ShortComplex.ShortExact

open TauCeti.Topology TauCeti.CategoryTheory Homeomorph

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} R)]
  [CompactSpace X] [NormalSpace X]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective (ModuleCat.{u} R)]

/-- The native sheaf connecting map is preserved by transport through a homeomorphism. -/
@[reassoc]
theorem cechCohomologyδ_comp_cechCohomologyIso_hom_app
    {Y : TopCat.{u}} [CompactSpace Y] [NormalSpace Y]
    (hS : S.ShortExact) (h : X ≃ₜ Y) (n : ℕ) :
    hS.cechCohomologyδ n ≫
        (cechCohomologyIso (A := ModuleCat.{u} R) h (n + 1)).hom.app S.X₁.obj =
      (cechCohomologyIso (A := ModuleCat.{u} R) h n).hom.app S.X₃.obj ≫
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
  -- sheafCongr's underlying presheaf is definitionally inverse.op ⋙ S.Xᵢ.obj.
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hs ht
  have : IsIso ((cechCohomology X (ModuleCat.{u} R) n).map c) := by
    have := hS.isIso_presheafToSheaf_map_cokernelDesc
    refine isIso_cechCohomology_map_of_isIso_sheafification _ ?_ ?_ n
    · exact IsZero.of_epi ((cokernel.π S.f.hom).app (Opposite.op ⊥))
        (TopCat.Sheaf.isTerminalOfEqEmpty S.X₂ rfl).isZero
    · exact (TopCat.Sheaf.isTerminalOfEqEmpty S.X₃ rfl).isZero
  have hd := Homeomorph.cechCohomologyδ_comp_cechCohomologyIso_hom_app h hT n
  have hc := (cechCohomologyIso (A := ModuleCat.{u} R) h n).hom.naturality c
  dsimp only [Functor.comp_map] at hc
  apply (cancel_epi ((cechCohomology X (ModuleCat.{u} R) n).map c)).mp
  -- First transport the presheaf connecting map, then use its comparison with sheaves.
  have htransport := hd.trans (_ ≫= ht)
  exact ((reassoc_of% hs.symm) _).trans
    (htransport.trans ((reassoc_of% hc.symm) _))

end CategoryTheory.ShortComplex.ShortExact

namespace Homeomorph

universe a b

open TauCeti.CategoryTheory

variable {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{u} A]
  {X Y : TopCat.{u}} (h : X ≃ₜ Y) (U : PointOpenCover X) (P : (Opens X)ᵒᵖ ⥤ A)

/-- The original cover refines the inverse image of its transported cover. -/
def cechPullbackRefinement :
    FormalCoproduct.mk Y (fun y ↦ (Opens.map (TopCat.isoOfHomeo h).hom).obj
      ((U.mapHomeomorph h).opens y)) ⟶ U.toFormalCoproduct :=
  ⟨h.symm, fun y ↦ homOfLE (by
    -- FormalCoproduct.mk/toFormalCoproduct reduce the component goal to an Opens inclusion.
    change (Opens.map (TopCat.isoOfHomeo h).hom).obj ((U.mapHomeomorph h).opens y) ≤
      U.opens (h.symm y)
    rw [PointOpenCover.mapHomeomorph_opens]
    exact le_of_eq (h.opensCongr.symm_apply_apply _))⟩

/-- The actual refinement reads a transported point at its inverse image. -/
@[simp]
theorem cechPullbackRefinement_f (y : Y) : (h.cechPullbackRefinement U).f y = h.symm y := by
  rfl

/-- Native transport followed by continuous-map pullback is the actual refinement map
from the preimage of the transported cover to the original cover. -/
theorem cechComplexIso_hom_app_comp_cechComplexPullback :
    (h.cechComplexIso (A := A) U).hom.app P ≫
        (TopCat.isoOfHomeo h).hom.cechComplexPullback (U.mapHomeomorph h).opens
          (𝟙 ((TopCat.Presheaf.pushforward A (TopCat.isoOfHomeo h).hom).obj P)) =
      cechComplexMap P (h.cechPullbackRefinement U) := by
  ext n : 2
  let f := (TopCat.isoOfHomeo h).hom
  let V := (U.mapHomeomorph h).opens
  let Q : (Opens Y)ᵒᵖ ⥤ A := (TopCat.Presheaf.pushforward A f).obj P
  let B := fun y ↦ (Opens.map f).obj (V y)
  let g : (cechComplexFunctor U.opens).obj P ⟶ (cechComplexFunctor V).obj Q :=
    (h.cechComplexIso (A := A) U).hom.app P
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
  have hg := cechComplexIso_hom_app_f_π h U P n a
  have hm := (_ ≫= cechXIso_hom_π B P n a).trans
    (cechComplexMap_f_π P (h.cechPullbackRefinement U) n a)
  have hc : P.map (h.cechTupleComparison U n a).op ≫
      P.map (inv (piComparison (Opens.map f) (fun j ↦ V (a j)))).op =
      P.map (Limits.Pi.map (fun j ↦ (h.cechPullbackRefinement U).φ (a j))).op :=
    (P.map_comp _ _).symm.trans (congrArg P.map (Subsingleton.elim _ _))
  -- The formal-coproduct fiber needs this typed transport before reassociation.
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
theorem cechCohomologyIso_inv_app_eq_cechCohomologyPullback :
    (h.cechCohomologyIso (A := A) n).inv.app P =
      (TopCat.isoOfHomeo h).hom.cechCohomologyPullback n
        (𝟙 ((TopCat.Presheaf.pushforward A (TopCat.isoOfHomeo h).hom).obj P)) := by
  apply (cancel_epi ((h.cechCohomologyIso (A := A) n).hom.app P)).mp
  rw [Iso.hom_inv_id_app]
  symm
  apply cechCohomology_obj_hom_ext
  intro U
  let f := (TopCat.isoOfHomeo h).hom
  let V := U.mapHomeomorph h
  let Q : (Opens Y)ᵒᵖ ⥤ A := (TopCat.Presheaf.pushforward A f).obj P
  let B := fun y ↦ (Opens.map f).obj (V.opens y)
  have hi := cechCohomologyIso_hom_app_ι h P n U
  have hp := f.toCechCohomology_app_comp_cechCohomologyPullback n (𝟙 Q)
    V.opens V.isOpenCover
  have hι := congrArg (fun α ↦ α.app Q) (toCechCohomology_opens A n V)
  have hcomp := (HomologicalComplex.homologyMap_comp
    ((h.cechComplexIso (A := A) U).hom.app P)
    (f.cechComplexPullback V.opens (𝟙 Q)) n).symm.trans
      (congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
        (cechComplexIso_hom_app_comp_cechComplexPullback h U P))
  have hr := homologyMap_cechComplexMap_comp_toCechCohomology_app A n
    (h.cechPullbackRefinement U) U.isOpenCover (V.isOpenCover.comap f.hom) P
  have hx := congrArg (fun α ↦ α.app P) (toCechCohomology_opens A n U)
  calc
    _ = HomologicalComplex.homologyMap
        ((h.cechComplexIso (A := A) U).hom.app P) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app Q ≫
          f.cechCohomologyPullback n (𝟙 Q) :=
      -- Keep this typed colimit-comparison association; its wrappers are not simp-exposed.
      (Category.assoc _ _ _).symm.trans ((hi =≫ _).trans (Category.assoc _ _ _))
    _ = HomologicalComplex.homologyMap
        ((h.cechComplexIso (A := A) U).hom.app P) n ≫
        HomologicalComplex.homologyMap (f.cechComplexPullback V.opens (𝟙 Q)) n ≫
          (toCechCohomology A n B (V.isOpenCover.comap f.hom)).app P :=
      _ ≫= ((hι.symm =≫ _).trans hp)
    _ = HomologicalComplex.homologyMap (cechComplexMap P (h.cechPullbackRefinement U)) n ≫
        (toCechCohomology A n B (V.isOpenCover.comap f.hom)).app P :=
      (Category.assoc _ _ _).symm.trans (hcomp =≫ _)
    _ = (toCechCohomology A n U.opens U.isOpenCover).app P := hr
    _ = _ := by simpa only [Category.comp_id] using hx

end Homeomorph

namespace Homeomorph

universe u₁ u₂ u₃ a₁ b₁

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.Topology TauCeti.CategoryTheory

variable {A : Type a₁} [Category.{b₁} A] [Preadditive A]
  {X : TopCat.{u₁}} {Y : TopCat.{u₂}} {Z : TopCat.{u₃}}
  [HasProducts.{u₁} A] [HasProducts.{u₂} A] [HasProducts.{u₃} A]

omit [HasProducts.{u₂} A] [HasProducts.{u₃} A] in
/-- The component at `P` of identity transport, followed by the cover equality and the unit
identification of the precomposed presheaf, is the identity. -/
private lemma cechComplexIso_refl_hom_app_comp (U : PointOpenCover X)
    (P : (Opens X)ᵒᵖ ⥤ A) :
    ((Homeomorph.refl X).cechComplexIso (A := A) U).hom.app P ≫
      (eqToIso (congrArg (fun V : PointOpenCover X ↦ cechComplexFunctor.{u₁} (A := A) V.opens)
        (PointOpenCover.mapHomeomorph_refl U))).hom.app
          ((Homeomorph.refl X).opensCongr.equivalence.inverse.op ⋙ P) ≫
      (cechComplexFunctor U.opens).map ((eqToIso (congrArg (fun G : Opens X ⥤ Opens X ↦
        (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ A).obj G.op)
        (opensCongr_inverse_refl (X := X))) ≪≫
        Functor.whiskeringLeftObjIdIso (C := (Opens X)ᵒᵖ) (E := A)).hom.app P) = 𝟙 _ := by
  let F := (Homeomorph.refl X).opensCongr.equivalence.inverse
  let R := F.op ⋙ P
  let q := congrArg PointOpenCover.opens (PointOpenCover.mapHomeomorph_refl U)
  let e := (eqToIso (congrArg (cechComplexFunctor.{u₁} (A := A)) q)).hom.app R
  let ρ := eqToIso (congrArg (fun G : Opens X ⥤ Opens X ↦
      (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ A).obj G.op)
      (opensCongr_inverse_refl (X := X))) ≪≫
    Functor.whiskeringLeftObjIdIso (C := (Opens X)ᵒᵖ) (E := A)
  let φ := ρ.hom.app P
  ext n : 2
  apply (cancel_mono (cechXIso U.opens P n).hom).mp
  refine Pi.hom_ext _ _ fun a ↦ ?_
  let f := (((Homeomorph.refl X).cechComplexIso (A := A) U).hom.app P).f n
  let g := ((cechComplexFunctor U.opens).map φ).f n
  have sf := cechComplexIso_hom_app_f_commSq (Homeomorph.refl X) U P n a
  have se : CommSq (e.f n)
      ((cechXIso (U.mapHomeomorph (Homeomorph.refl X)).opens R n).hom ≫ Pi.π _ a)
      ((cechXIso U.opens R n).hom ≫ Pi.π _ a)
      (R.map (eqToHom (congrArg (fun V : X → Opens X ↦ ∏ᶜ fun j ↦ V (a j)) q.symm)).op) :=
    ⟨(R.cechComplex_eqToIso_hom_app_f_π
      (U.mapHomeomorph (Homeomorph.refl X)).opens U.opens q n a).trans
        (Category.assoc _ _ _).symm⟩
  have sg : CommSq g ((cechXIso U.opens R n).hom ≫ Pi.π _ a)
      ((cechXIso U.opens P n).hom ≫ Pi.π _ a) (φ.app (op (∏ᶜ fun j ↦ U.opens (a j)))) :=
    ⟨(cechComplexFunctor_map_f_comp_cechXIso_hom_π U.opens φ n a).trans
      (Category.assoc _ _ _).symm⟩
  have hm := map_comp_whiskeringLeft_eqToIso_op_id_app F
    (opensCongr_inverse_refl (X := X)) P ((Homeomorph.refl X).cechTupleComparison U n a)
    (eqToHom (congrArg (fun V : X → Opens X ↦ ∏ᶜ fun j ↦ V (a j)) q.symm))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.id_comp]
  -- The evaluated unit comparison has the named chain-map components f, e and g.
  change ((f ≫ e.f n ≫ g) ≫ (cechXIso U.opens P n).hom) ≫ Pi.π _ a =
    (cechXIso U.opens P n).hom ≫ Pi.π _ a
  have hs := ((sf.horiz_comp se).horiz_comp sg).w
  have he := hs.trans (((cechXIso U.opens P n).hom ≫ Pi.π _ a) ≫=
    ((Category.assoc _ _ _).trans hm))
  exact (Category.assoc _ _ _).trans
    (((Category.assoc f (e.f n) g).symm =≫ _).trans (he.trans (Category.comp_id _)))

omit [HasProducts.{u₂} A] [HasProducts.{u₃} A] in
/-- Identity transport is the canonical unit identification of the actual Čech complex functor. -/
theorem cechComplexIso_refl (U : PointOpenCover X) :
    let C := cechComplexFunctor.{u₁} (A := A) U.opens
    let W := (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ A).obj
      (Homeomorph.refl X).opensCongr.equivalence.inverse.op
    let q : W ⋙ cechComplexFunctor.{u₁} (A := A)
        (U.mapHomeomorph (Homeomorph.refl X)).opens ≅ W ⋙ C :=
      isoWhiskerLeft W (eqToIso (congrArg
        (fun V : PointOpenCover X ↦ cechComplexFunctor.{u₁} (A := A) V.opens)
        (PointOpenCover.mapHomeomorph_refl U)))
    let e : W ≅ 𝟭 ((Opens X)ᵒᵖ ⥤ A) :=
      eqToIso (congrArg (fun G : Opens X ⥤ Opens X ↦
        (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ A).obj G.op)
        (opensCongr_inverse_refl (X := X))) ≪≫
        Functor.whiskeringLeftObjIdIso (C := (Opens X)ᵒᵖ) (E := A)
    (Homeomorph.refl X).cechComplexIso (A := A) U =
      (q ≪≫ isoWhiskerRight e C ≪≫ Functor.leftUnitor C).symm := by
  apply Iso.ext
  apply (Iso.comp_hom_eq_id _).mp
  apply NatTrans.ext
  funext P
  simp only [NatTrans.comp_app, Iso.trans_hom, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, Functor.leftUnitor_hom_app, NatTrans.id_app]
  -- The left unitor component is `𝟙`; the remaining components are the helper's, read through
  -- the definitional `whiskeringLeft` object and `Iso.trans` component.
  exact (_ ≫= _ ≫= Category.comp_id _).trans (cechComplexIso_refl_hom_app_comp U P)

/-- Successive homeomorphisms give the same actual tuple transport as their composite,
including the equality identifying the transported cover and the canonical whiskering map. -/
theorem cechComplexIso_trans (h : X ≃ₜ Y) (k : Y ≃ₜ Z) (U : PointOpenCover X) :
    (h.trans k).cechComplexIso (A := A) U =
      h.cechComplexIso U ≪≫
        isoWhiskerLeft ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
          h.opensCongr.equivalence.inverse.op) (k.cechComplexIso (U.mapHomeomorph h)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight ((Functor.whiskeringLeftObjCompIso
          (E := A) k.opensCongr.equivalence.inverse.op h.opensCongr.equivalence.inverse.op).symm ≪≫
          eqToIso (congrArg (fun G : (Opens Z)ᵒᵖ ⥤ (Opens X)ᵒᵖ ↦
            (Functor.whiskeringLeft (Opens Z)ᵒᵖ (Opens X)ᵒᵖ A).obj G)
            (opensCongr_inverse_op_trans h k).symm))
          (cechComplexFunctor.{u₃} (A := A) ((U.mapHomeomorph h).mapHomeomorph k).opens) ≪≫
        isoWhiskerLeft ((Functor.whiskeringLeft (Opens Z)ᵒᵖ (Opens X)ᵒᵖ A).obj
          (h.trans k).opensCongr.equivalence.inverse.op)
          (eqToIso (congrArg (fun V : PointOpenCover Z ↦ cechComplexFunctor (A := A) V.opens)
            (PointOpenCover.mapHomeomorph_trans U h k))) := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  let Q := h.opensCongr.equivalence.inverse.op ⋙ P
  let R := k.opensCongr.equivalence.inverse.op ⋙ Q
  let S := (h.trans k).opensCongr.equivalence.inverse.op ⋙ P
  let V := (U.mapHomeomorph h).mapHomeomorph k
  let T := U.mapHomeomorph (h.trans k)
  let q := congrArg PointOpenCover.opens (PointOpenCover.mapHomeomorph_trans U h k)
  let γ := eqToIso (congrArg (fun G : (Opens Z)ᵒᵖ ⥤ (Opens X)ᵒᵖ ↦
    (Functor.whiskeringLeft (Opens Z)ᵒᵖ (Opens X)ᵒᵖ A).obj G)
    (opensCongr_inverse_op_trans h k).symm)
  let φ : R ⟶ S := γ.hom.app P
  let t := (cechComplexFunctor.{u₃} V.opens).map φ ≫
    (eqToIso (congrArg (cechComplexFunctor.{u₃} (A := A)) q)).hom.app S
  ext n : 2
  apply (cancel_mono (cechXIso T.opens S n).hom).mp
  refine Pi.hom_ext _ _ fun a ↦ ?_
  let ha : (h.trans k).symm.toEquiv ∘ a =
      h.symm.toEquiv ∘ (k.symm.toEquiv ∘ a) := rfl
  let mh := P.map (h.cechTupleComparison U n (k.symm.toEquiv ∘ a) ≫
    eqToHom (congrArg (fun b ↦ ∏ᶜ fun j ↦ U.opens (b j)) ha.symm)).op
  let mk := Q.map (k.cechTupleComparison (U.mapHomeomorph h) n a).op
  let mt := φ.app (op (∏ᶜ fun j ↦ V.opens (a j))) ≫
    S.map (eqToHom (congrArg (fun V : Z → Opens Z ↦ ∏ᶜ fun j ↦ V (a j)) q.symm)).op
  have sf := cechComplexIso_hom_app_f_commSq_of_eq h U P n
    (k.symm.toEquiv ∘ a) ((h.trans k).symm.toEquiv ∘ a) ha
  have sg := cechComplexIso_hom_app_f_commSq k (U.mapHomeomorph h) Q n a
  have st : CommSq (t.f n) ((cechXIso V.opens R n).hom ≫ Pi.π _ a)
      ((cechXIso T.opens S n).hom ≫ Pi.π _ a) mt :=
    ⟨(R.cechComplexFunctor_map_comp_eqToIso_hom_app_f_π φ V.opens T.opens q n a).trans
      (Category.assoc _ _ _).symm⟩
  have hm : (mh ≫ mk) ≫ mt = P.map ((h.trans k).cechTupleComparison U n a).op := by
    dsimp only [mh, mk, mt, φ]
    rw [whiskeringLeft_eqToIso_hom_app_app _ _ (opensCongr_inverse_op_trans h k).symm]
    dsimp only [Q, R, S, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
    exact ((P.map_comp _ _).symm =≫ _).trans ((_ ≫= (P.map_comp _ _).symm).trans
      ((P.map_comp _ _).symm.trans (congrArg P.map (Subsingleton.elim _ _))))
  have hr := ((sf.horiz_comp sg).horiz_comp st).w.trans
    (((cechXIso U.opens P n).hom ≫ Pi.π _ _) ≫= hm)
  have hl := cechComplexIso_hom_app_f_commSq (A := A) (h.trans k) U P n a
  rw [Functor.whiskeringLeft_transport_comp_hom_app (q := (opensCongr_inverse_op_trans h k).symm),
    isoWhiskerLeft_hom, whiskerLeft_app]
  simp only [HomologicalComplex.comp_f]
  refine ((Category.assoc _ _ _).trans hl.w).trans ?_
  simpa only [t, Q, R, S, V, T, φ, γ, HomologicalComplex.comp_f,
    Functor.whiskeringLeft_obj_obj, Function.comp_def, Category.assoc] using hr.symm

end Homeomorph

namespace Homeomorph

universe u₁ u₂ u₃ a₁ b₁

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.Topology TauCeti.CategoryTheory

variable {A : Type a₁} [Category.{b₁} A] [Preadditive A] [CategoryWithHomology A]
  {X : TopCat.{u₁}} {Y : TopCat.{u₂}} {Z : TopCat.{u₃}}
  [HasProducts.{u₁} A] [HasProducts.{u₂} A] [HasProducts.{u₃} A]
  [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]
  [HasColimitsOfShape (PointOpenCover Z) A]

/-- Successive native cover-colimit transport agrees with the composite homeomorphism,
with the canonical actual inverse-opens precomposition identification. -/
theorem cechCohomologyIso_trans (h : X ≃ₜ Y) (k : Y ≃ₜ Z) (n : ℕ) :
    (h.trans k).cechCohomologyIso (A := A) n =
      h.cechCohomologyIso n ≪≫
        isoWhiskerLeft ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
          h.opensCongr.equivalence.inverse.op) (k.cechCohomologyIso n) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight ((Functor.whiskeringLeftObjCompIso
          (E := A) k.opensCongr.equivalence.inverse.op h.opensCongr.equivalence.inverse.op).symm ≪≫
          eqToIso (congrArg (fun G : (Opens Z)ᵒᵖ ⥤ (Opens X)ᵒᵖ ↦
            (Functor.whiskeringLeft (Opens Z)ᵒᵖ (Opens X)ᵒᵖ A).obj G)
            (opensCongr_inverse_op_trans h k).symm)) (cechCohomology Z A n) := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  let Q := h.opensCongr.equivalence.inverse.op ⋙ P
  let R := k.opensCongr.equivalence.inverse.op ⋙ Q
  let S := (h.trans k).opensCongr.equivalence.inverse.op ⋙ P
  let γ := eqToIso (congrArg (fun G : (Opens Z)ᵒᵖ ⥤ (Opens X)ᵒᵖ ↦
    (Functor.whiskeringLeft (Opens Z)ᵒᵖ (Opens X)ᵒᵖ A).obj G)
    (opensCongr_inverse_op_trans h k).symm)
  let φ : R ⟶ S := γ.hom.app P
  apply cechCohomology_obj_hom_ext
  intro U
  let V := (U.mapHomeomorph h).mapHomeomorph k
  let T := U.mapHomeomorph (h.trans k)
  let q := PointOpenCover.mapHomeomorph_trans U h k
  have sh : CommSq _ _ _ _ := ⟨cechCohomologyIso_hom_app_ι h P n U⟩
  have sk : CommSq _ _ _ _ := ⟨cechCohomologyIso_hom_app_ι k Q n (U.mapHomeomorph h)⟩
  have sp : CommSq
      ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app R)
      (HomologicalComplex.homologyMap ((cechComplexFunctor V.opens).map φ) n)
      ((cechCohomology Z A n).map φ)
      ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app S) :=
    ⟨((cechCohomologyι PointOpenCover.toFormalCoproduct
      (fun _ _ hf ↦ hf) n V).naturality φ).symm⟩
  have hs := ((sh.vert_comp sk).vert_comp sp).w
  have he := PointOpenCover.homologyMap_eqToIso_comp_cechCohomologyι V T q S n
  have hc := congrArg (fun e ↦ HomologicalComplex.homologyMap (e.hom.app P) n)
    (cechComplexIso_trans (A := A) h k U)
  rw [Functor.whiskeringLeft_transport_comp_hom_app (q := (opensCongr_inverse_op_trans h k).symm),
    isoWhiskerLeft_hom, whiskerLeft_app] at hc
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have hcohomology := Functor.whiskeringLeft_transport_comp_hom_app _ _ _
    (opensCongr_inverse_op_trans h k).symm (h.cechCohomologyIso (A := A) n)
    (k.cechCohomologyIso (A := A) n) (Iso.refl _) P
  simp only [Iso.trans_refl, Iso.refl_hom, NatTrans.id_app] at hcohomology
  rw [hcohomology]
  have ht := cechCohomologyIso_hom_app_ι (h.trans k) P n U
  have hb := ((HomologicalComplex.homologyMap ((h.cechComplexIso U).hom.app P) n ≫
      HomologicalComplex.homologyMap ((k.cechComplexIso (U.mapHomeomorph h)).hom.app Q) n) ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor V.opens).map φ) n) ≫= he
  have hch := hc.trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)
  have hr := (((hch =≫ (cechCohomologyι PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n T).app S).trans (Category.assoc _ _ _)).trans hb).trans hs.symm
  simpa only [Q, φ, Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Category.assoc,
    Category.comp_id] using
    ht.trans hr

end Homeomorph

namespace Homeomorph

universe u₁ a₁ b₁

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.Topology TauCeti.CategoryTheory

variable {A : Type a₁} [Category.{b₁} A] [Preadditive A] [CategoryWithHomology A]
  {X : TopCat.{u₁}} [HasProducts.{u₁} A] [HasColimitsOfShape (PointOpenCover X) A]

/-- Identity homeomorphism transport is the canonical unit on native cover-colimit cohomology. -/
theorem cechCohomologyIso_refl (n : ℕ) :
    let C := cechCohomology X A n
    let W := (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ A).obj
      (Homeomorph.refl X).opensCongr.equivalence.inverse.op
    let e : W ≅ 𝟭 ((Opens X)ᵒᵖ ⥤ A) :=
      eqToIso (congrArg (fun G : Opens X ⥤ Opens X ↦
        (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ A).obj G.op)
        (opensCongr_inverse_refl (X := X))) ≪≫
        Functor.whiskeringLeftObjIdIso (C := (Opens X)ᵒᵖ) (E := A)
    (Homeomorph.refl X).cechCohomologyIso (A := A) n =
      (isoWhiskerRight e C ≪≫ Functor.leftUnitor C).symm := by
  apply Iso.ext
  apply (Iso.comp_hom_eq_id _).mp
  apply NatTrans.ext
  funext P
  let R := (Homeomorph.refl X).opensCongr.equivalence.inverse.op ⋙ P
  let ρ := eqToIso (congrArg (fun G : Opens X ⥤ Opens X ↦
      (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens X)ᵒᵖ A).obj G.op)
      (opensCongr_inverse_refl (X := X))) ≪≫
    Functor.whiskeringLeftObjIdIso (C := (Opens X)ᵒᵖ) (E := A)
  let φ : R ⟶ P := ρ.hom.app P
  simp only [NatTrans.comp_app, Iso.trans_hom, isoWhiskerRight_hom, whiskerRight_app,
    Functor.leftUnitor_hom_app, NatTrans.id_app]
  -- The left unitor evaluates to the identity, while φ is the ρ-component at P.
  change _ ≫ (cechCohomology X A n).map φ ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id ((cechCohomology X A n).map φ)]
  apply cechCohomology_obj_hom_ext
  intro U
  let V := U.mapHomeomorph (Homeomorph.refl X)
  let q := PointOpenCover.mapHomeomorph_refl U
  let e := eqToIso (congrArg (fun T : PointOpenCover X ↦
    cechComplexFunctor.{u₁} (A := A) T.opens) q)
  have sh : CommSq _ _ _ _ := ⟨cechCohomologyIso_hom_app_ι (Homeomorph.refl X) P n U⟩
  have sp : CommSq
      ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app R)
      (HomologicalComplex.homologyMap ((cechComplexFunctor V.opens).map φ) n)
      ((cechCohomology X A n).map φ)
      ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app P) :=
    ⟨((cechCohomologyι PointOpenCover.toFormalCoproduct
      (fun _ _ hf ↦ hf) n V).naturality φ).symm⟩
  have hs := (sh.vert_comp sp).w
  have he := PointOpenCover.homologyMap_eqToIso_comp_cechCohomologyι V U q P n
  have hn := e.hom.naturality φ
  have hm := ((Homeomorph.refl X).cechComplexIso (A := A) U).hom.app P ≫= hn
  have hm' := hm.trans (cechComplexIso_refl_hom_app_comp U P)
  have hh := congrArg (fun f ↦ HomologicalComplex.homologyMap f n) hm'
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at hh
  have hb := (HomologicalComplex.homologyMap
      (((Homeomorph.refl X).cechComplexIso U).hom.app P) n ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor V.opens).map φ) n) ≫= he
  have hh' := (Category.assoc _ _ _).trans hh
  have hy := (hh' =≫ (cechCohomologyι PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n U).app P).trans (Category.id_comp _)
  have hx := (Category.assoc _ _ _).trans hb
  exact (hs.trans (hx.symm.trans hy)).trans (Category.comp_id _).symm

end Homeomorph
