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
public import Mathlib.CategoryTheory.Sites.Equivalence
public import TauCeti.CategoryTheory.Limits.Reindex

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

universe u v

namespace TauCeti.Topology

universe a b

open TauCeti.CategoryTheory

variable {A : Type a} [Category.{b} A] [Preadditive A]

variable {X : TopCat.{u}} {Y : TopCat.{v}} (h : X ≃ₜ Y)
  [HasProducts.{u} A] [HasProducts.{v} A]
  (U : PointOpenCover X) (P : (Opens X)ᵒᵖ ⥤ A)

private lemma inverseOpens_mapHomeomorph :
    (fun y ↦ h.opensCongr.symm.equivalence.functor.obj ((U.mapHomeomorph h).opens y)) =
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
          h.opensCongr.symm.equivalence.functor.op ⋙
        cechComplexFunctor.{v} (U.mapHomeomorph h).opens :=
  (cechComplexReindexIso h.symm.toEquiv U.opens).symm ≪≫
    (eqToIso (congrArg (fun V : Y → Opens X ↦ cechComplexFunctor (A := A) V)
      (inverseOpens_mapHomeomorph h U).symm)) ≪≫
    NatIso.ofComponents (fun P ↦
      cechComplexCompIso h.opensCongr.symm.equivalence.functor (U.mapHomeomorph h).opens P
        (fun _ _ ↦ inferInstance))
      (fun φ ↦ cechComplexFunctor_map_comp_cechComplexCompIso_hom
        h.opensCongr.symm.equivalence.functor (U.mapHomeomorph h).opens _
        (fun _ _ ↦ inferInstance) φ)

/-- The inverse image of a finite intersection maps to the intersection of inverse images. -/
def homeomorphTupleComparison (n : ℕ) (a : Fin (n + 1) → Y) :
    h.opensCongr.symm.equivalence.functor.obj (∏ᶜ fun j ↦ (U.mapHomeomorph h).opens (a j)) ⟶
      ∏ᶜ fun j ↦ U.opens (h.symm (a j)) :=
  (Pi.lift fun j ↦ h.opensCongr.symm.equivalence.functor.map
    (Pi.π (fun j ↦ (U.mapHomeomorph h).opens (a j)) j)) ≫
      eqToHom (congrArg (fun V ↦ ∏ᶜ fun j ↦ V (a j)) (inverseOpens_mapHomeomorph h U))

/-- Inverse-image transport preserves finite intersections. -/
instance homeomorphTupleComparison_isIso (n : ℕ) (a : Fin (n + 1) → Y) :
    IsIso (homeomorphTupleComparison h U n a) := by
  -- The first factor is the native product comparison of the opens equivalence.
  change IsIso (piComparison h.opensCongr.symm.equivalence.functor
    (fun j ↦ (U.mapHomeomorph h).opens (a j)) ≫ _)
  infer_instance

/-- Each component of the tuple comparison is the image of the corresponding projection. -/
@[reassoc]
theorem homeomorphTupleComparison_comp_π (n : ℕ) (a : Fin (n + 1) → Y)
    (j : Fin (n + 1)) :
    homeomorphTupleComparison h U n a ≫ Pi.π _ j =
      h.opensCongr.symm.equivalence.functor.map
        (Pi.π (fun j ↦ (U.mapHomeomorph h).opens (a j)) j) ≫
        eqToHom (by
          rw [PointOpenCover.mapHomeomorph_opens]
          exact h.opensCongr.symm_apply_apply _) := by
  apply Subsingleton.elim

@[reassoc]
private lemma cechComplexHomeomorphIso_hom_app_f_comp_cechXIso_hom_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((cechComplexHomeomorphIso (A := A) h U).hom.app P).f n ≫
        (cechXIso (U.mapHomeomorph h).opens
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) n).hom ≫ Pi.π _ a =
      (cechXIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a) ≫
        P.map (homeomorphTupleComparison h U n a).op := by
  simp only [cechComplexHomeomorphIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, HomologicalComplex.comp_f, Category.assoc,
    cechComplexCompIso_hom_f_comp_cechXIso_hom_π]
  rw [cechComplex_eqToIso_hom_app_f_π_assoc P (U.opens ∘ h.symm.toEquiv)
    (fun y ↦ h.opensCongr.symm.equivalence.functor.obj ((U.mapHomeomorph h).opens y))
    (inverseOpens_mapHomeomorph h U).symm n a]
  rw [cechComplexReindexIso_inv_app_f_comp_cechXIso_hom_π_assoc]
  simp only [homeomorphTupleComparison, op_comp, Functor.map_comp]

/-- The native component reads a transported tuple by the corresponding original tuple. -/
@[reassoc]
theorem cechComplexHomeomorphIso_hom_app_f_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((cechComplexHomeomorphIso (A := A) h U).hom.app P).f n ≫ Pi.π _ a =
      Pi.π _ (h.symm.toEquiv ∘ a) ≫ P.map (homeomorphTupleComparison h U n a).op := by
  have hr := cechComplexHomeomorphIso_hom_app_f_comp_cechXIso_hom_π h U P n a
  simp only [cechXIso_hom_π, cechXIso_hom_π_assoc] at hr
  -- The explicit intersection and native rightOp term have this same dependent codomain.
  convert hr using 1; rfl

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
theorem cechAugmentation_comp_cechComplexHomeomorphIso [HasZeroObject A] :
    cechAugmentation U.opens isTerminalTop P ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P =
      (CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op) ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) := by
  -- Use the actual inverse-opens functor object at top in the component calculation.
  let α : P.obj (op ⊤) ⟶ (h.opensCongr.symm.equivalence.functor.op ⋙ P).obj (op ⊤) :=
    P.map (eqToHom (show h.opensCongr.symm.equivalence.functor.obj ⊤ = ⊤ from
      h.opensCongr.symm.map_top)).op
  change cechAugmentation U.opens isTerminalTop P ≫
      (cechComplexHomeomorphIso (A := A) h U).hom.app P =
    (CochainComplex.single₀ A).map α ≫ cechAugmentation (U.mapHomeomorph h).opens
      isTerminalTop (h.opensCongr.symm.equivalence.functor.op ⋙ P)
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_mono (cechXIso (U.mapHomeomorph h).opens
    (h.opensCongr.symm.equivalence.functor.op ⋙ P) 0).hom).mp
  refine Pi.hom_ext _ _ fun a ↦ ?_
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, Category.assoc]
  rw [cechComplexHomeomorphIso_hom_app_f_comp_cechXIso_hom_π,
    cechAugmentation_f_zero_comp_cechXIso_hom_π_assoc,
    cechAugmentation_f_zero_comp_cechXIso_hom_π]
  dsimp only [α, Functor.comp_map, Functor.op_map]
  rw [← P.map_comp, ← P.map_comp]
  exact P.congr_map (Subsingleton.elim _ _)

private lemma cechAugmentation_comp_homeomorph_map [HasZeroObject A]
    (Q : (Opens Y)ᵒᵖ ⥤ A)
    (φ : h.opensCongr.symm.equivalence.functor.op ⋙ P ⟶ Q) :
    cechAugmentation U.opens isTerminalTop P ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P ≫
        (cechComplexFunctor (U.mapHomeomorph h).opens).map φ =
      (CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op ≫ φ.app (op ⊤)) ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop Q := by
  have hn := cechAugmentation_naturality (U.mapHomeomorph h).opens isTerminalTop
    (h.opensCongr.symm.equivalence.functor.op ⋙ P) φ
  -- The top-open object of the inverse-opens composite is the codomain of the map.
  erw [← Category.assoc, cechAugmentation_comp_cechComplexHomeomorphIso,
    Category.assoc, hn, ← Category.assoc, ← Functor.map_comp]

@[reassoc]
private lemma cechAugmentationClass_comp_homeomorph_map
    [CategoryWithHomology A] [HasZeroObject A] (Q : (Opens Y)ᵒᵖ ⥤ A)
    (φ : h.opensCongr.symm.equivalence.functor.op ⋙ P ⟶ Q) :
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
    cechComplexMap (U := U.opens) (V := V.opens) P φ ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P =
      (cechComplexHomeomorphIso (A := A) h V).hom.app P ≫
        cechComplexMap (U := (U.mapHomeomorph h).opens) (V := (V.mapHomeomorph h).opens)
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) (U.mapHomeomorphHom h φ) := by
  ext n : 2
  simp only [HomologicalComplex.comp_f]
  apply (cancel_mono (cechXIso (U.mapHomeomorph h).opens
    (h.opensCongr.symm.equivalence.functor.op ⋙ P) n).hom).mp
  refine Pi.hom_ext _ _ fun a ↦ ?_
  simp only [Category.assoc]
  rw [cechComplexHomeomorphIso_hom_app_f_comp_cechXIso_hom_π,
    cechComplexMap_f_comp_cechXIso_hom_π_assoc,
    cechComplexMap_f_comp_cechXIso_hom_π]
  refine Eq.trans ?_ (cechComplexHomeomorphIso_hom_app_f_comp_cechXIso_hom_π_assoc h V P n
    ((U.mapHomeomorphHom h φ).f ∘ a) _).symm
  simp only [Functor.comp_map, Functor.op_map, ← Functor.map_comp, ← op_comp]
  refine (cechXIso V.opens P n).hom ≫=
    cechProjection_comp_map_eq_of_tuple_eq (κ := X) (W := V.opens) P ?_ _ _
  funext j
  simp [PointOpenCover.mapHomeomorphHom_f]

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
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) := by
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
      (h.opensCongr.symm.equivalence.functor.op ⋙ P)).symm))

variable [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]

private def cechHomeomorphObjIso :
    (cechCohomology X A n).obj P ≅
      (cechCohomology Y A n).obj (h.opensCongr.symm.equivalence.functor.op ⋙ P) :=
  HasColimit.isoOfEquivalence (coverHomeomorphEquivalence h)
    (cechHomeomorphDiagramIso h P n).symm

@[reassoc]
private lemma cechHomeomorphObjIso_ι (V : PointOpenCover X) :
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app P ≫
        (cechHomeomorphObjIso h P n).hom =
      HomologicalComplex.homologyMap ((cechComplexHomeomorphIso (A := A) h V).hom.app P) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n
          (V.mapHomeomorph h)).app (h.opensCongr.symm.equivalence.functor.op ⋙ P) := by
  have he := HasColimit.ι_isoOfEquivalence_hom
    (coverHomeomorphEquivalence h)
    (cechHomeomorphDiagramIso h P n).symm V
  exact ((cechCohomologyι_app PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n V P =≫ _).trans he).trans
      (_ ≫= (cechCohomologyι_app PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n
        (V.mapHomeomorph h) (h.opensCongr.symm.equivalence.functor.op ⋙ P)).symm)

private lemma cechHomeomorphObjIso_hom_naturality {Q : (Opens X)ᵒᵖ ⥤ A} (φ : P ⟶ Q) :
    (cechCohomology X A n).map φ ≫ (cechHomeomorphObjIso h Q n).hom =
      (cechHomeomorphObjIso h P n).hom ≫ (cechCohomology Y A n).map
        (Functor.whiskerLeft h.opensCongr.symm.equivalence.functor.op φ) := by
  let D := cechCohomologyDiagram.{u} A (PointOpenCover.toFormalCoproduct (X := X))
    (fun _ _ hf ↦ hf) n
  let E := cechCohomologyDiagram.{v} A (PointOpenCover.toFormalCoproduct (X := Y))
    (fun _ _ hf ↦ hf) n
  apply HasColimit.colimMap_comp_isoOfEquivalence_hom
    (coverHomeomorphEquivalence h) (D.flip.map φ)
    (E.flip.map (Functor.whiskerLeft h.opensCongr.symm.equivalence.functor.op φ))
    (cechHomeomorphDiagramIso h P n).symm (cechHomeomorphDiagramIso h Q n).symm
  intro V
  exact (Functor.isoWhiskerRight (cechComplexHomeomorphIso (A := A) h V)
    (HomologicalComplex.homologyFunctor A _ n)).hom.naturality φ

/-- Native cover-colimit Čech cohomology is preserved by a homeomorphism across universes. -/
def cechCohomologyHomeomorphIso :
    cechCohomology X A n ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
        h.opensCongr.symm.equivalence.functor.op ⋙ cechCohomology Y A n :=
  NatIso.ofComponents (fun P ↦ cechHomeomorphObjIso h P n)
    (fun φ ↦ cechHomeomorphObjIso_hom_naturality h _ n φ)

/-- The transported native class of each cover is its original class followed by the comparison. -/
@[reassoc]
theorem cechCohomologyHomeomorphIso_hom_app_ι (V : PointOpenCover X) :
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app P ≫
        (cechCohomologyHomeomorphIso (A := A) h n).hom.app P =
      HomologicalComplex.homologyMap ((cechComplexHomeomorphIso (A := A) h V).hom.app P) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n
          (V.mapHomeomorph h)).app (h.opensCongr.symm.equivalence.functor.op ⋙ P) :=
  cechHomeomorphObjIso_ι h P n V

end Cohomology

section ZeroComparison

variable [CategoryWithHomology A] [HasZeroObject A]
  [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]
  (F : Sheaf (Opens.grothendieckTopology X) A)

/-- Transport through a homeomorphism preserves the native degree-zero Čech class of a
section, including the actual comparison with the transported sheaf. -/
@[reassoc]
theorem cechCohomologyZeroIso_hom_comp_cechCohomologyHomeomorphIso :
    (cechCohomologyZeroIso F).hom ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj ≫
        (cechCohomology Y A 0).map ((h.sheafCongrSheafToPresheafIso A).inv.app F) =
      (F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫
        ((h.sheafCongrSheafToPresheafIso A).inv.app F).app (op ⊤)) ≫
        (cechCohomologyZeroIso ((h.sheafCongr A).functor.obj F)).hom := by
  let U : PointOpenCover X := default
  let F' := (h.sheafCongr A).functor.obj F
  let φ := (h.sheafCongrSheafToPresheafIso A).inv.app F
  have hs := cechCohomologyZeroIso_hom F U
  have ht := cechCohomologyZeroIso_hom F' (U.mapHomeomorph h)
  have hi := cechCohomologyHomeomorphIso_hom_app_ι h F.obj 0 U
  have hn : (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) 0
        (U.mapHomeomorph h)).app (h.opensCongr.symm.equivalence.functor.op ⋙ F.obj) ≫
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

variable [HasWeakSheafify (Opens.grothendieckTopology X) A]
  [HasWeakSheafify (Opens.grothendieckTopology Y) A]

/-- The existing homeomorphism comparison of global sections commutes with the native
identifications of global sections and degree-zero Čech cohomology. -/
@[reassoc]
theorem sectionsIsoCechZero_hom_comp_cechCohomologyHomeomorphIso :
    (sectionsIsoCechZero F).hom ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj ≫
        (cechCohomology Y A 0).map ((h.sheafCongrSheafToPresheafIso A).inv.app F) =
      (h.globalSectionsIso A).hom.app F ≫
        (sectionsIsoCechZero ((h.sheafCongr A).functor.obj F)).hom := by
  rw [sectionsIsoCechZero_hom, Category.assoc,
    cechCohomologyZeroIso_hom_comp_cechCohomologyHomeomorphIso,
    sectionsIsoCechZero_hom]
  simpa only [Category.assoc] using
    (h.globalSectionsIso_hom_app_comp_ΓNatIsoSheafSections_hom_assoc A F
      (cechCohomologyZeroIso ((h.sheafCongr A).functor.obj F)).hom).symm

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
      h.opensCongr.symm.equivalence.functor.op)).map
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
              h.opensCongr.symm.equivalence.functor.op)).map_of_exact
                (cechComplexFunctor V.opens)) n := by
  apply colimit.hom_ext
  intro V
  have hi := cechCohomologyι_app PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n V T.X₃
  refine (hi.symm =≫ _).trans (Eq.trans ?_ (hi =≫ _))
  have hsource := cechCohomologyι_app_δ PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) (fun V ↦ hT.map_of_exact (cechComplexFunctor V.opens)) n V
  have hlocal := δ_comp_homologyMap_cechComplexHomeomorphIso_hom_app h V
    (hT.map_of_exact (cechComplexFunctor V.opens)) n
  have htarget := cechCohomologyι_app_δ PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf)
    (fun V : PointOpenCover Y ↦ (hT.map_of_exact
      ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
        h.opensCongr.symm.equivalence.functor.op)).map_of_exact
          (cechComplexFunctor V.opens)) n (V.mapHomeomorph h)
  have hq₁ := cechCohomologyHomeomorphIso_hom_app_ι h T.X₁ (n + 1) V
  have hq₃ := cechCohomologyHomeomorphIso_hom_app_ι h T.X₃ n V
  have sourceSquare : CommSq _ _ _ _ := ⟨hsource⟩
  have targetSquare : CommSq _ _ _ _ := ⟨htarget⟩
  have upperSquare : CommSq _ _ _ _ := ⟨hq₃⟩
  have lowerSquare : CommSq _ _ _ _ := ⟨hq₁⟩
  exact (sourceSquare.vert_comp lowerSquare).w.trans
    ((hlocal =≫ _).trans (upperSquare.vert_comp targetSquare).w.symm)

end TauCeti.Topology
