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

/-!
# Čech cohomology under a homeomorphism

Homeomorphisms identify native point-neighborhood covers and their Čech cohomology,
including when the spaces belong to different universes.
-/

public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u v

namespace TauCeti.Topology.PointOpenCover

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- A refinement can be specified point by point, without choosing its function in advance. -/
theorem le_iff_forall_exists (U V : PointOpenCover X) :
    U ≤ V ↔ ∀ x, ∃ y, V.opens x ≤ U.opens y := by
  constructor
  · rintro ⟨f⟩ x
    exact ⟨f.f x, leOfHom (f.φ x)⟩
  · intro h
    choose f hf using h
    exact ⟨⟨f, fun x ↦ homOfLE (hf x)⟩⟩

/-- Move the neighborhoods of a point cover through a homeomorphism. -/
def mapHomeomorph (h : X ≃ₜ Y) (U : PointOpenCover X) : PointOpenCover Y where
  opens y := h.opensCongr (U.opens (h.symm y))
  mem_opens y := U.mem_opens (h.symm y)

/-- The identity homeomorphism leaves every actual point-neighborhood cover unchanged. -/
@[simp]
theorem mapHomeomorph_refl (U : PointOpenCover X) :
    U.mapHomeomorph (Homeomorph.refl X) = U := by
  ext x z
  rfl

/-- Successive homeomorphisms transport the same actual neighborhoods as their composite. -/
theorem mapHomeomorph_trans {Z : Type*} [TopologicalSpace Z]
    (h : X ≃ₜ Y) (k : Y ≃ₜ Z) (U : PointOpenCover X) :
    (U.mapHomeomorph h).mapHomeomorph k = U.mapHomeomorph (h.trans k) := by
  ext x z
  rfl

/-- The transported neighborhood at the image of a point. -/
@[simp]
theorem mapHomeomorph_opens_apply (h : X ≃ₜ Y) (U : PointOpenCover X) (x : X) :
    (U.mapHomeomorph h).opens (h x) = h.opensCongr (U.opens x) := by
  simp [mapHomeomorph]

/-- Transporting through a homeomorphism and back recovers the same native cover. -/
@[simp]
theorem mapHomeomorph_symm (h : X ≃ₜ Y) (U : PointOpenCover X) :
    (U.mapHomeomorph h).mapHomeomorph h.symm = U := by
  ext x z
  simp [mapHomeomorph, Homeomorph.opensCongr]

/-- Transport both the neighborhoods and the actual refinement relation. -/
theorem mapHomeomorph_le_mapHomeomorph_iff (h : X ≃ₜ Y) (U V : PointOpenCover X) :
    U.mapHomeomorph h ≤ V.mapHomeomorph h ↔ U ≤ V := by
  rw [le_iff_forall_exists, le_iff_forall_exists]
  constructor
  · intro hUV x
    obtain ⟨y, hxy⟩ := hUV (h x)
    refine ⟨h.symm y, h.opensCongr.le_iff_le.mp ?_⟩
    simpa [mapHomeomorph] using hxy
  · intro hUV y
    obtain ⟨x, hyx⟩ := hUV (h.symm y)
    refine ⟨h x, ?_⟩
    simpa [mapHomeomorph] using h.opensCongr.monotone hyx

/-- A homeomorphism identifies the native refinement preorders, with no universe restriction. -/
def orderIsoOfHomeomorph (h : X ≃ₜ Y) : PointOpenCover X ≃o PointOpenCover Y where
  toFun := mapHomeomorph h
  invFun := mapHomeomorph h.symm
  left_inv := mapHomeomorph_symm h
  right_inv := mapHomeomorph_symm h.symm
  map_rel_iff' := mapHomeomorph_le_mapHomeomorph_iff h _ _

/-- Transport an actual refinement function and all its open inclusions. -/
def mapHomeomorphHom (U : PointOpenCover X) (h : X ≃ₜ Y) {V : PointOpenCover X}
    (φ : U.toFormalCoproduct ⟶ V.toFormalCoproduct) :
    (U.mapHomeomorph h).toFormalCoproduct ⟶ (V.mapHomeomorph h).toFormalCoproduct where
  f y := h (φ.f (h.symm y))
  φ y := homOfLE (by
    change h.opensCongr (U.opens (h.symm y)) ≤
      (V.mapHomeomorph h).opens (h (φ.f (h.symm y)))
    rw [mapHomeomorph_opens_apply]
    exact h.opensCongr.monotone (leOfHom (φ.φ (h.symm y))))

/-- The actual transported refinement uses the conjugated function on points. -/
@[simp]
theorem mapHomeomorphHom_f (U : PointOpenCover X) (h : X ≃ₜ Y) {V : PointOpenCover X}
    (φ : U.toFormalCoproduct ⟶ V.toFormalCoproduct) (y : Y) :
    (U.mapHomeomorphHom h φ).f y = h (φ.f (h.symm y)) := by
  unfold mapHomeomorphHom
  rfl

end TauCeti.Topology.PointOpenCover

namespace TauCeti.Topology

universe a b

open TauCeti.CategoryTheory

variable {A : Type a} [Category.{b} A] [Preadditive A]

section Terms

universe z c d
variable {C : Type c} [Category.{d} C] [HasFiniteProducts C]
  {τ : Type z} [HasProducts.{z} A] (V : τ → C) (P : Cᵒᵖ ⥤ A)

private def cechTermIso (n : ℕ) :
    ((cechComplexFunctor V).obj P).X n ≅
      ∏ᶜ fun a : Fin (n + 1) → τ ↦ P.obj (op (∏ᶜ fun j ↦ V (a j))) :=
  Iso.refl _

@[reassoc]
private lemma cechComplexMap_f_comp_term_π {κ : Type z} (W : κ → C)
    (φ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ W)
    (n : ℕ) (a : Fin (n + 1) → τ) :
    (cechComplexMap P φ).f n ≫ (cechTermIso V P n).hom ≫ Pi.π _ a =
      (cechTermIso W P n).hom ≫ Pi.π _ (φ.f ∘ a) ≫
        P.map (Limits.Pi.map fun j ↦ φ.φ (a j)).op :=
  (_ ≫= Category.id_comp _).trans <| (cechComplexMap_f_π P φ n a).trans
    (Category.id_comp _).symm

end Terms

variable {X : TopCat.{u}} {Y : TopCat.{v}} (h : X ≃ₜ Y)
  [HasProducts.{u} A] [HasProducts.{v} A]
  (U : PointOpenCover X) (P : (Opens X)ᵒᵖ ⥤ A)

private lemma inverseOpens_mapHomeomorph :
    (fun y ↦ h.opensCongr.symm.equivalence.functor.obj ((U.mapHomeomorph h).opens y)) =
      U.opens ∘ h.symm.toEquiv :=
  funext fun _ ↦ h.opensCongr.symm_apply_apply _

omit [HasProducts.{u} A] in
@[reassoc]
private lemma cechComplex_eqToIso_hom_app_f_π (V W : Y → Opens X) (q : V = W)
    (n : ℕ) (a : Fin (n + 1) → Y) :
    ((eqToIso (congrArg (fun V ↦ cechComplexFunctor (A := A) V) q)).hom.app P).f n ≫
        (cechTermIso W P n).hom ≫ Pi.π _ a =
      (cechTermIso V P n).hom ≫ Pi.π _ a ≫
        P.map (eqToHom (congrArg (fun V ↦ ∏ᶜ fun j ↦ V (a j)) q.symm)).op := by
  subst W
  simp

@[reassoc]
private lemma cechComplex_reindex_inv_f_comp_term_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((cechComplexReindexIso h.symm.toEquiv U.opens).inv.app P).f n ≫
        (cechTermIso (U.opens ∘ h.symm.toEquiv) P n).hom ≫ Pi.π _ a =
      (cechTermIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a) :=
  (_ ≫= Category.id_comp _).trans <|
    (cechComplexReindexIso_inv_app_f_π h.symm.toEquiv U.opens P n a).trans
      (Category.id_comp _).symm

omit [HasProducts.{u} A] in
@[reassoc]
private lemma cechComplex_comp_f_comp_term_π (n : ℕ) (a : Fin (n + 1) → Y) :
    (cechComplexCompIso h.opensCongr.symm.equivalence.functor (U.mapHomeomorph h).opens P
      (fun _ _ ↦ inferInstance)).hom.f n ≫
        (cechTermIso (U.mapHomeomorph h).opens
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) n).hom ≫ Pi.π _ a =
      (cechTermIso (fun y ↦ h.opensCongr.symm.equivalence.functor.obj
        ((U.mapHomeomorph h).opens y)) P n).hom ≫ Pi.π _ a ≫
          P.map (Pi.lift fun j ↦ h.opensCongr.symm.equivalence.functor.map
            (Pi.π (fun j ↦ (U.mapHomeomorph h).opens (a j)) j)).op :=
  (_ ≫= Category.id_comp _).trans <|
    (cechComplexCompIso_hom_f_π h.opensCongr.symm.equivalence.functor
      (U.mapHomeomorph h).opens P (fun _ _ ↦ inferInstance) n a).trans
      (Category.id_comp _).symm

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

private def homeomorphTupleComparison (n : ℕ) (a : Fin (n + 1) → Y) :
    h.opensCongr.symm.equivalence.functor.obj (∏ᶜ fun j ↦ (U.mapHomeomorph h).opens (a j)) ⟶
      ∏ᶜ fun j ↦ U.opens (h.symm (a j)) :=
  (Pi.lift fun j ↦ h.opensCongr.symm.equivalence.functor.map
    (Pi.π (fun j ↦ (U.mapHomeomorph h).opens (a j)) j)) ≫
      eqToHom (congrArg (fun V ↦ ∏ᶜ fun j ↦ V (a j)) (inverseOpens_mapHomeomorph h U))

@[reassoc]
private lemma cechComplexHomeomorphIso_hom_app_f_π (n : ℕ) (a : Fin (n + 1) → Y) :
    ((cechComplexHomeomorphIso (A := A) h U).hom.app P).f n ≫
        (cechTermIso (U.mapHomeomorph h).opens
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) n).hom ≫ Pi.π _ a =
      (cechTermIso U.opens P n).hom ≫ Pi.π _ (h.symm.toEquiv ∘ a) ≫
        P.map (homeomorphTupleComparison h U n a).op := by
  simp only [cechComplexHomeomorphIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, HomologicalComplex.comp_f, Category.assoc,
    cechComplex_comp_f_comp_term_π]
  rw [cechComplex_eqToIso_hom_app_f_π_assoc P (U.opens ∘ h.symm.toEquiv)
    (fun y ↦ h.opensCongr.symm.equivalence.functor.obj ((U.mapHomeomorph h).opens y))
    (inverseOpens_mapHomeomorph h U).symm n a]
  rw [cechComplex_reindex_inv_f_comp_term_π_assoc h U P n a]
  simp only [homeomorphTupleComparison, op_comp, Functor.map_comp]

/-- Transport through a homeomorphism preserves restriction of a global section to its cover. -/
@[reassoc]
theorem cechAugmentation_comp_cechComplexHomeomorphIso [HasZeroObject A] :
    cechAugmentation U.opens isTerminalTop P ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P =
      (CochainComplex.single₀ A).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op) ≫
        cechAugmentation (U.mapHomeomorph h).opens isTerminalTop
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) := by
  refine HomologicalComplex.from_single_hom_ext (Pi.hom_ext _ _ fun a ↦ ?_)
  have hc := cechComplexHomeomorphIso_hom_app_f_π h U P 0 a
  dsimp only [cechTermIso, Iso.refl_hom] at hc
  have hc' : ((cechComplexHomeomorphIso (A := A) h U).hom.app P).f 0 ≫ Pi.π _ a =
      Pi.π _ (h.symm.toEquiv ∘ a) ≫ P.map (homeomorphTupleComparison h U 0 a).op :=
    (_ ≫= (Category.id_comp _).symm).trans (hc.trans (Category.id_comp _))
  have hl := (Category.assoc _ _ _).trans ((_ ≫= hc').trans
    ((Category.assoc _ _ _).symm.trans
      ((cechAugmentation_f_zero_comp_π U.opens isTerminalTop P _ =≫ _).trans
        (P.map_comp _ _).symm)))
  have hr := (Category.assoc (P.map (eqToHom h.opensCongr.symm.map_top).op) _ _).trans
    (_ ≫= cechAugmentation_f_zero_comp_π (U.mapHomeomorph h).opens isTerminalTop
      (h.opensCongr.symm.equivalence.functor.op ⋙ P) a)
  dsimp only [Functor.comp_map, Functor.op_map] at hr
  have hr' := ((CochainComplex.single₀_map_f_zero
    (P.map (eqToHom h.opensCongr.symm.map_top).op) =≫
      (cechAugmentation (U.mapHomeomorph h).opens isTerminalTop
        (h.opensCongr.symm.equivalence.functor.op ⋙ P)).f 0) =≫ Pi.π _ a).trans hr
  exact hl.trans ((P.congr_map (Subsingleton.elim _ _)).trans
    ((P.map_comp _ _).trans hr'.symm))

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
  exact (Category.assoc _ _ _).symm.trans
    ((cechAugmentation_comp_cechComplexHomeomorphIso h U P =≫ _).trans
      ((Category.assoc _ _ _).trans ((_ ≫= hn).trans
        ((Category.assoc _ _ _).symm.trans
          (((CochainComplex.single₀ A).map_comp _ _).symm =≫ _)))))

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
  exact (_ ≫= ha).trans ((Category.assoc _ _ _).symm.trans
    ((hs =≫ _).trans (Category.assoc _ _ _)))

omit [HasProducts.{v} A] in
private lemma cechReading_map_eq_of_tuple_eq (V : PointOpenCover X) (n : ℕ)
    {a b : Fin (n + 1) → X} (hab : a = b) {W : Opens X}
    (f : W ⟶ ∏ᶜ fun j ↦ V.opens (a j)) (g : W ⟶ ∏ᶜ fun j ↦ V.opens (b j)) :
    (cechTermIso V.opens P n).hom ≫ Pi.π _ a ≫ P.map f.op =
      (cechTermIso V.opens P n).hom ≫ Pi.π _ b ≫ P.map g.op := by
  subst b
  rw [Subsingleton.elim f g]

/-- Native transport of Čech complexes commutes with every actual refinement function. -/
@[reassoc]
theorem cechComplexHomeomorphIso_hom_app_comp_cechComplexMap {V : PointOpenCover X}
    (φ : U.toFormalCoproduct ⟶ V.toFormalCoproduct) :
    cechComplexMap (U := U.opens) (V := V.opens) P φ ≫
        (cechComplexHomeomorphIso (A := A) h U).hom.app P =
      (cechComplexHomeomorphIso (A := A) h V).hom.app P ≫
        cechComplexMap (U := (U.mapHomeomorph h).opens) (V := (V.mapHomeomorph h).opens)
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) (U.mapHomeomorphHom h φ) := by
  ext n : 2
  simp only [HomologicalComplex.comp_f]
  apply (cancel_mono (cechTermIso (U.mapHomeomorph h).opens
    (h.opensCongr.symm.equivalence.functor.op ⋙ P) n).hom).mp
  refine Pi.hom_ext _ _ fun a ↦ ?_
  simp only [Category.assoc]
  rw [cechComplexHomeomorphIso_hom_app_f_π, cechComplexMap_f_comp_term_π_assoc,
    cechComplexMap_f_comp_term_π]
  refine Eq.trans ?_ (cechComplexHomeomorphIso_hom_app_f_π_assoc h V P n
    ((U.mapHomeomorphHom h φ).f ∘ a) _).symm
  simp only [Functor.comp_map, Functor.op_map, ← Functor.map_comp, ← op_comp]
  apply cechReading_map_eq_of_tuple_eq
  funext j
  simp [PointOpenCover.mapHomeomorphHom_f]

section Cohomology

variable [CategoryWithHomology A] (n : ℕ)

private def cechHomeomorphDiagramIso :
    (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := X))
      (fun _ _ hf ↦ hf) n).flip.obj P ≅
      (PointOpenCover.orderIsoOfHomeomorph h).equivalence.functor ⋙
        (cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := Y))
          (fun _ _ hf ↦ hf) n).flip.obj
          (h.opensCongr.symm.equivalence.functor.op ⋙ P) :=
  NatIso.ofComponents (fun U ↦ (HomologicalComplex.homologyFunctor A _ n).mapIso
      ((cechComplexHomeomorphIso (A := A) h U).app P)) (by
    intro U V f
    let φ := (leOfHom f).some
    let ψ := V.mapHomeomorphHom h φ
    change ((cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := X))
      (fun _ _ hf ↦ hf) n).map f).app P ≫ _ = _ ≫
        ((cechCohomologyDiagram A (PointOpenCover.toFormalCoproduct (X := Y))
          (fun _ _ hf ↦ hf) n).map
          ((PointOpenCover.orderIsoOfHomeomorph h).equivalence.functor.map f)).app
            (h.opensCongr.symm.equivalence.functor.op ⋙ P)
    rw [cechCohomologyDiagram_map A (PointOpenCover.toFormalCoproduct (X := X))
      (fun _ _ hf ↦ hf) n f φ,
      cechCohomologyDiagram_map A (PointOpenCover.toFormalCoproduct (X := Y)) (fun _ _ hf ↦ hf) n
        ((PointOpenCover.orderIsoOfHomeomorph h).equivalence.functor.map f) ψ]
    have hc := congrArg ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n).map)
      (cechComplexHomeomorphIso_hom_app_comp_cechComplexMap h V P φ)
    simp only [Functor.map_comp] at hc
    exact (cechComplexHomologyMap_app A n φ P =≫ _).trans
      (hc.trans (_ ≫= (cechComplexHomologyMap_app A n ψ
        (h.opensCongr.symm.equivalence.functor.op ⋙ P)).symm)))

variable [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]

private def cechHomeomorphObjIso :
    (cechCohomology X A n).obj P ≅
      (cechCohomology Y A n).obj (h.opensCongr.symm.equivalence.functor.op ⋙ P) :=
  HasColimit.isoOfEquivalence (PointOpenCover.orderIsoOfHomeomorph h).equivalence
    (cechHomeomorphDiagramIso h P n).symm

@[reassoc]
private lemma cechHomeomorphObjIso_ι (V : PointOpenCover X) :
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n V).app P ≫
        (cechHomeomorphObjIso h P n).hom =
      HomologicalComplex.homologyMap ((cechComplexHomeomorphIso (A := A) h V).hom.app P) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n
          (V.mapHomeomorph h)).app (h.opensCongr.symm.equivalence.functor.op ⋙ P) := by
  have he := HasColimit.ι_isoOfEquivalence_hom
    (PointOpenCover.orderIsoOfHomeomorph h).equivalence
    (cechHomeomorphDiagramIso h P n).symm V
  exact ((cechCohomologyι_app PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf) n V P =≫ _).trans he).trans
      (_ ≫= (cechCohomologyι_app PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n
        (V.mapHomeomorph h) (h.opensCongr.symm.equivalence.functor.op ⋙ P)).symm)

omit [Preadditive A] [HasProducts.{u} A] [HasProducts.{v} A] [CategoryWithHomology A] in
private lemma colimitIsoOfEquivalence_naturality
    {J K : Type*} [Category* J] [Category* K] (e : J ≌ K)
    {D₁ D₂ : J ⥤ A} {E₁ E₂ : K ⥤ A}
    [HasColimit D₁] [HasColimit D₂] [HasColimit E₁] [HasColimit E₂]
    (a : D₁ ⟶ D₂) (b : E₁ ⟶ E₂)
    (i₁ : D₁ ≅ e.functor ⋙ E₁) (i₂ : D₂ ≅ e.functor ⋙ E₂)
    (hc : ∀ j, a.app j ≫ i₂.hom.app j = i₁.hom.app j ≫ b.app (e.functor.obj j)) :
    colimMap a ≫ (HasColimit.isoOfEquivalence e i₂.symm).hom =
      (HasColimit.isoOfEquivalence e i₁.symm).hom ≫ colimMap b := by
  apply colimit.hom_ext
  intro j
  calc
    _ = a.app j ≫ colimit.ι D₂ j ≫ (HasColimit.isoOfEquivalence e i₂.symm).hom := by
      rw [← Category.assoc, ι_colimMap, Category.assoc]
    _ = a.app j ≫ i₂.hom.app j ≫ colimit.ι E₂ (e.functor.obj j) := by
      rw [HasColimit.ι_isoOfEquivalence_hom, Iso.symm_inv]
    _ = i₁.hom.app j ≫ b.app (e.functor.obj j) ≫
        colimit.ι E₂ (e.functor.obj j) := by rw [← Category.assoc, hc, Category.assoc]
    _ = i₁.hom.app j ≫ colimit.ι E₁ (e.functor.obj j) ≫ colimMap b := by
      rw [← ι_colimMap]
    _ = _ := (Category.assoc _ _ _).symm.trans
      (((HasColimit.ι_isoOfEquivalence_hom e i₁.symm j).symm =≫ _).trans
        (Category.assoc _ _ _))

private lemma cechHomeomorphObjIso_hom_naturality {Q : (Opens X)ᵒᵖ ⥤ A} (φ : P ⟶ Q) :
    (cechCohomology X A n).map φ ≫ (cechHomeomorphObjIso h Q n).hom =
      (cechHomeomorphObjIso h P n).hom ≫ (cechCohomology Y A n).map
        (Functor.whiskerLeft h.opensCongr.symm.equivalence.functor.op φ) := by
  let D := cechCohomologyDiagram.{u} A (PointOpenCover.toFormalCoproduct (X := X))
    (fun _ _ hf ↦ hf) n
  let E := cechCohomologyDiagram.{v} A (PointOpenCover.toFormalCoproduct (X := Y))
    (fun _ _ hf ↦ hf) n
  apply colimitIsoOfEquivalence_naturality
    (PointOpenCover.orderIsoOfHomeomorph h).equivalence (D.flip.map φ)
    (E.flip.map (Functor.whiskerLeft h.opensCongr.symm.equivalence.functor.op φ))
    (cechHomeomorphDiagramIso h P n) (cechHomeomorphDiagramIso h Q n)
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
theorem cechCohomologyZeroIso_hom_comp_homeomorphIso :
    (cechCohomologyZeroIso F).hom ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj ≫
        (cechCohomology Y A 0).map ((h.sheafCongrForgetIso A).inv.app F) =
      (F.obj.map (eqToHom h.opensCongr.symm.map_top).op ≫
        ((h.sheafCongrForgetIso A).inv.app F).app (op ⊤)) ≫
        (cechCohomologyZeroIso ((h.sheafCongr A).functor.obj F)).hom := by
  let U : PointOpenCover X := default
  let F' := (h.sheafCongr A).functor.obj F
  let φ := (h.sheafCongrForgetIso A).inv.app F
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
  have hp := (Category.assoc _ _ _).symm.trans
    ((hi =≫ (cechCohomology Y A 0).map φ).trans
      ((Category.assoc _ _ _).trans (_ ≫= hn)))
  have hc := cechAugmentationClass_comp_homeomorph_map_assoc h U F.obj F'.obj φ
    ((cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) 0
      (U.mapHomeomorph h)).app F'.obj)
  exact (hs =≫ _).trans ((Category.assoc _ _ _).trans
    ((_ ≫= Category.assoc _ _ _).trans
      ((_ ≫= (_ ≫= hp)).trans (hc.trans (_ ≫= ht.symm)))))

variable [HasSheafify (Opens.grothendieckTopology X) A]
  [HasSheafify (Opens.grothendieckTopology Y) A]

/-- The existing homeomorphism comparison of global sections commutes with the native
identifications of global sections and degree-zero Čech cohomology. -/
@[reassoc]
theorem sectionsIsoCechZero_hom_comp_homeomorphIso :
    (sectionsIsoCechZero F).hom ≫
        (cechCohomologyHomeomorphIso (A := A) h 0).hom.app F.obj ≫
        (cechCohomology Y A 0).map ((h.sheafCongrForgetIso A).inv.app F) =
      (h.globalSectionsIso A).hom.app F ≫
        (sectionsIsoCechZero ((h.sheafCongr A).functor.obj F)).hom := by
  rw [sectionsIsoCechZero_hom, Category.assoc, cechCohomologyZeroIso_hom_comp_homeomorphIso,
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
theorem cechComplexHomeomorphIso_hom_app_δ
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
theorem cechCohomologyHomeomorphIso_hom_app_δ
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
  have hlocal := cechComplexHomeomorphIso_hom_app_δ h V
    (hT.map_of_exact (cechComplexFunctor V.opens)) n
  have htarget := cechCohomologyι_app_δ PointOpenCover.toFormalCoproduct
    (fun _ _ hf ↦ hf)
    (fun V : PointOpenCover Y ↦ (hT.map_of_exact
      ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ A).obj
        h.opensCongr.symm.equivalence.functor.op)).map_of_exact
          (cechComplexFunctor V.opens)) n (V.mapHomeomorph h)
  have hq₁ := cechCohomologyHomeomorphIso_hom_app_ι h T.X₁ (n + 1) V
  have hq₃ := cechCohomologyHomeomorphIso_hom_app_ι h T.X₃ n V
  exact (Category.assoc _ _ _).symm.trans
    ((hsource =≫ _).trans ((Category.assoc _ _ _).trans
      ((_ ≫= hq₁).trans ((Category.assoc _ _ _).symm.trans
        ((hlocal =≫ _).trans ((Category.assoc _ _ _).trans
          ((_ ≫= htarget.symm).trans ((Category.assoc _ _ _).symm.trans
            ((hq₃.symm =≫ _).trans (Category.assoc _ _ _))))))))))


end TauCeti.Topology
