/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Functor
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# DG natural transformations on homotopy categories

A DG natural transformation has closed degree-zero components that commute with every homogeneous
arrow. Mathlib's unit-graded `GradedNatTrans` supplies closed degree-zero components and naturality
on all degrees. Passing the components to cohomology gives a natural transformation between the
induced functors on `H⁰`.

## Reference

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory MonoidalCategory

universe v u₁ u₂

namespace TauCeti

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
variable [TauCeti.DGCategory R C] [TauCeti.DGCategory R D]

/-- Closed degree-zero DG natural transformations, using Mathlib's graded enriched
natural transformations at the monoidal unit. -/
abbrev DGNatTrans
    (F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :=
  GradedNatTrans
    ((Center.ofBraided (CochainComplex (ModuleCat.{v} R) ℤ)).obj
      (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))) F G

section GradedBridge

universe w
variable {V : Type v} [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
variable {C' : Type u₁} {D' : Type u₂} [EnrichedCategory V C'] [EnrichedCategory V D']

private theorem unit_braiding (H : V) :
    (λ_ H).inv ≫ (β_ (𝟙_ V) H).hom = (ρ_ H).inv := by
  have h : (β_ (𝟙_ V) H).hom = (λ_ H).hom ≫ (ρ_ H).inv :=
    ((ρ_ H).eq_comp_inv).mpr (braiding_rightUnitor H)
  rw [h]
  simp
private theorem unitGradedNaturality
    (F G : EnrichedFunctor V C' D') (X Y : C')
    (aX : 𝟙_ V ⟶ F.obj X ⟶[V] G.obj X)
    (aY : 𝟙_ V ⟶ F.obj Y ⟶[V] G.obj Y)
    (h : (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
      (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
      (aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y))
    (f : 𝟙_ V ⟶ X ⟶[V] Y) :
    (λ_ (𝟙_ V)).inv ≫ ((f ≫ F.map X Y) ⊗ₘ aY) ≫
      eComp V (F.obj X) (F.obj Y) (G.obj Y) =
    (λ_ (𝟙_ V)).inv ≫ (aX ⊗ₘ (f ≫ G.map X Y)) ≫
      eComp V (F.obj X) (G.obj X) (G.obj Y) := by
  have h' :
      (f ≫ (λ_ (X ⟶[V] Y)).inv) ≫
        ((β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
          (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y)) =
      (f ≫ (λ_ (X ⟶[V] Y)).inv) ≫
        ((aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)) := by rw [h]
  have hL :
      (λ_ (𝟙_ V)).inv ≫ ((f ≫ F.map X Y) ⊗ₘ aY) =
      f ≫ (λ_ (X ⟶[V] Y)).inv ≫
        (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ aY) := by
    rw [unitors_inv_equal, rightUnitor_inv_comp_tensorHom]
    calc
      _ = f ≫ ((ρ_ (X ⟶[V] Y)).inv ≫ (F.map X Y ⊗ₘ aY)) := by
        rw [rightUnitor_inv_comp_tensorHom]
        simp only [Category.assoc]
      _ = f ≫ (((λ_ (X ⟶[V] Y)).inv ≫
        (β_ (𝟙_ V) (X ⟶[V] Y)).hom) ≫ (F.map X Y ⊗ₘ aY)) := by
          rw [unit_braiding]
      _ = _ := by simp only [Category.assoc]
  have hR :
      (λ_ (𝟙_ V)).inv ≫ (aX ⊗ₘ (f ≫ G.map X Y)) =
      f ≫ (λ_ (X ⟶[V] Y)).inv ≫ (aX ⊗ₘ G.map X Y) := by
    simp only [leftUnitor_inv_comp_tensorHom, Category.assoc]
  calc
    _ = (f ≫ (λ_ (X ⟶[V] Y)).inv) ≫
      ((β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
        (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y)) := by
          simpa only [Category.assoc] using
            (congrArg (fun q => q ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y)) hL)
    _ = (f ≫ (λ_ (X ⟶[V] Y)).inv) ≫
      ((aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)) := h'
    _ = _ := by simpa only [Category.assoc] using
      (congrArg (fun q => q ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)) hR.symm)
private noncomputable def gradedNatTransToOrdinary
    {F G : EnrichedFunctor V C' D'}
    (α : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) :
    F.forget ⟶ G.forget where
  app X := α.app (ForgetEnrichment.to V X)
  naturality := by
    intro X Y f
    apply_fun ForgetEnrichment.homTo V
    · change
        ForgetEnrichment.homTo V
          (F.forget.map f ≫ ForgetEnrichment.homOf (C := D') V (α.app _)) =
        ForgetEnrichment.homTo V
          (ForgetEnrichment.homOf (C := D') V (α.app _) ≫ G.forget.map f)
      simp only [ForgetEnrichment.homTo_comp, EnrichedFunctor.forget_map]
      dsimp [ForgetEnrichment.homTo, ForgetEnrichment.homOf,
        ForgetEnrichment.to, ForgetEnrichment.of]
      simpa only [ForgetEnrichment.to, ForgetEnrichment.homTo, Category.assoc] using
        (unitGradedNaturality F G (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y)
          (α.app _) (α.app _) (α.naturality _ _) (ForgetEnrichment.homTo V f))
    · intro a b hab
      exact hab

private theorem unitNatSquare
    (F G : EnrichedFunctor V C' D') (X Y : C')
    (aX : 𝟙_ V ⟶ F.obj X ⟶[V] G.obj X)
    (aY : 𝟙_ V ⟶ F.obj Y ⟶[V] G.obj Y)
    (h : (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
      (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
      (aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)) :
    F.map X Y ≫ eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj X))
      (ForgetEnrichment.homOf V aY) =
    G.map X Y ≫ eHomWhiskerRight V (ForgetEnrichment.homOf V aX)
      (ForgetEnrichment.of V (G.obj Y)) := by
  change F.map X Y ≫ (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
    G.map X Y ≫ (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)
  apply (cancel_epi (λ_ (X ⟶[V] Y)).hom).mp
  have hb : (λ_ (X ⟶[V] Y)).hom ≫ (ρ_ (X ⟶[V] Y)).inv =
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom :=
    (((ρ_ (X ⟶[V] Y)).eq_comp_inv).mpr
      (braiding_rightUnitor (X ⟶[V] Y))).symm
  have hl : (λ_ (X ⟶[V] Y)).hom ≫ F.map X Y ≫
      (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY =
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ aY) := by
    calc
      _ = (λ_ (X ⟶[V] Y)).hom ≫
          ((ρ_ (X ⟶[V] Y)).inv ≫ (F.map X Y ⊗ₘ aY)) := by
            rw [rightUnitor_inv_comp_tensorHom]
      _ = ((λ_ (X ⟶[V] Y)).hom ≫ (ρ_ (X ⟶[V] Y)).inv) ≫
          (F.map X Y ⊗ₘ aY) := by simp only [Category.assoc]
      _ = _ := by rw [hb]
  have hr : (λ_ (X ⟶[V] Y)).hom ≫ G.map X Y ≫
      (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) = aX ⊗ₘ G.map X Y := by
    calc
      _ = (λ_ (X ⟶[V] Y)).hom ≫
          ((λ_ (X ⟶[V] Y)).inv ≫ (aX ⊗ₘ G.map X Y)) := by
            rw [leftUnitor_inv_comp_tensorHom]
      _ = _ := by simp
  calc
    _ = (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
        (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) := by
          simpa only [Category.assoc] using
            (congrArg (fun q => q ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y)) hl)
    _ = (aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y) := h
    _ = _ := by simpa only [Category.assoc] using
      (congrArg (fun q => q ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)) hr.symm)

private theorem unitNatSquareReverse
    (F G : EnrichedFunctor V C' D') (X Y : C')
    (aX : 𝟙_ V ⟶ F.obj X ⟶[V] G.obj X)
    (aY : 𝟙_ V ⟶ F.obj Y ⟶[V] G.obj Y)
    (hs : F.map X Y ≫ eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj X))
        (ForgetEnrichment.homOf V aY) =
      G.map X Y ≫ eHomWhiskerRight V (ForgetEnrichment.homOf V aX)
        (ForgetEnrichment.of V (G.obj Y))) :
    (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
      (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
    (aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y) := by
  change F.map X Y ≫ (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
    G.map X Y ≫ (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y) at hs
  have hb : (λ_ (X ⟶[V] Y)).hom ≫ (ρ_ (X ⟶[V] Y)).inv =
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom :=
    (((ρ_ (X ⟶[V] Y)).eq_comp_inv).mpr
      (braiding_rightUnitor (X ⟶[V] Y))).symm
  have hl : (λ_ (X ⟶[V] Y)).hom ≫ F.map X Y ≫
      (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY =
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ aY) := by
    calc
      _ = (λ_ (X ⟶[V] Y)).hom ≫
          ((ρ_ (X ⟶[V] Y)).inv ≫ (F.map X Y ⊗ₘ aY)) := by
            rw [rightUnitor_inv_comp_tensorHom]
      _ = ((λ_ (X ⟶[V] Y)).hom ≫ (ρ_ (X ⟶[V] Y)).inv) ≫
          (F.map X Y ⊗ₘ aY) := by simp only [Category.assoc]
      _ = _ := by rw [hb]
  have hr : (λ_ (X ⟶[V] Y)).hom ≫ G.map X Y ≫
      (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) = aX ⊗ₘ G.map X Y := by
    calc
      _ = (λ_ (X ⟶[V] Y)).hom ≫
          ((λ_ (X ⟶[V] Y)).inv ≫ (aX ⊗ₘ G.map X Y)) := by
            rw [leftUnitor_inv_comp_tensorHom]
      _ = _ := by simp
  calc
    _ = (λ_ (X ⟶[V] Y)).hom ≫ F.map X Y ≫
      (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) := by
        simpa only [Category.assoc] using
          (congrArg (fun q => q ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y)) hl.symm)
    _ = (λ_ (X ⟶[V] Y)).hom ≫ G.map X Y ≫
      (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y) := by
        simpa only [Category.assoc] using
          (congrArg (fun q => (λ_ (X ⟶[V] Y)).hom ≫ q) hs)
    _ = _ := by simpa only [Category.assoc] using
      (congrArg (fun q => q ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)) hr)

omit [BraidedCategory V] in
private theorem composeNaturalSquares
    {E : Type u₂} [Category E] [EnrichedOrdinaryCategory V E]
    {FX GX HX FY GY HY : E} {M : V}
    (fMap : M ⟶ FX ⟶[V] FY) (gMap : M ⟶ GX ⟶[V] GY)
    (hMap : M ⟶ HX ⟶[V] HY)
    (aX : FX ⟶ GX) (aY : FY ⟶ GY)
    (bX : GX ⟶ HX) (bY : GY ⟶ HY)
    (ha : fMap ≫ eHomWhiskerLeft V FX aY =
      gMap ≫ eHomWhiskerRight V aX GY)
    (hb : gMap ≫ eHomWhiskerLeft V GX bY =
      hMap ≫ eHomWhiskerRight V bX HY) :
    fMap ≫ eHomWhiskerLeft V FX (aY ≫ bY) =
      hMap ≫ eHomWhiskerRight V (aX ≫ bX) HY := by
  rw [eHomWhiskerLeft_comp, eHomWhiskerRight_comp]
  calc
    _ = gMap ≫ eHomWhiskerRight V aX GY ≫ eHomWhiskerLeft V FX bY := by
      simpa only [Category.assoc] using
        (congrArg (fun q => q ≫ eHomWhiskerLeft V FX bY) ha)
    _ = gMap ≫ eHomWhiskerLeft V GX bY ≫ eHomWhiskerRight V aX HY := by
      rw [eHom_whisker_exchange]
    _ = _ := by simpa only [Category.assoc] using
      (congrArg (fun q => q ≫ eHomWhiskerRight V aX HY) hb)


/-- Composition of graded natural transformations at the monoidal unit. -/
noncomputable def unitGradedNatTransComp {F G H : EnrichedFunctor V C' D'}
    (α : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
    (γ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G H) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F H where
  app X := eHomEquiv V
    (ForgetEnrichment.homOf V (α.app X) ≫ ForgetEnrichment.homOf V (γ.app X))
  naturality X Y := by
    have hα := unitNatSquare F G X Y (α.app X) (α.app Y) (α.naturality X Y)
    have hγ := unitNatSquare G H X Y (γ.app X) (γ.app Y) (γ.naturality X Y)
    dsimp [Center.ofBraided, Center.ofBraidedObj] at hα hγ ⊢
    apply unitNatSquareReverse F H X Y _ _
    let aX := ForgetEnrichment.homOf V (α.app X)
    let aY := ForgetEnrichment.homOf V (α.app Y)
    let bX := ForgetEnrichment.homOf V (γ.app X)
    let bY := ForgetEnrichment.homOf V (γ.app Y)
    change F.map X Y ≫ eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj X))
        (aY ≫ bY) =
      H.map X Y ≫ eHomWhiskerRight V (aX ≫ bX)
        (ForgetEnrichment.of V (H.obj Y))
    exact composeNaturalSquares (V := V) (F.map X Y) (G.map X Y) (H.map X Y)
      aX aY bX bY hα hγ

/-- Identity graded natural transformation at the monoidal unit. -/
noncomputable def unitGradedNatTransId (F : EnrichedFunctor V C' D') :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F where
  app X := eId V (F.obj X)
  naturality X Y := by
    dsimp [Center.ofBraided, Center.ofBraidedObj]
    simp only [tensorHom_def, Category.assoc]
    conv_rhs => rw [← whisker_exchange_assoc]
    have hcomp : ((F.obj X ⟶[V] F.obj Y) ◁ eId V (F.obj Y)) ≫
        eComp V (F.obj X) (F.obj Y) (F.obj Y) =
        (ρ_ (F.obj X ⟶[V] F.obj Y)).hom := by
      simpa using ((ρ_ (F.obj X ⟶[V] F.obj Y)).inv_comp_eq).mp
        (e_comp_id V (F.obj X) (F.obj Y))
    have hid : (eId V (F.obj X) ▷ (F.obj X ⟶[V] F.obj Y)) ≫
        eComp V (F.obj X) (F.obj X) (F.obj Y) =
        (λ_ (F.obj X ⟶[V] F.obj Y)).hom := by
      simpa using ((λ_ (F.obj X ⟶[V] F.obj Y)).inv_comp_eq).mp
        (e_id_comp V (F.obj X) (F.obj Y))
    rw [hcomp, hid, rightUnitor_naturality]
    calc
      _ = ((β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
          (ρ_ (X ⟶[V] Y)).hom) ≫ F.map X Y := by rw [Category.assoc]
      _ = (λ_ (X ⟶[V] Y)).hom ≫ F.map X Y := by rw [braiding_rightUnitor]
      _ = _ := by rw [leftUnitor_naturality]


end GradedBridge

namespace DGNatTrans

/-- The identity DG natural transformation. -/
@[expose]
noncomputable def id (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    DGNatTrans F F := unitGradedNatTransId F

/-- Composition of DG natural transformations. -/
@[expose]
noncomputable def comp {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) : DGNatTrans F H :=
  unitGradedNatTransComp α β

end DGNatTrans

/-- DG functors with closed degree-zero DG natural transformations as morphisms. -/
structure DGFunctor (R : Type v) [CommRing R] (C : Type u₁) (D : Type u₂)
    [TauCeti.DGCategory R C] [TauCeti.DGCategory R D] where
  /-- The underlying functor enriched in cochain complexes. -/
  toEnrichedFunctor : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D

noncomputable instance : Category (DGFunctor R C D) where
  Hom F G := DGNatTrans F.toEnrichedFunctor G.toEnrichedFunctor
  id F := DGNatTrans.id F.toEnrichedFunctor
  comp α β := DGNatTrans.comp α β
  id_comp := by
    intro F G α
    apply GradedNatTrans.ext
    funext X
    simp [DGNatTrans.comp, DGNatTrans.id, unitGradedNatTransComp, unitGradedNatTransId, eHomEquiv]
    rfl
  comp_id := by
    intro F G α
    apply GradedNatTrans.ext
    funext X
    simp [DGNatTrans.comp, DGNatTrans.id, unitGradedNatTransComp, unitGradedNatTransId, eHomEquiv]
    rfl
  assoc := by
    intro F G H I α β γ
    apply GradedNatTrans.ext
    funext X
    simp only [DGNatTrans.comp, unitGradedNatTransComp, eHomEquiv]
    change (ForgetEnrichment.homOf _ (α.app X) ≫
        ForgetEnrichment.homOf _ (β.app X)) ≫
        ForgetEnrichment.homOf _ (γ.app X) =
      ForgetEnrichment.homOf _ (α.app X) ≫
        (ForgetEnrichment.homOf _ (β.app X) ≫
          ForgetEnrichment.homOf _ (γ.app X))
    exact Category.assoc _ _ _

/-- The component of a DG natural transformation on the homotopy category is the
homotopy class of its closed degree-zero component. -/
noncomputable def mapDGHomotopyCategoryNatTrans
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) :
    F.mapDGHomotopyCategory ⟶ G.mapDGHomotopyCategory where
  app X := (TauCeti.dgClosedToHomotopy (C := D) R).map
    (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
      (α.app (TauCeti.DGHomotopyCategory.underlying R X)))
  naturality := by
    intro X Y f
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    obtain ⟨g, hg, rfl⟩ := TauCeti.exists_dgHomotopyClass_eq R f
    have h := congrArg (fun q => (TauCeti.dgClosedToHomotopy (C := D) R).map q)
      ((gradedNatTransToOrdinary α).naturality (TauCeti.dgClosedHomOf R g hg))
    rw [Functor.map_comp, Functor.map_comp] at h
    have hmap (J : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
        (TauCeti.dgClosedToHomotopy (C := D) R).map
          (J.forget.map (TauCeti.dgClosedHomOf R g hg)) =
          J.mapDGHomotopyCategory.map (TauCeti.dgHomotopyClass R g hg) := by
      simp only [EnrichedFunctor.forget_map]
      simp only [TauCeti.dgClosedToHomotopy_map, TauCeti.DGHomotopyCategory.homOf_def]
      simp only [J.dgClosedHom_forget_map]
      simp only [TauCeti.dgClosedHom_dgClosedHomOf, J.mapDGHomotopyCategory_map,
        TauCeti.homologyMap_dgHomotopyClass, J.dgMap_apply, ForgetEnrichment.to_of]
      rfl
    rw [← hmap F, ← hmap G]
    exact h

/-- On an object, the induced transformation is the homotopy class of the closed component. -/
@[simp]
theorem mapDGHomotopyCategoryNatTrans_app
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G)
    (X : C) :
    (mapDGHomotopyCategoryNatTrans α).app (TauCeti.DGHomotopyCategory.of R X) =
      TauCeti.DGHomotopyCategory.homOf R
        (TauCeti.dgClosedHom R
          (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
            (α.app X)))
        (TauCeti.dgClosedHom_mem_dgCycles R _) := by
  unfold mapDGHomotopyCategoryNatTrans
  dsimp only [TauCeti.DGHomotopyCategory.underlying_of]
  exact TauCeti.dgClosedToHomotopy_map R _

/-- A component of the induced transformation vanishes exactly when the corresponding closed
degree-zero DG morphism is a boundary. -/
theorem mapDGHomotopyCategoryNatTrans_app_eq_zero_iff
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G)
    (X : C) :
    (mapDGHomotopyCategoryNatTrans α).app (TauCeti.DGHomotopyCategory.of R X) = 0 ↔
      TauCeti.dgClosedHom R
        (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
          (α.app X)) ∈
          TauCeti.dgBoundaries R (F.obj X) (G.obj X) := by
  unfold mapDGHomotopyCategoryNatTrans
  dsimp only [TauCeti.DGHomotopyCategory.underlying_of]
  exact TauCeti.dgClosedToHomotopy_map_eq_zero_iff (C := D) R _

/-- Passing the identity DG transformation to `H⁰` gives the identity transformation. -/
@[simp]
theorem mapDGHomotopyCategoryNatTrans_id
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    mapDGHomotopyCategoryNatTrans (DGNatTrans.id F) = 𝟙 F.mapDGHomotopyCategory := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategoryNatTrans, NatTrans.id_app]
  exact (TauCeti.dgClosedToHomotopy (C := D) R).map_id _

/-- Passing a composite of DG transformations to `H⁰` composes their images. -/
@[simp]
theorem mapDGHomotopyCategoryNatTrans_comp
    {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) :
    mapDGHomotopyCategoryNatTrans (DGNatTrans.comp α β) =
      mapDGHomotopyCategoryNatTrans α ≫ mapDGHomotopyCategoryNatTrans β := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategoryNatTrans, NatTrans.comp_app]
  exact (TauCeti.dgClosedToHomotopy (C := D) R).map_comp _ _

/-- Taking `H⁰` sends DG functors and DG natural transformations to ordinary functors and
natural transformations. -/
@[expose]
noncomputable def mapDGHomotopyCategoryFunctor :
    DGFunctor R C D ⥤
      (TauCeti.DGHomotopyCategory R C ⥤ TauCeti.DGHomotopyCategory R D) where
  obj F := F.toEnrichedFunctor.mapDGHomotopyCategory
  map α := mapDGHomotopyCategoryNatTrans α
  map_id F := mapDGHomotopyCategoryNatTrans_id F.toEnrichedFunctor
  map_comp α β := mapDGHomotopyCategoryNatTrans_comp α β

/-- On objects, the functor takes a DG functor to its induced functor on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_obj (F : DGFunctor R C D) :
    mapDGHomotopyCategoryFunctor.obj F = F.toEnrichedFunctor.mapDGHomotopyCategory :=
  (rfl)

/-- On morphisms, the functor takes a DG transformation to its induced transformation on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_map {F G : DGFunctor R C D} (α : F ⟶ G) :
    mapDGHomotopyCategoryFunctor.map α = mapDGHomotopyCategoryNatTrans α :=
  (rfl)

end TauCeti
