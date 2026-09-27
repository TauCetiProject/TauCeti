/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Functor

/-!
# DG natural transformations on homotopy categories

A DG natural transformation has closed degree-zero components that commute with every homogeneous
arrow. Mathlib's `EnrichedNatTrans` supplies the components and ordinary naturality; the extra
condition below supplies naturality on all degrees. Passing the components to cohomology gives a
natural transformation between the induced functors on `H⁰`.

## Reference

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory

universe v u₁ u₂

namespace TauCeti

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
variable [TauCeti.DGCategory R C] [TauCeti.DGCategory R D]

/-- A closed degree-zero DG natural transformation. Besides naturality on closed arrows, its
components commute with every homogeneous arrow. -/
structure DGNatTrans
    (F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) where
  /-- The closed degree-zero components and their ordinary naturality. -/
  toEnrichedNatTrans : F ⟶ G
  /-- Naturality on a homogeneous arrow of arbitrary degree. -/
  naturality : ∀ {X Y : C} (n : ℤ) (f : TauCeti.DGHom R n X Y),
    TauCeti.dgComp R (F.dgMap n f)
      (TauCeti.dgClosedHom R (toEnrichedNatTrans.out.app
        (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y))) (add_zero n) =
    TauCeti.dgComp R
      (TauCeti.dgClosedHom R (toEnrichedNatTrans.out.app
        (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
      (G.dgMap n f) (zero_add n)

namespace DGNatTrans

/-- Two DG transformations with the same underlying enriched transformation are equal. -/
@[ext]
theorem ext {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    {α β : DGNatTrans F G}
    (h : α.toEnrichedNatTrans = β.toEnrichedNatTrans) : α = β := by
  cases α with
  | mk a ha =>
    cases β with
    | mk b hb =>
      cases h
      rfl

/-- The identity DG natural transformation. -/
@[expose]
noncomputable def id (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    DGNatTrans F F where
  toEnrichedNatTrans := 𝟙 F
  naturality := by
    intro X Y n f
    change TauCeti.dgComp R (F.dgMap n f)
      (TauCeti.dgClosedHom R
        (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) (F.obj Y))))
      (add_zero n) =
      TauCeti.dgComp R
        (TauCeti.dgClosedHom R
          (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) (F.obj X))))
        (F.dgMap n f) (zero_add n)
    have hY := TauCeti.dgClosedHom_id (C := D) R
      (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) (F.obj Y))
    have hX := TauCeti.dgClosedHom_id (C := D) R
      (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) (F.obj X))
    rw [hY, hX]
    simp only [ForgetEnrichment.to_of, TauCeti.dgComp_dgId, TauCeti.dgId_dgComp]

/-- Composition of DG natural transformations. -/
@[expose]
noncomputable def comp {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) : DGNatTrans F H where
  toEnrichedNatTrans := α.toEnrichedNatTrans ≫ β.toEnrichedNatTrans
  naturality := by
    intro X Y n f
    change TauCeti.dgComp R (F.dgMap n f)
      (TauCeti.dgClosedHom R
        (α.toEnrichedNatTrans.out.app
          (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y) ≫
        β.toEnrichedNatTrans.out.app
          (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y))) (add_zero n) =
      TauCeti.dgComp R
        (TauCeti.dgClosedHom R
          (α.toEnrichedNatTrans.out.app
            (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X) ≫
          β.toEnrichedNatTrans.out.app
            (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
        (H.dgMap n f) (zero_add n)
    have hY := TauCeti.dgClosedHom_comp (C := D) R
      (α.toEnrichedNatTrans.out.app
        (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y))
      (β.toEnrichedNatTrans.out.app
        (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y))
    have hX := TauCeti.dgClosedHom_comp (C := D) R
      (α.toEnrichedNatTrans.out.app
        (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X))
      (β.toEnrichedNatTrans.out.app
        (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X))
    rw [hY, hX]
    simp only [TauCeti.dgCompZero_def]
    calc
      TauCeti.dgComp R (F.dgMap n f)
          (TauCeti.dgComp R
            (TauCeti.dgClosedHom R (α.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y)))
            (TauCeti.dgClosedHom R (β.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y)))
            (zero_add 0)) (add_zero n) =
        TauCeti.dgComp R
          (TauCeti.dgComp R (F.dgMap n f)
            (TauCeti.dgClosedHom R (α.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y)))
            (add_zero n))
          (TauCeti.dgClosedHom R (β.toEnrichedNatTrans.out.app
            (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y)))
          (add_zero n) := by rw [TauCeti.dgComp_assoc]; omega
      _ = TauCeti.dgComp R
          (TauCeti.dgComp R
            (TauCeti.dgClosedHom R (α.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
            (G.dgMap n f) (zero_add n))
          (TauCeti.dgClosedHom R (β.toEnrichedNatTrans.out.app
            (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y)))
          (add_zero n) := by rw [α.naturality n f]
      _ = TauCeti.dgComp R
          (TauCeti.dgClosedHom R (α.toEnrichedNatTrans.out.app
            (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
          (TauCeti.dgComp R (G.dgMap n f)
            (TauCeti.dgClosedHom R (β.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y)))
            (add_zero n)) (zero_add n) := by rw [TauCeti.dgComp_assoc]; omega
      _ = TauCeti.dgComp R
          (TauCeti.dgClosedHom R (α.toEnrichedNatTrans.out.app
            (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
          (TauCeti.dgComp R
            (TauCeti.dgClosedHom R (β.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
            (H.dgMap n f) (zero_add n)) (zero_add n) := by rw [β.naturality n f]
      _ = TauCeti.dgComp R
          (TauCeti.dgComp R
            (TauCeti.dgClosedHom R (α.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
            (TauCeti.dgClosedHom R (β.toEnrichedNatTrans.out.app
              (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
            (zero_add 0))
          (H.dgMap n f) (zero_add n) := by rw [TauCeti.dgComp_assoc]; omega

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
    apply DGNatTrans.ext
    change (𝟙 F.toEnrichedFunctor) ≫ α.toEnrichedNatTrans = α.toEnrichedNatTrans
    simp
  comp_id := by
    intro F G α
    apply DGNatTrans.ext
    change α.toEnrichedNatTrans ≫ (𝟙 G.toEnrichedFunctor) = α.toEnrichedNatTrans
    simp
  assoc := by
    intro F G H I α β γ
    apply DGNatTrans.ext
    change (α.toEnrichedNatTrans ≫ β.toEnrichedNatTrans) ≫ γ.toEnrichedNatTrans =
      α.toEnrichedNatTrans ≫ (β.toEnrichedNatTrans ≫ γ.toEnrichedNatTrans)
    simp only [Category.assoc]

/-- The component of a DG natural transformation on the homotopy category is the
homotopy class of its closed degree-zero component. -/
noncomputable def mapDGHomotopyCategoryNatTrans
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) :
    F.mapDGHomotopyCategory ⟶ G.mapDGHomotopyCategory where
  app X := (TauCeti.dgClosedToHomotopy (C := D) R).map
    (α.toEnrichedNatTrans.out.app (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ)
      (TauCeti.DGHomotopyCategory.underlying R X)))
  naturality := by
    intro X Y f
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    obtain ⟨g, hg, rfl⟩ := TauCeti.exists_dgHomotopyClass_eq R f
    have h := congrArg (fun q => (TauCeti.dgClosedToHomotopy (C := D) R).map q)
      (α.toEnrichedNatTrans.out.naturality (TauCeti.dgClosedHomOf R g hg))
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
          (α.toEnrichedNatTrans.out.app
            (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
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
        (α.toEnrichedNatTrans.out.app
          (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)) ∈
          TauCeti.dgBoundaries R (F.obj X) (G.obj X) := by
  rw [mapDGHomotopyCategoryNatTrans_app]
  exact TauCeti.DGHomotopyCategory.homOf_eq_zero_iff R _

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
