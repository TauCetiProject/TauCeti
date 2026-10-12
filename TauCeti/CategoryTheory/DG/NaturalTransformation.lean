/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Functor
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.CategoryTheory.Enriched.NaturalTransformation

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
  UnitGradedNatTrans F G

namespace DGNatTrans

/-- The identity DG natural transformation. -/
noncomputable def id (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    DGNatTrans F F := UnitGradedNatTrans.id F

/-- Composition of DG natural transformations. -/
noncomputable def comp {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) : DGNatTrans F H :=
  UnitGradedNatTrans.unitComp α β

/-- The component of the identity DG natural transformation. -/
@[simp]
theorem id_app (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)
    (X : C) : (id F).app X = eId _ (F.obj X) := by
  simp only [id, UnitGradedNatTrans.id_app]
  rfl

/-- The component of a composite DG natural transformation. -/
@[simp]
theorem comp_app {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) (X : C) :
    (comp α β).app X = eHomEquiv _
      (ForgetEnrichment.homOf _ (α.app X) ≫ ForgetEnrichment.homOf _ (β.app X)) := by
  simp only [comp, UnitGradedNatTrans.unitComp_app]
  rfl

end DGNatTrans

/-- DG functors with closed degree-zero DG natural transformations as morphisms. -/
@[ext]
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
    simp [DGNatTrans.comp_app, DGNatTrans.id_app, eHomEquiv]
    rfl
  comp_id := by
    intro F G α
    apply GradedNatTrans.ext
    funext X
    simp [DGNatTrans.comp_app, DGNatTrans.id_app, eHomEquiv]
    rfl
  assoc := by
    intro F G H I α β γ
    apply GradedNatTrans.ext
    funext X
    simp only [DGNatTrans.comp_app, eHomEquiv]
    -- Composition of unit-shaped components reduces to ordinary composition in `Z⁰`.
    change (ForgetEnrichment.homOf _ (α.app X) ≫
        ForgetEnrichment.homOf _ (β.app X)) ≫
        ForgetEnrichment.homOf _ (γ.app X) =
      ForgetEnrichment.homOf _ (α.app X) ≫
        (ForgetEnrichment.homOf _ (β.app X) ≫
          ForgetEnrichment.homOf _ (γ.app X))
    exact Category.assoc _ _ _

namespace DGNatTrans

/-- The component of a DG natural transformation on the homotopy category is the
homotopy class of its closed degree-zero component. -/
noncomputable def mapDGHomotopyCategory
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
      ((UnitGradedNatTrans.toOrdinary α).naturality
        (TauCeti.dgClosedHomOf R g hg))
    simp only [UnitGradedNatTrans.toOrdinary_app] at h
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
    -- The forgetful object wrappers reduce to the same DG objects.
    exact h

/-- On an object, the induced transformation is the homotopy class of the closed component. -/
@[simp]
theorem mapDGHomotopyCategory_app
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G)
    (X : C) :
    (mapDGHomotopyCategory α).app (TauCeti.DGHomotopyCategory.of R X) =
      TauCeti.DGHomotopyCategory.homOf R
        (TauCeti.dgClosedHom R
          (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
            (α.app X)))
        (TauCeti.dgClosedHom_mem_dgCycles R _) := by
  unfold mapDGHomotopyCategory
  dsimp only [TauCeti.DGHomotopyCategory.underlying_of]
  exact TauCeti.dgClosedToHomotopy_map R _

/-- A component of the induced transformation vanishes exactly when the corresponding closed
degree-zero DG morphism is a boundary. -/
-- This remains outside `simp`: `mapDGHomotopyCategory_app` already reduces its left side.
theorem mapDGHomotopyCategory_app_eq_zero_iff
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G)
    (X : C) :
    (mapDGHomotopyCategory α).app (TauCeti.DGHomotopyCategory.of R X) = 0 ↔
      TauCeti.dgClosedHom R
        (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
          (α.app X)) ∈
          TauCeti.dgBoundaries R (F.obj X) (G.obj X) := by
  unfold mapDGHomotopyCategory
  dsimp only [TauCeti.DGHomotopyCategory.underlying_of]
  exact TauCeti.dgClosedToHomotopy_map_eq_zero_iff (C := D) R _

/-- Passing the identity DG transformation to `H⁰` gives the identity transformation. -/
@[simp]
theorem mapDGHomotopyCategory_id
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    mapDGHomotopyCategory (DGNatTrans.id F) = 𝟙 F.mapDGHomotopyCategory := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategory, NatTrans.id_app, DGNatTrans.id_app]
  -- The identity component is the enriched identity after forgetting enrichment.
  exact (TauCeti.dgClosedToHomotopy (C := D) R).map_id _

/-- Passing a composite of DG transformations to `H⁰` composes their images. -/
@[simp]
theorem mapDGHomotopyCategory_comp
    {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) :
    mapDGHomotopyCategory (DGNatTrans.comp α β) =
      mapDGHomotopyCategory α ≫ mapDGHomotopyCategory β := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategory, NatTrans.comp_app, DGNatTrans.comp_app]
  -- The composite's unit-graded component is ordinary composition under `homOf`.
  exact (TauCeti.dgClosedToHomotopy (C := D) R).map_comp _ _

end DGNatTrans

/-- Taking `H⁰` sends DG functors and DG natural transformations to ordinary functors and
natural transformations. -/
@[expose]
noncomputable def mapDGHomotopyCategoryFunctor :
    DGFunctor R C D ⥤
      (TauCeti.DGHomotopyCategory R C ⥤ TauCeti.DGHomotopyCategory R D) where
  obj F := F.toEnrichedFunctor.mapDGHomotopyCategory
  map α := DGNatTrans.mapDGHomotopyCategory α
  map_id F := DGNatTrans.mapDGHomotopyCategory_id F.toEnrichedFunctor
  map_comp α β := DGNatTrans.mapDGHomotopyCategory_comp α β

/-- On objects, the functor takes a DG functor to its induced functor on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_obj (F : DGFunctor R C D) :
    mapDGHomotopyCategoryFunctor.obj F = F.toEnrichedFunctor.mapDGHomotopyCategory :=
  (rfl)

/-- On morphisms, the functor takes a DG transformation to its induced transformation on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_map {F G : DGFunctor R C D} (α : F ⟶ G) :
    mapDGHomotopyCategoryFunctor.map α = DGNatTrans.mapDGHomotopyCategory α :=
  (rfl)

end TauCeti
