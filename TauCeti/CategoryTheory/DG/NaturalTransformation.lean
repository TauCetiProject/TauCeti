/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Functor

/-!
# DG natural transformations on homotopy categories

Mathlib represents a natural transformation of functors enriched in complexes by a natural
transformation of their underlying functors. Its components are therefore closed degree-zero
arrows. Passing each component to cohomology gives a natural transformation between the induced
functors on `H⁰`. This is the degree-zero transformation used when comparing DG functors up to
homotopy; boundaries disappear from its components.

The construction uses Mathlib's `EnrichedNatTrans` and the closed-morphism comparison rather
than introducing another notion of DG natural transformation.

## Reference

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory

universe v u₁ u₂

namespace CategoryTheory.EnrichedFunctor

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
variable [TauCeti.DGCategory R C] [TauCeti.DGCategory R D]

/-- The component of an enriched natural transformation on the homotopy category is the
homotopy class of its closed degree-zero component. -/
noncomputable def mapDGHomotopyCategoryNatTrans
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D} (α : F ⟶ G) :
    F.mapDGHomotopyCategory ⟶ G.mapDGHomotopyCategory where
  app X := (TauCeti.dgClosedToHomotopy (C := D) R).map
    (α.out.app (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ)
      (TauCeti.DGHomotopyCategory.underlying R X)))
  naturality := by
    intro X Y f
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    obtain ⟨g, hg, rfl⟩ := TauCeti.exists_dgHomotopyClass_eq R f
    have h := congrArg (fun q => (TauCeti.dgClosedToHomotopy (C := D) R).map q)
      (α.out.naturality (TauCeti.dgClosedHomOf R g hg))
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
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D} (α : F ⟶ G)
    (X : C) :
    (mapDGHomotopyCategoryNatTrans α).app (TauCeti.DGHomotopyCategory.of R X) =
      TauCeti.DGHomotopyCategory.homOf R
        (TauCeti.dgClosedHom R
          (α.out.app (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)))
        (TauCeti.dgClosedHom_mem_dgCycles R _) := by
  unfold mapDGHomotopyCategoryNatTrans
  dsimp only [TauCeti.DGHomotopyCategory.underlying_of]
  exact TauCeti.dgClosedToHomotopy_map R _

/-- A component of the induced transformation vanishes exactly when the corresponding closed
degree-zero DG morphism is a boundary. -/
theorem mapDGHomotopyCategoryNatTrans_app_eq_zero_iff
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D} (α : F ⟶ G)
    (X : C) :
    (mapDGHomotopyCategoryNatTrans α).app (TauCeti.DGHomotopyCategory.of R X) = 0 ↔
      TauCeti.dgClosedHom R
        (α.out.app (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X)) ∈
          TauCeti.dgBoundaries R (F.obj X) (G.obj X) := by
  rw [mapDGHomotopyCategoryNatTrans_app]
  exact TauCeti.DGHomotopyCategory.homOf_eq_zero_iff R _

/-- Passing the identity enriched transformation to `H⁰` gives the identity transformation. -/
@[simp]
theorem mapDGHomotopyCategoryNatTrans_id
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    mapDGHomotopyCategoryNatTrans (𝟙 F) = 𝟙 F.mapDGHomotopyCategory := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategoryNatTrans, NatTrans.id_app]
  exact (TauCeti.dgClosedToHomotopy (C := D) R).map_id _

/-- Passing a composite of enriched transformations to `H⁰` composes their images. -/
@[simp]
theorem mapDGHomotopyCategoryNatTrans_comp
    {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : F ⟶ G) (β : G ⟶ H) :
    mapDGHomotopyCategoryNatTrans (α ≫ β) =
      mapDGHomotopyCategoryNatTrans α ≫ mapDGHomotopyCategoryNatTrans β := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategoryNatTrans, NatTrans.comp_app]
  exact (TauCeti.dgClosedToHomotopy (C := D) R).map_comp _ _

/-- Degree-zero homotopy takes DG functors and enriched transformations to functors and
transformations between homotopy categories. -/
@[expose]
noncomputable def mapDGHomotopyCategoryFunctor :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D ⥤
      (TauCeti.DGHomotopyCategory R C ⥤ TauCeti.DGHomotopyCategory R D) where
  obj F := F.mapDGHomotopyCategory
  map α := mapDGHomotopyCategoryNatTrans α
  map_id := mapDGHomotopyCategoryNatTrans_id
  map_comp := mapDGHomotopyCategoryNatTrans_comp

/-- The functor on functor categories sends a DG functor to its induced functor on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_obj
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    mapDGHomotopyCategoryFunctor.obj F = F.mapDGHomotopyCategory :=
  (rfl)

/-- The functor on functor categories sends an enriched transformation to the induced
transformation on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_map
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D} (α : F ⟶ G) :
    mapDGHomotopyCategoryFunctor.map α = mapDGHomotopyCategoryNatTrans α :=
  (rfl)

end CategoryTheory.EnrichedFunctor
