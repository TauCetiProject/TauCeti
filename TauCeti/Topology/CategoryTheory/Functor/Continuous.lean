/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
public import TauCeti.Topology.CategoryTheory.FullSubcategory
public import TauCeti.Topology.CategoryTheory.Prod

/-!
# Continuous functors on total arrows

`CategoryTheory.Functor.IsTopologicallyContinuous` asks for continuity on objects and on
`Quiver.Total` arrows, with their separately supplied topologies. Unlike continuity on each
hom type, this controls arrows whose endpoints vary. It is unrelated to continuity of functors
between sites.

Continuous functors are closed under identities, composition, products and full restriction.
The product and full-subcategory criteria express the corresponding universal properties with
the existing product and subspace topologies. For topological groupoids, continuity on total
arrows alone implies continuity on objects, by inserting units and taking sources. No
separation assumptions, or topology on individual hom types, are needed.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open Topology

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {K : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} K]
  [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace K]
  [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]
  [TopologicalSpace (Quiver.Total E)] [TopologicalSpace (Quiver.Total K)]

/-- A functor continuous on objects and on the total arrow space. The arrow topology is not
required to be a disjoint-union topology of its hom types. -/
structure IsTopologicallyContinuous (F : C ⥤ D) : Prop where
  /-- Continuity of the object map. -/
  continuous_obj : Continuous F.obj
  /-- Continuity of the map on total arrows, allowing endpoints to vary. -/
  continuous_mapTotal : Continuous F.toPrefunctor.mapTotal

/-- The identity functor is continuous for any object and total-arrow topologies. -/
@[simp]
theorem isTopologicallyContinuous_id : (𝟭 C).IsTopologicallyContinuous :=
  ⟨continuous_id, continuous_id⟩

/-- Composition preserves continuity on objects and total arrows. -/
theorem IsTopologicallyContinuous.comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : F.IsTopologicallyContinuous) (hG : G.IsTopologicallyContinuous) :
    (F ⋙ G).IsTopologicallyContinuous :=
  ⟨hG.continuous_obj.comp hF.continuous_obj,
    hG.continuous_mapTotal.comp hF.continuous_mapTotal⟩

/-- The first product projection is continuous on objects and total arrows. -/
@[simp]
theorem isTopologicallyContinuous_fst :
    (CategoryTheory.Prod.fst C D).IsTopologicallyContinuous := by
  refine ⟨continuous_fst, ?_⟩
  convert continuous_fst.comp (TauCeti.totalProdHomeomorph C D).continuous using 1
  funext a
  rw [Function.comp_apply, TauCeti.totalProdHomeomorph_apply]
  rfl

/-- The second product projection is continuous on objects and total arrows. -/
@[simp]
theorem isTopologicallyContinuous_snd :
    (CategoryTheory.Prod.snd C D).IsTopologicallyContinuous := by
  refine ⟨continuous_snd, ?_⟩
  convert continuous_snd.comp (TauCeti.totalProdHomeomorph C D).continuous using 1
  funext a
  rw [Function.comp_apply, TauCeti.totalProdHomeomorph_apply]
  rfl

/-- A functor to a product is continuous exactly when both projections are continuous. -/
theorem isTopologicallyContinuous_iff_proj (F : C ⥤ D × E) :
    F.IsTopologicallyContinuous ↔
      (F ⋙ CategoryTheory.Prod.fst D E).IsTopologicallyContinuous ∧
      (F ⋙ CategoryTheory.Prod.snd D E).IsTopologicallyContinuous := by
  constructor
  · intro hF
    exact ⟨hF.comp isTopologicallyContinuous_fst, hF.comp isTopologicallyContinuous_snd⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁.continuous_obj.prodMk h₂.continuous_obj, ?_⟩
    apply (TauCeti.totalProdHomeomorph D E).isInducing.continuous_iff.mpr
    convert h₁.continuous_mapTotal.prodMk h₂.continuous_mapTotal using 1
    funext a
    rw [Function.comp_apply, TauCeti.totalProdHomeomorph_apply]
    rfl

/-- Pairing continuous functors with a common source is continuous. -/
theorem IsTopologicallyContinuous.prod' {F : C ⥤ D} {G : C ⥤ E}
    (hF : F.IsTopologicallyContinuous) (hG : G.IsTopologicallyContinuous) :
    (F.prod' G).IsTopologicallyContinuous := by
  apply (isTopologicallyContinuous_iff_proj _).mpr
  -- Projection after pairing recovers the original object and arrow maps.
  exact ⟨hF, hG⟩

/-- Products of continuous functors are continuous for the product arrow topologies. -/
theorem IsTopologicallyContinuous.prod {F : C ⥤ D} {G : E ⥤ K}
    (hF : F.IsTopologicallyContinuous) (hG : G.IsTopologicallyContinuous) :
    (F.prod G).IsTopologicallyContinuous :=
  (isTopologicallyContinuous_fst.comp hF).prod' (isTopologicallyContinuous_snd.comp hG)

/-- Inclusion of a full subcategory is continuous for its subspace topologies. -/
@[simp]
theorem isTopologicallyContinuous_ι (P : ObjectProperty C) : P.ι.IsTopologicallyContinuous :=
  ⟨TauCeti.isEmbedding_obj_fullSubcategory.continuous,
    TauCeti.isEmbedding_total_fullSubcategory.continuous⟩

/-- Continuity into a full subcategory is detected after its inclusion. -/
@[simp]
theorem isTopologicallyContinuous_comp_ι_iff (P : ObjectProperty D)
    (F : C ⥤ P.FullSubcategory) :
    (F ⋙ P.ι).IsTopologicallyContinuous ↔ F.IsTopologicallyContinuous := by
  constructor
  · intro hF
    exact ⟨TauCeti.isEmbedding_obj_fullSubcategory.continuous_iff.mpr hF.continuous_obj,
      TauCeti.isEmbedding_total_fullSubcategory.continuous_iff.mpr hF.continuous_mapTotal⟩
  · exact fun hF ↦ hF.comp (isTopologicallyContinuous_ι P)

/-- Lifting a continuous functor whose objects satisfy a property preserves continuity. -/
theorem IsTopologicallyContinuous.lift {F : C ⥤ D} (hF : F.IsTopologicallyContinuous)
    (P : ObjectProperty D) (h : ∀ X, P (F.obj X)) :
    (P.lift F h).IsTopologicallyContinuous := by
  apply (isTopologicallyContinuous_comp_ι_iff P _).mp
  -- The lift followed by inclusion has exactly the original object and arrow maps.
  exact hF

/-- Restricting a continuous functor to full subcategories preserves continuity, without any
openness or invariance condition on the object properties. -/
theorem IsTopologicallyContinuous.restrict {F : C ⥤ D} (hF : F.IsTopologicallyContinuous)
    (P : ObjectProperty C) (Q : ObjectProperty D) (h : ∀ X, P X → Q (F.obj X)) :
    (Q.lift (P.ι ⋙ F) (fun X ↦ h X.obj X.property)).IsTopologicallyContinuous :=
  ((isTopologicallyContinuous_ι P).comp hF).lift Q _

/-- Inclusion between nested full subcategories is continuous. -/
@[simp]
theorem isTopologicallyContinuous_ιOfLE {P Q : ObjectProperty C} (h : P ≤ Q) :
    (ObjectProperty.ιOfLE h).IsTopologicallyContinuous := by
  apply (isTopologicallyContinuous_comp_ι_iff Q _).mp
  -- Both composites are the same inclusion on objects and total arrows.
  exact isTopologicallyContinuous_ι P

/-- With continuous source units and target source map, continuity on total arrows implies
continuity on objects. No invertibility of arrows is needed. -/
theorem isTopologicallyContinuous_iff_continuous_mapTotal_of_continuous_unit_source
    (F : C ⥤ D) (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hs : Continuous (Quiver.Total.left : Quiver.Total D → D)) :
    F.IsTopologicallyContinuous ↔ Continuous F.toPrefunctor.mapTotal := by
  refine ⟨fun hF ↦ hF.continuous_mapTotal, fun hF ↦ ⟨?_, hF⟩⟩
  exact hs.comp (hF.comp hu)

/-- For topological groupoids, continuity of a functor is detected on total arrows alone. -/
theorem isTopologicallyContinuous_iff_continuous_mapTotal
    [IsGroupoid C] [IsGroupoid D] [TauCeti.IsTopologicalGroupoid C]
    [TauCeti.IsTopologicalGroupoid D] (F : C ⥤ D) :
    F.IsTopologicallyContinuous ↔ Continuous F.toPrefunctor.mapTotal :=
  isTopologicallyContinuous_iff_continuous_mapTotal_of_continuous_unit_source F
    TauCeti.IsTopologicalGroupoid.continuous_unit
    TauCeti.IsTopologicalGroupoid.continuous_source

end CategoryTheory.Functor
