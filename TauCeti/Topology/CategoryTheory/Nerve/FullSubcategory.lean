/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ComposableArrows.FullSubcategory
public import TauCeti.Topology.CategoryTheory.ComposableArrows
public import TauCeti.Topology.CategoryTheory.FullSubcategory

/-!
# Nerves of open full subcategories

Full restriction to an open set of objects gives an open subspace in each degree of the
topological nerve. Only continuity of source is needed: each vertex is the source of its
identity arrow. The nerve topology and the full-subcategory arrow topology are the existing
ones, so no extra continuity or separation condition is imposed on individual hom types.
-/

public section

open CategoryTheory Topology Set

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C)

/-- Restriction to an open set of objects is levelwise an open embedding on topological
nerves. Saturation is not necessary for this levelwise assertion. -/
theorem isOpenEmbedding_mapComposableArrows_ι
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hP : IsOpen {x | P x}) (n : ℕ) :
    IsOpenEmbedding (P.ι.mapComposableArrows n).obj := by
  refine ⟨ComposableArrows.isEmbedding_mapComposableArrows_obj
    TauCeti.isEmbedding_total_fullSubcategory, ?_⟩
  rw [P.range_mapComposableArrows_ι]
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦ hP.preimage (ComposableArrows.continuous_obj hs i)

end CategoryTheory.ObjectProperty
