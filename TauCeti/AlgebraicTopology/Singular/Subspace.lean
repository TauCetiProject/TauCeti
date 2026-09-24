/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Singular simplices of subspaces

The singular simplices of a subspace are characterized by the image of their underlying maps.
This identifies the range subcomplex of a subspace inclusion in a singular simplicial set.
-/

public section

open CategoryTheory Limits Topology

universe u

namespace TopCat

variable {X : TopCat.{u}}

/-- A singular simplex belongs to the range of a subspace inclusion exactly when its image is
contained in the subspace. -/
lemma mem_range_toSSet_subtypeVal_iff (S : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (toSSet.obj X).obj n) :
    σ ∈ (SSet.Subcomplex.range
      (toSSet.map (ofHom (ContinuousMap.subtypeVal S)))).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ S := by
  change σ ∈ Set.range ((toSSet.map (ofHom (ContinuousMap.subtypeVal S))).app n) ↔ _
  rw [(IsInducing.subtypeVal : IsInducing
    (ofHom (ContinuousMap.subtypeVal S))).mem_range_toSSet_map_app_iff n σ]
  change Set.range (X.toSSetObjEquiv n σ) ⊆ Set.range (Subtype.val : S → X) ↔ _
  rw [Subtype.range_coe]

end TopCat
