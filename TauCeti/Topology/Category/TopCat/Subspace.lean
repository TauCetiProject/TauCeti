/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.EpiMono
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Subspace inclusions in `TopCat`

The canonical inclusions of subspaces are monomorphisms. These instances supply the
monomorphism hypotheses for the subspace inclusions in the Mayer–Vietoris pushout square.
The singular simplices of a subspace are characterized by the image of their underlying maps.
-/

public section

open CategoryTheory Limits Topology

universe u

namespace TopCat

variable {X : TopCat.{u}}

/-- The inclusion of a subspace is a monomorphism of topological spaces. -/
instance mono_ofHom_subtypeVal (S : Set X) : Mono (ofHom (ContinuousMap.subtypeVal S)) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The inclusion of one subspace in another is a monomorphism of topological spaces. -/
instance mono_ofHom_inclusion {S T : Set X} (h : S ⊆ T) :
    Mono (ofHom (ContinuousMap.inclusion h)) :=
  (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective h)

/-- A singular simplex belongs to the range of a subspace inclusion exactly when its image is
contained in the subspace. -/
lemma mem_range_toSSet_subtypeVal_iff (S : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (toSSet.obj X).obj n) :
    σ ∈ (SSet.Subcomplex.range
      (toSSet.map (ofHom (ContinuousMap.subtypeVal S)))).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ S := by
  -- The range subcomplex is defined levelwise as the range of the induced map.
  change σ ∈ Set.range ((toSSet.map (ofHom (ContinuousMap.subtypeVal S))).app n) ↔ _
  rw [(IsInducing.subtypeVal : IsInducing
    (ofHom (ContinuousMap.subtypeVal S))).mem_range_toSSet_map_app_iff n σ]
  -- The underlying map of `ofHom (ContinuousMap.subtypeVal S)` is subtype projection.
  change Set.range (X.toSSetObjEquiv n σ) ⊆ Set.range (Subtype.val : S → X) ↔ _
  rw [Subtype.range_coe]

variable (U V : Set X)

/-- The square of inclusions of `U ∩ V`, `U` and `V` into `X` commutes. -/
lemma commSq_ofHom_inter :
    CommSq (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V))))
      (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))
      (ofHom (ContinuousMap.subtypeVal U)) (ofHom (ContinuousMap.subtypeVal V)) :=
  ⟨rfl⟩

end TopCat
