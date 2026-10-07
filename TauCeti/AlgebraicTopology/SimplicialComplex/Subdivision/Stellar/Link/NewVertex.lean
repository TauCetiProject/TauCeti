/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Basic

/-!
# Links of faces containing the stellar vertex

The link of a face containing the new vertex in a stellar subdivision is the local piece needed
when transporting the combinatorial-manifold link condition through a stellar move.  The defining
face description in `Stellar.Basic` gives this directly, but repeatedly unfolding the two cases is
error-prone.  This file records the resulting membership criterion and its deletion containment.

The criterion is the containing-new-vertex companion to
`link_stellarSubdivision_of_notMem`: it is the next local ingredient for the higher-face
sphere-or-ball classification in layer 11 of the geometric-topology roadmap.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ ρ τ : Finset ι} {v : ι}

/-- A face in the link of `insert v ρ` is characterized by the face condition after erasing the
stellar vertex.  In particular, it is disjoint from both `ρ` and the new vertex. -/
theorem mem_link_stellarSubdivision_insert_iff (hvρ : v ∉ ρ) :
    τ ∈ link (stellarSubdivision K σ v) (insert v ρ) ↔
      τ.Nonempty ∧ v ∉ τ ∧ Disjoint τ ρ ∧ ¬ σ ⊆ τ ∪ ρ ∧ (τ ∪ ρ) ∪ σ ∈ K := by
  rw [mem_link_nonempty]
  constructor
  · rintro ⟨hτ, hdis, hface⟩
    have hdis' : v ∉ τ ∧ Disjoint τ ρ := Finset.disjoint_insert_right.mp hdis
    rcases hdis' with ⟨hvτ, hτρ⟩
    have hvτρ : v ∉ τ ∪ ρ := by simp [hvτ, hvρ]
    have hface' : insert v (τ ∪ ρ) ∈ stellarSubdivision K σ v := by
      simpa [Finset.union_insert, Finset.insert_union, Finset.union_assoc,
        Finset.union_left_comm, Finset.union_comm] using hface
    obtain ⟨hσ, hK⟩ := (insert_mem_stellarSubdivision_iff hvτρ).mp hface'
    exact ⟨hτ, hvτ, hτρ, hσ, hK⟩
  · rintro ⟨hτ, hvτ, hτρ, hσ, hK⟩
    have hvτρ : v ∉ τ ∪ ρ := by simp [hvτ, hvρ]
    have hface : insert v (τ ∪ ρ) ∈ stellarSubdivision K σ v :=
      (insert_mem_stellarSubdivision_iff hvτρ).mpr ⟨hσ, hK⟩
    refine ⟨hτ, Finset.disjoint_insert_right.mpr ⟨hvτ, hτρ⟩, ?_⟩
    simpa [Finset.union_insert, Finset.insert_union, Finset.union_assoc,
      Finset.union_left_comm, Finset.union_comm] using hface

/-- Every face in the link of a stellar face containing the new vertex belongs to the deletion of
that starred face in the source complex. -/
theorem link_stellarSubdivision_insert_le_deletion (hvρ : v ∉ ρ) :
    link (stellarSubdivision K σ v) (insert v ρ) ≤ deletion K σ := by
  intro τ hτ
  obtain ⟨hτ, -, -, hσ, hK⟩ := mem_link_stellarSubdivision_insert_iff hvρ |>.mp hτ
  apply mem_deletion.mpr
  refine ⟨(K.isRelLowerSet_faces hK).2
      (Finset.subset_union_left.trans Finset.subset_union_left) hτ, ?_⟩
  intro hστ
  exact hσ (hστ.trans Finset.subset_union_left)

end PreAbstractSimplicialComplex
