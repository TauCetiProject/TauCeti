/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar
public import TauCeti.Data.Finset.Partition

/-!
# Closed stars as joins

The closed star of a face `σ` is the join of the simplex on `σ` with its link. The part of
that closed star which does not contain `σ` is the join of the boundary of `σ` with its link.
In particular, this describes the link of the new vertex of a stellar subdivision.

The join uses disjoint tagged vertex types. The identifications below tag a vertex on the left
when it belongs to `σ`, and on the right otherwise. This vertex map is injective: untagging is
a left inverse. Thus the equalities are actual relabelings, without identifying distinct used
vertices. No nonvoidness assumption is imposed on the link; the formulas include maximal faces
and singleton faces, whose links or simplex boundaries may be void.

The combinatorial description follows Rourke--Sanderson, *Introduction to Piecewise-Linear
Topology*, Chapters 2--3, and Lickorish, *Simplicial moves on complexes and manifolds*,
Geom. Topol. Monogr. 2 (1999), 299--320.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι}

/-- Tagging the vertices of a closed star according to membership in `σ` identifies it with
the join of the simplex on `σ` and the link of `σ`. -/
@[simp]
theorem map_closedStar_eq_join (hσ : σ ∈ K) :
    (closedStar K σ).map (partitionEmbedding (· ∈ σ)) =
      join (simplex σ) (link K σ) := by
  refine SetLike.ext fun τ => ?_
  rw [mem_map_iff]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨hne, hlink⟩ := (mem_closedStar_iff_sdiff hσ).mp hρ
    rw [image_partitionEmbedding]
    simp only [filter_mem_eq_inter, filter_notMem_eq_sdiff, disjSum_mem_join_iff]
    refine ⟨?_, ?_, hlink⟩
    · obtain ⟨x, hx⟩ := hne
      by_cases hxs : x ∈ σ
      · exact Or.inl ⟨x, mem_inter.mpr ⟨hx, hxs⟩⟩
      · exact Or.inr ⟨x, mem_sdiff.mpr ⟨hx, hxs⟩⟩
    · by_cases h : ρ ∩ σ = ∅
      · exact Or.inl h
      · exact Or.inr (mem_simplex.mpr ⟨nonempty_iff_ne_empty.mpr h, inter_subset_right⟩)
  · intro hτ
    obtain ⟨hne, hs, ht⟩ := mem_join_iff.mp hτ
    have hsσ : τ.toLeft ⊆ σ := by
      rcases hs with h | h
      · simp [h]
      · exact (mem_simplex.mp h).2
    have hdis : Disjoint τ.toRight σ := by
      rcases ht with h | h
      · simp [h]
      · exact (mem_link_nonempty.mp h).2.1
    have hface : τ.toRight ∪ σ ∈ K := by
      rcases ht with h | h
      · simpa only [h, empty_union] using hσ
      · exact (mem_link_nonempty.mp h).2.2
    refine ⟨τ.toLeft ∪ τ.toRight, ?_, ?_⟩
    · refine mem_closedStar_nonempty.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx⟩ := hne
        cases x with
        | inl x => exact ⟨x, mem_union_left _ (mem_toLeft.mpr hx)⟩
        | inr x => exact ⟨x, mem_union_right _ (mem_toRight.mpr hx)⟩
      · have heq : (τ.toLeft ∪ τ.toRight) ∪ σ = τ.toRight ∪ σ := by
          grind
        rwa [heq]
    · rw [image_partitionEmbedding]
      have hl : (τ.toLeft ∪ τ.toRight).filter (· ∈ σ) = τ.toLeft := by
        ext x
        simp only [mem_filter, mem_union]
        grind [disjoint_left]
      have hr : (τ.toLeft ∪ τ.toRight).filter (fun x => x ∉ σ) = τ.toRight := by
        ext x
        simp only [mem_filter, mem_union]
        grind [disjoint_left]
      rw [hl, hr, toLeft_disjSum_toRight]

/-- The part of a closed star avoiding the whole starred face is the join of the simplex
boundary with the link, after tagging vertices according to membership in that face. -/
@[simp]
theorem map_closedStar_inf_deletion_eq_join (hσ : σ ∈ K) :
    (closedStar K σ ⊓ deletion K σ).map
        (partitionEmbedding (· ∈ σ)) =
      join (simplexBoundary σ) (link K σ) := by
  refine SetLike.ext fun τ => ?_
  rw [mem_map_iff]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨-, hproper, hlink⟩ := (mem_closedStar_inf_deletion_iff_sdiff hσ).mp hρ
    have hmem : ρ.image (partitionEmbedding (· ∈ σ)) ∈
        join (simplex σ) (link K σ) := by
      rw [← map_closedStar_eq_join hσ]
      exact mem_map_iff.mpr ⟨ρ, (mem_inf.mp hρ).1, rfl⟩
    rw [image_partitionEmbedding] at hmem ⊢
    simp only [filter_mem_eq_inter, filter_notMem_eq_sdiff, disjSum_mem_join_iff] at hmem ⊢
    refine ⟨hmem.1, ?_, hlink⟩
    rcases hmem.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr (mem_simplexBoundary.mpr ⟨(mem_simplex.mp h).1, hproper⟩)
  · intro hτ
    have hτstar : τ ∈ join (simplex σ) (link K σ) :=
      join_mono simplexBoundary_le_simplex le_rfl hτ
    rw [← map_closedStar_eq_join hσ, mem_map_iff] at hτstar
    obtain ⟨ρ, hρ, rfl⟩ := hτstar
    refine ⟨ρ, mem_inf.mpr ⟨hρ, mem_deletion.mpr
      ⟨closedStar_le hρ, ?_⟩⟩, rfl⟩
    intro hsub
    rw [image_partitionEmbedding] at hτ
    simp only [filter_mem_eq_inter, filter_notMem_eq_sdiff, disjSum_mem_join_iff] at hτ
    have heq : ρ ∩ σ = σ := inter_eq_right.mpr hsub
    rcases hτ.2.1 with h | h
    · exact (K.isRelLowerSet_faces hσ).1.ne_empty (heq.symm.trans h)
    · exact (mem_simplexBoundary.mp h).2.ne heq

end PreAbstractSimplicialComplex
