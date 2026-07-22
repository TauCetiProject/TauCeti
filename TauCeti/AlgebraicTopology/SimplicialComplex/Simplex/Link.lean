/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# Links and stars in abstract simplices

This file computes the closed star, link, and deletion constructions on the standard abstract
simplex and its boundary.  These formulas are the standard-model calculations used by the
recursive link condition for combinatorial manifolds in layer 11 of the geometric-topology
roadmap.  In particular, the link of a face in a simplex is the simplex on the complementary
vertices, while the link in the boundary is the boundary of that complementary simplex.

The constructions use `PreAbstractSimplicialComplex`, since taking a link changes the vertices
that occur.  The formulas follow Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 2.

## Main results

* `closedStar_simplex`: the closed star of a simplex face is the whole simplex.
* `link_simplex`: the link of a simplex face is the simplex on its complementary vertices.
* `deletion_simplex_self`: deleting the top face leaves the simplex boundary.
* `link_simplexBoundary`: the link of a boundary face is the boundary on its complementary
  vertices.
-/

public section

namespace TauCeti

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]
variable {V σ : Finset ι}

/-- The closed star of a face in a simplex is the entire simplex. -/
theorem closedStar_simplex (hσ : σ ⊆ V) : closedStar (simplex V) σ = simplex V := by
  apply SetLike.ext
  intro ρ
  rw [mem_closedStar, mem_simplex, mem_simplex]
  constructor
  · exact fun h => ⟨h.1, subset_union_left.trans h.2.2⟩
  · exact fun h => ⟨h.1, h.1.mono subset_union_left, union_subset h.2 hσ⟩

/-- The link of a face `σ` in the simplex on `V` is the simplex on the vertices of `V` not in
`σ`. -/
theorem link_simplex (hσ : σ ⊆ V) : link (simplex V) σ = simplex (V \ σ) := by
  apply SetLike.ext
  intro ρ
  rw [mem_link, mem_simplex, mem_simplex]
  constructor
  · rintro ⟨hρ, hdis, -, hρσ⟩
    refine ⟨hρ, subset_sdiff.mpr ⟨subset_union_left.trans hρσ, ?_⟩⟩
    exact hdis
  · rintro ⟨hρ, hρV⟩
    have hρV' : ρ ⊆ V := hρV.trans sdiff_subset
    have hdis : Disjoint ρ σ := Finset.disjoint_left.mpr fun x hxρ hxσ =>
      (Finset.mem_sdiff.mp (hρV hxρ)).2 hxσ
    exact ⟨hρ, hdis, (hρ.mono subset_union_left), union_subset hρV' hσ⟩

omit [DecidableEq ι] in
/-- Deleting the top face from a simplex leaves exactly its boundary. -/
theorem deletion_simplex_self : deletion (simplex V) V = simplexBoundary V := by
  apply SetLike.ext
  intro ρ
  rw [mem_deletion, mem_simplex, mem_simplexBoundary]
  constructor
  · rintro ⟨⟨hρ, hρV⟩, hVρ⟩
    exact ⟨hρ, Finset.ssubset_iff_subset_ne.mpr ⟨hρV, fun h => hVρ h.symm.subset⟩⟩
  · rintro ⟨hρ, hρV⟩
    exact ⟨⟨hρ, hρV.subset⟩, fun hVρ => hρV.not_subset hVρ⟩

/-- The closed star of a proper face in the boundary of a simplex consists of the nonempty
faces whose union with the selected face is still proper.  Equivalently, it is the part of the
simplex boundary supported away from no entire complementary face. -/
theorem mem_closedStar_simplexBoundary {ρ : Finset ι} :
    ρ ∈ closedStar (simplexBoundary V) σ ↔ ρ.Nonempty ∧ ρ ∪ σ ⊂ V := by
  rw [mem_closedStar, mem_simplexBoundary]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, h.1.mono subset_union_left, h.2⟩

/-- The link of a face in a simplex boundary is the simplex boundary on the complementary
vertices. -/
theorem link_simplexBoundary (hσ : σ ⊆ V) :
    link (simplexBoundary V) σ = simplexBoundary (V \ σ) := by
  apply SetLike.ext
  intro ρ
  rw [mem_link, mem_simplexBoundary, mem_simplexBoundary]
  constructor
  · rintro ⟨hρ, hdis, -, hρσ⟩
    refine ⟨hρ, Finset.ssubset_iff_subset_ne.mpr ⟨subset_sdiff.mpr
      ⟨subset_union_left.trans hρσ.subset, hdis⟩, ?_⟩⟩
    · intro hρeq
      apply hρσ.ne
      apply Subset.antisymm hρσ.subset
      intro x hxV
      by_cases hxσ : x ∈ σ
      · exact mem_union_right ρ hxσ
      · exact mem_union_left σ (hρeq ▸ mem_sdiff.mpr ⟨hxV, hxσ⟩)
  · rintro ⟨hρ, hρdiff⟩
    have hρV : ρ ⊆ V := hρdiff.subset.trans sdiff_subset
    have hdis : Disjoint ρ σ := Finset.disjoint_left.mpr fun x hxρ hxσ =>
      (mem_sdiff.mp (hρdiff.subset hxρ)).2 hxσ
    refine ⟨hρ, hdis, hρ.mono subset_union_left, ?_⟩
    refine Finset.ssubset_iff_subset_ne.mpr ⟨union_subset hρV hσ, ?_⟩
    intro hρσeq
    apply hρdiff.ne
    apply Subset.antisymm hρdiff.subset
    intro x hx
    have hxV : x ∈ V := (mem_sdiff.mp hx).1
    have hxρσ : x ∈ ρ ∪ σ := hρσeq ▸ hxV
    exact (mem_union.mp hxρσ).resolve_right (mem_sdiff.mp hx).2

/-- The link of the top face in its simplex is empty. -/
@[simp]
theorem link_simplex_self : link (simplex V) V = ⊥ := by
  rw [link_simplex Subset.rfl, sdiff_self]
  change simplex (∅ : Finset ι) = ⊥
  exact simplex_empty

/-- The link of the top face in its simplex boundary is empty.  The statement also covers the
empty spanning set. -/
@[simp]
theorem link_simplexBoundary_self : link (simplexBoundary V) V = ⊥ := by
  rw [link_simplexBoundary Subset.rfl, sdiff_self]
  change simplexBoundary (∅ : Finset ι) = ⊥
  exact simplexBoundary_empty

end PreAbstractSimplicialComplex

end TauCeti
