/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Link

/-!
# Iterated links and standard combinatorial models

This file supplies the recursive link identity and computes the standard-model cases needed by
the link condition for combinatorial manifolds.  The identity reduces a link of a higher face to
successive links, while the model lemmas identify the result as a combinatorial ball or sphere.
These are the combinatorial prerequisites for the realization theorem.  The calculations follow
Rourke--Sanderson, *Introduction to Piecewise-Linear
Topology*, Chapter 2.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]
variable {K : PreAbstractSimplicialComplex ι} {σ τ V : Finset ι} {n : ℕ}

/-- Taking the link of `τ` inside the link of a disjoint face `σ` is the link of their union. -/
theorem link_link (hστ : Disjoint σ τ) : link (link K σ) τ = link K (σ ∪ τ) := by
  ext ρ
  change ρ ∈ link (link K σ) τ ↔ ρ ∈ link K (σ ∪ τ)
  constructor
  · intro hρ
    obtain ⟨hρσ, hρτ, hρτσ⟩ := mem_link.mp hρ
    obtain ⟨hρK, hρσdis, _⟩ := mem_link.mp hρσ
    obtain ⟨_, _, hρτσK⟩ := mem_link.mp hρτσ
    refine mem_link.mpr ⟨hρK, disjoint_union_right.mpr ⟨hρσdis, hρτ⟩, ?_⟩
    simpa [union_assoc, union_left_comm, union_comm] using hρτσK
  · intro hρ
    obtain ⟨hρK, hρστdis, hρστK⟩ := mem_link.mp hρ
    have hρσdis : Disjoint ρ σ := (disjoint_union_right.mp hρστdis).1
    have hρτdis : Disjoint ρ τ := (disjoint_union_right.mp hρστdis).2
    have hρne : ρ.Nonempty := (K.isRelLowerSet_faces hρK).1
    have hρσK : ρ ∪ σ ∈ K :=
      (K.isRelLowerSet_faces hρστK).2
        (union_subset_union Subset.rfl subset_union_left) (hρne.mono subset_union_left)
    have hρτσK : ρ ∪ τ ∈ K :=
      (K.isRelLowerSet_faces hρστK).2
        (union_subset_union Subset.rfl subset_union_right) (hρne.mono subset_union_left)
    have hρσ : ρ ∈ link K σ := mem_link.mpr ⟨hρK, hρσdis, hρσK⟩
    have hρτσ : ρ ∪ τ ∈ link K σ := by
      refine mem_link.mpr ⟨hρτσK, disjoint_union_left.mpr ⟨hρσdis, hστ.symm⟩, ?_⟩
      simpa [union_assoc, union_left_comm, union_comm] using hρστK
    exact mem_link.mpr ⟨hρσ, hρτdis, hρτσ⟩

/-- The link of a face in a standard simplex is a combinatorial ball of the complementary
dimension. -/
theorem isCombinatorialBall_link_simplex (hV : V.card = n + 1) (hσ : σ ⊆ V)
    (hσcard : σ.card ≤ n) :
    IsCombinatorialBall (link (simplex V) σ) (n - σ.card) := by
  rw [link_simplex hσ]
  apply isCombinatorialBall_simplex
  rw [Finset.card_sdiff_of_subset hσ, hV]
  omega

/-- The link of a face in a standard simplex boundary is a combinatorial sphere of the
complementary dimension. -/
theorem isCombinatorialSphere_link_simplexBoundary (hV : V.card = n + 2) (hσ : σ ⊆ V)
    (hσcard : σ.card ≤ n) :
    IsCombinatorialSphere (link (simplexBoundary V) σ) (n - σ.card) := by
  rw [link_simplexBoundary hσ]
  apply isCombinatorialSphere_simplexBoundary
  rw [Finset.card_sdiff_of_subset hσ, hV]
  omega

end PreAbstractSimplicialComplex
