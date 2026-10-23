/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Pure

/-!
# Purity of combinatorial manifolds

Combinatorial `n`-balls and `n`-spheres are pure: every face extends to an `n`-dimensional
face. The vertex-link condition then implies the same for combinatorial `n`-manifolds,
without assuming that the whole complex is finite.

In particular, the link of a face with `k ≤ n` vertices in a combinatorial `n`-manifold
has dimension `n - k`; the link of a face with `n + 1` vertices is void. These statements
give the dimension indices needed when classifying higher-face links and the new-vertex
links of stellar subdivisions.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 2--3.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {n : ℕ} {σ : Finset ι}

/-- A combinatorial `n`-ball is pure of dimension `n`. -/
theorem IsCombinatorialBall.isPure (h : IsCombinatorialBall K n) : IsPure K n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  exact he.isPure_iff.mpr (isPure_simplex hV)

/-- A combinatorial `n`-sphere is pure of dimension `n`. -/
theorem IsCombinatorialSphere.isPure (h : IsCombinatorialSphere K n) : IsPure K n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  exact he.isPure_iff.mpr (isPure_simplexBoundary hV)

/-- The vertex-link condition makes a combinatorial manifold pure, including in dimension
zero and for infinite complexes. -/
theorem IsCombinatorialManifold.isPure (h : IsCombinatorialManifold K n) : IsPure K n := by
  cases n with
  | zero =>
    rw [isPure_iff]
    intro σ hσ
    obtain ⟨v, rfl⟩ := dimension_le_zero_iff.mp h.dimension_le σ hσ
    exact ⟨{v}, hσ, Subset.rfl, card_singleton v⟩
  | succ n =>
    rw [isPure_iff]
    intro σ hσ
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
    have hvK := singleton_mem_of_mem hσ hv
    have hlink : IsPure (link K {v}) n ∧ link K {v} ≠ ⊥ := by
      rcases isCombinatorialManifold_succ_iff.mp h hvK with hs | hb
      · exact ⟨hs.isPure, hs.ne_bot⟩
      · exact ⟨hb.isPure, hb.ne_bot⟩
    obtain ⟨hpure, hnonvoid⟩ := hlink
    have hex : ∃ τ ∈ link K {v}, σ.erase v ⊆ τ ∧ τ.card = n + 1 := by
      by_cases hempty : σ.erase v = ∅
      · obtain ⟨ρ, hρ, -⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hnonvoid)
        obtain ⟨τ, hτ, -, hcard⟩ := hpure.exists_coface hρ
        exact ⟨τ, hτ, by simp [hempty], hcard⟩
      · apply hpure.exists_coface
        exact mem_link_nonempty.mpr ⟨nonempty_iff_ne_empty.mpr hempty,
          disjoint_singleton_right.mpr (notMem_erase v σ), by
            rwa [union_singleton, insert_erase hv]⟩
    obtain ⟨τ, hτ, hsub, hcard⟩ := hex
    obtain ⟨-, hdis, hface⟩ := mem_link_nonempty.mp hτ
    refine ⟨insert v τ, by rwa [union_singleton] at hface, ?_, ?_⟩
    · rw [← insert_erase hv]
      exact insert_subset_insert v hsub
    · rw [card_insert_of_notMem (disjoint_singleton_right.mp hdis), hcard]

/-- A face below top dimension in a combinatorial `n`-manifold has link of dimension
`n - σ.card`. No finiteness of the manifold or ambient vertex type is required. -/
theorem IsCombinatorialManifold.dimension_link (h : IsCombinatorialManifold K n)
    (hσ : σ ∈ K) (hcard : σ.card ≤ n) :
    dimension (link K σ) = ((n - σ.card : ℕ) : WithBot ℕ∞) :=
  h.isPure.dimension_link hσ hcard

/-- The top-dimensional faces of a combinatorial manifold are exactly its faces with
void link. -/
theorem IsCombinatorialManifold.link_eq_bot_iff (h : IsCombinatorialManifold K n)
    (hσ : σ ∈ K) : link K σ = ⊥ ↔ σ.card = n + 1 :=
  h.isPure.link_eq_bot_iff hσ

end PreAbstractSimplicialComplex
