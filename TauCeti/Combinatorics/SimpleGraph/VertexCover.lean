/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
# Neighbourhood constructions and finite-cover kernelization for vertex covers

For any vertex cover `C` of a simple graph `G : SimpleGraph V` and any subset `S : Set V`,
replacing `S` in `C` by its open neighbourhood `⋃ x ∈ S, G.neighborSet x` yields another vertex
cover `(C \ S) ∪ ⋃ x ∈ S, G.neighborSet x`
(`SimpleGraph.IsVertexCover.sdiff_union_biUnion_neighborSet`).

When `C₀` is a finite vertex cover of `G` on a possibly infinite vertex type `V`, retaining at most
`C₀.ncard + 1` neighbours of each vertex of `C₀` produces an induced subgraph `S : G.Subgraph` on a
finite vertex set `S.verts ⊇ C₀` such that any vertex cover of `S.coe` of extended cardinality at
most `C₀.encard` pushes forward under `Subtype.val` to a vertex cover of `G`
(`SimpleGraph.IsVertexCover.exists_finite_verts_isVertexCover_image`): any vertex of `C₀` with more
than `C₀.ncard` retained neighbours must lie in the cover by cardinality, while every neighbour of
any remaining vertex of `C₀` already belongs to `S.verts`.

## Main results

* `SimpleGraph.IsVertexCover.sdiff_union_biUnion_neighborSet`: removing `S` from a vertex cover `C`
  and adjoining `⋃ x ∈ S, G.neighborSet x` produces a vertex cover.
* `SimpleGraph.IsVertexCover.exists_finite_verts_isVertexCover_image`: finite-cover neighbourhood
  kernelization to an induced subgraph on finitely many vertices.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Removing any subset `S` from a vertex cover `C` and adjoining the neighbourhood
`⋃ x ∈ S, G.neighborSet x` yields a vertex cover of `G`. -/
theorem IsVertexCover.sdiff_union_biUnion_neighborSet {C : Set V} (hC : G.IsVertexCover C)
    (S : Set V) :
    G.IsVertexCover ((C \ S) ∪ ⋃ x ∈ S, G.neighborSet x) := by
  intro u v huv
  rcases hC huv with huC | hvC
  · by_cases huS : u ∈ S
    · exact Or.inr (Or.inr <| Set.mem_iUnion₂.2 ⟨u, huS, huv⟩)
    · exact Or.inl (Or.inl ⟨huC, huS⟩)
  · by_cases hvS : v ∈ S
    · exact Or.inl (Or.inr <| Set.mem_iUnion₂.2 ⟨v, hvS, huv.symm⟩)
    · exact Or.inr (Or.inl ⟨hvC, hvS⟩)

/-- Given a finite vertex cover `C₀` of `G`, there exists an induced subgraph `S : G.Subgraph` on a
finite vertex set `S.verts ⊇ C₀` such that every vertex cover of `S.coe` of extended cardinality at
most `C₀.encard` pushes forward to a vertex cover of `G`. -/
theorem IsVertexCover.exists_finite_verts_isVertexCover_image {C₀ : Set V}
    (hC₀ : G.IsVertexCover C₀) (hC₀fin : C₀.Finite) :
    ∃ S : G.Subgraph, S.IsInduced ∧ C₀ ⊆ S.verts ∧ S.verts.Finite ∧
      ∀ ⦃C₁ : Set S.verts⦄, S.coe.IsVertexCover C₁ → C₁.encard ≤ C₀.encard →
        G.IsVertexCover (Subtype.val '' C₁) := by
  -- Retain at most `C₀.ncard + 1` neighbours of each vertex of `C₀`; any cover of the resulting
  -- finite induced subgraph of size at most `C₀.ncard` must include every vertex of `C₀` that has
  -- neighbours outside the induced subgraph.
  let k : ℕ := C₀.ncard
  have hk : C₀.encard = k := hC₀fin.cast_ncard_eq.symm
  have hexA (x : V) : ∃ A : Set V, A ⊆ G.neighborSet x ∧ A.Finite ∧
      (G.neighborSet x ⊆ A ∨ A.encard = (k + 1 : ℕ)) := by
    by_cases hle : ((k + 1 : ℕ) : ℕ∞) ≤ (G.neighborSet x).encard
    · obtain ⟨A, hAsub, hAcard⟩ := Set.exists_subset_encard_eq hle
      exact ⟨A, hAsub, Set.encard_ne_top_iff.1 (by simp [hAcard]), Or.inr hAcard⟩
    · have hfin : (G.neighborSet x).Finite :=
        Set.encard_lt_top_iff.1 ((lt_of_not_ge hle).trans_le le_top)
      exact ⟨G.neighborSet x, Set.Subset.rfl, hfin, Or.inl Set.Subset.rfl⟩
  choose A hAsub hAfin hAcase using hexA
  let S : G.Subgraph := (⊤ : G.Subgraph).induce (C₀ ∪ ⋃ x ∈ C₀, A x)
  have hSverts : S.verts = C₀ ∪ ⋃ x ∈ C₀, A x := Subgraph.induce_verts _ _
  refine ⟨S, S.isInduced_iff_exists_eq_induce_top.2 ⟨_, rfl⟩,
    hSverts.symm ▸ Set.subset_union_left,
    hSverts.symm ▸ hC₀fin.union (hC₀fin.biUnion fun x _ ↦ hAfin x),
    fun C₁ hC₁ hC₁le ↦ ?_⟩
  have hcov_left {u v : V} (huv : G.Adj u v) (hu₀ : u ∈ C₀) :
      u ∈ Subtype.val '' C₁ ∨ v ∈ Subtype.val '' C₁ := by
    have hu : u ∈ C₀ ∪ ⋃ x ∈ C₀, A x := Or.inl hu₀
    have huU : u ∈ S.verts := hSverts.symm ▸ hu
    rcases hAcase u with hall | hlarge
    · have hv : v ∈ C₀ ∪ ⋃ x ∈ C₀, A x := Or.inr (Set.mem_iUnion₂.2 ⟨u, hu₀, hall huv⟩)
      have hvU : v ∈ S.verts := hSverts.symm ▸ hv
      have hadjS : S.coe.Adj ⟨u, huU⟩ ⟨v, hvU⟩ := by
        rw [Subgraph.coe_adj, Subgraph.induce_adj, Subgraph.top_adj]
        exact ⟨hu, hv, huv⟩
      exact (hC₁ hadjS).imp (fun h ↦ ⟨⟨u, huU⟩, h, rfl⟩) (fun h ↦ ⟨⟨v, hvU⟩, h, rfl⟩)
    · refine Or.inl ?_
      by_contra huC
      have hsub : A u ⊆ Subtype.val '' C₁ := fun w hw ↦ by
        have hw' : w ∈ C₀ ∪ ⋃ x ∈ C₀, A x := Or.inr (Set.mem_iUnion₂.2 ⟨u, hu₀, hw⟩)
        have hwU : w ∈ S.verts := hSverts.symm ▸ hw'
        have hadjS : S.coe.Adj ⟨u, huU⟩ ⟨w, hwU⟩ := by
          rw [Subgraph.coe_adj, Subgraph.induce_adj, Subgraph.top_adj]
          exact ⟨hu, hw', hAsub u hw⟩
        rcases hC₁ hadjS with hu1 | hw1
        · exact absurd ⟨⟨u, huU⟩, hu1, rfl⟩ huC
        · exact ⟨⟨w, hwU⟩, hw1, rfl⟩
      have hbad : ((k + 1 : ℕ) : ℕ∞) ≤ k := by
        calc
          ((k + 1 : ℕ) : ℕ∞) = (A u).encard := hlarge.symm
          _ ≤ (Subtype.val '' C₁).encard := Set.encard_mono hsub
          _ = C₁.encard := Subtype.val_injective.encard_image C₁
          _ ≤ k := hC₁le.trans_eq hk
      exact absurd (Nat.cast_le.1 hbad) (by omega)
  intro u v huv
  rcases hC₀ huv with hu₀ | hv₀
  · exact hcov_left huv hu₀
  · exact (hcov_left huv.symm hv₀).symm

end SimpleGraph
