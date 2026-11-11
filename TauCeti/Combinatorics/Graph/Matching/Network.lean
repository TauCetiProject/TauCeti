/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Bipartition
public import TauCeti.Combinatorics.Network.AuxiliaryTerminals

/-!
# The flow network of a bipartite multigraph

For a bipartition `L, R` of a finite multigraph, orient every actual edge from `L` to `R`, add a
fresh source with one arrow to each vertex of `L`, and add one arrow from each vertex of `R` to a
fresh sink.  The terminal arrows at `v` have capacity `b v`; every original edge has the large
capacity `b(L) + 1`.

This file develops the cut side of the standard flow proof of capacitated Kőnig's theorem.  A
vertex cover `C` gives the source side

`{source} ∪ (L \ C) ∪ (R ∩ C)`,

whose cut capacity is exactly the weight of `C`.  Conversely, every terminal-separating cut of
capacity below `b(L) + 1` determines the vertex cover `(L \ S) ∪ (R ∩ S)`, because such a cut
cannot cross an original edge.  Edge identities are retained, so the construction applies to
parallel edges; a displayed bipartition already excludes loops.

The construction follows the classical network proof of Kőnig's theorem; see A. Schrijver,
*Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003, Section 21.1.

## Main definitions

* `Graph.BipartiteHom`: one arrow for every actual edge, directed from `L` to `R`.
* `Graph.bipartiteCapacity`: the capacities after adjoining the fresh source and sink.
* `Graph.bipartiteNetwork`: the corresponding zero-lower-bound integer network.
* `Graph.bipartiteCoverSourceSide`: the source side associated to a vertex cover.
* `Graph.bipartiteCutCover`: the candidate cover extracted from a source side; a low-capacity cut
  guarantees that it covers every edge.

## Main results

* `Graph.IsVertexCover.arrowSum_bipartiteCapacity_bipartiteCoverSourceSide`: a cover gives a cut
  of the same weight.
* `Graph.IsBipartition.arrowSum_bipartiteCapacity_eq_sum_bipartiteCutCover`: a low-capacity cut
  has the same weight as its associated cover.
* `Graph.IsBipartition.isVertexCover_bipartiteCutCover`: every cut below the large capacity gives
  a vertex cover.
-/

public section

open Finset Sum TauCeti
open scoped Graph

universe u v

namespace Graph

variable {alpha : Type u} {beta : Type v} {G : Graph alpha beta}
variable {L R : Finset V(G)}

/-- The capacity assigned to every original edge in the bipartite network.  It exceeds the
capacity of the cut obtained by deleting all source arrows. -/
def bipartiteLargeCapacity (L : Finset V(G)) (b : V(G) → ℕ) : ℤ :=
  ((∑ x ∈ L, b x) + 1 : ℕ)

/-- The large capacity is one more than the total capacity on `L`. -/
theorem bipartiteLargeCapacity_def (L : Finset V(G)) (b : V(G) → ℕ) :
    bipartiteLargeCapacity L b = ((∑ x ∈ L, b x) + 1 : ℕ) :=
  (rfl)

/-- The capacities of the bipartite network: `b v` on the terminal arrow at `v`, and
`b(L) + 1` on every original edge directed from `L` to `R`. -/
def bipartiteCapacity (L R : Finset V(G)) (b : V(G) → ℕ) :
    Assignment (AuxTerminalHom (G.BipartiteHom L) L R) ℤ :=
  auxTerminalCapacity (A := L) (B := R)
    (fun {_ _} _ ↦ bipartiteLargeCapacity L b) (fun x ↦ (b x : ℤ)) fun x ↦ (b x : ℤ)

/-- The bipartite capacity as an auxiliary-terminal capacity. -/
theorem bipartiteCapacity_def (L R : Finset V(G)) (b : V(G) → ℕ) :
    bipartiteCapacity L R b =
      auxTerminalCapacity (A := L) (B := R)
        (fun {_ _} _ ↦ bipartiteLargeCapacity L b) (fun x ↦ (b x : ℤ)) fun x ↦ (b x : ℤ) :=
  (rfl)

/-- Every capacity in the bipartite network is nonnegative. -/
theorem bipartiteCapacity_nonneg (L R : Finset V(G)) (b : V(G) → ℕ) :
    0 ≤ bipartiteCapacity L R b :=
  auxTerminalCapacity_nonneg (fun _ _ _ ↦ by
      rw [bipartiteLargeCapacity_def]
      exact Int.natCast_nonneg _)
    (fun _ _ ↦ Int.natCast_nonneg _) fun _ _ ↦ Int.natCast_nonneg _

@[simp]
theorem bipartiteCapacity_original (b : V(G) → ℕ) {x y : V(G)}
    (e : G.BipartiteHom L x y) :
    bipartiteCapacity L R b (AuxTerminalHom.original e) = bipartiteLargeCapacity L b :=
  auxTerminalCapacity_original _ _ _ e

@[simp]
theorem bipartiteCapacity_source (b : V(G) → ℕ) {x : V(G)} (hx : x ∈ L) :
    bipartiteCapacity L R b (AuxTerminalHom.source hx) = b x :=
  auxTerminalCapacity_source _ _ _ hx

@[simp]
theorem bipartiteCapacity_sink (b : V(G) → ℕ) {x : V(G)} (hx : x ∈ R) :
    bipartiteCapacity L R b (AuxTerminalHom.sink hx) = b x :=
  auxTerminalCapacity_sink _ _ _ hx

/-- The integer network used in the flow proof of capacitated Kőnig's theorem. -/
@[expose] noncomputable def bipartiteNetwork
    (G : Graph alpha beta) (L R : Finset V(G)) (b : V(G) → ℕ) :
  Network ℤ (V(G) ⊕ Bool) :=
  Network.ofCapacity (AuxTerminalHom (G.BipartiteHom L) L R) (bipartiteCapacity L R b)
    fun {_ _} e ↦ bipartiteCapacity_nonneg L R b _ _ e

@[simp]
theorem bipartiteNetwork_Hom (b : V(G) → ℕ) :
    (bipartiteNetwork G L R b).Hom = AuxTerminalHom (G.BipartiteHom L) L R :=
  rfl

@[simp]
theorem bipartiteNetwork_upper (b : V(G) → ℕ) {x y : V(G) ⊕ Bool}
    (e : (bipartiteNetwork G L R b).Hom x y) :
    (bipartiteNetwork G L R b).upper e = bipartiteCapacity L R b e :=
  rfl

@[simp]
theorem bipartiteNetwork_lower (b : V(G) → ℕ) {x y : V(G) ⊕ Bool}
    (e : (bipartiteNetwork G L R b).Hom x y) :
    (bipartiteNetwork G L R b).lower e = 0 :=
  rfl

/-- The source side associated to a vertex set `C`: it contains the fresh source, the vertices of
`L` outside `C`, and the vertices of `R` inside `C`. -/
noncomputable def bipartiteCoverSourceSide
    (L R C : Finset V(G)) : Finset (V(G) ⊕ Bool) := by
  classical
  exact ((L \ C) ∪ (R ∩ C)).disjSum {false}

@[simp]
theorem inl_mem_bipartiteCoverSourceSide (L R C : Finset V(G)) (x : V(G)) :
    inl x ∈ bipartiteCoverSourceSide L R C ↔
      (x ∈ L ∧ x ∉ C) ∨ (x ∈ R ∧ x ∈ C) := by
  simp [bipartiteCoverSourceSide]

@[simp]
theorem inr_mem_bipartiteCoverSourceSide (L R C : Finset V(G)) (t : Bool) :
    inr t ∈ bipartiteCoverSourceSide L R C ↔ t = false := by
  simp [bipartiteCoverSourceSide]

@[simp]
theorem bipartiteCoverSourceSide_toLeft [DecidableEq V(G)] (L R C : Finset V(G)) :
    (bipartiteCoverSourceSide L R C).toLeft = (L \ C) ∪ (R ∩ C) :=
  by
    ext x
    simp

/-- The vertex set associated to a source side `S`: vertices of `L` outside `S`, together with
vertices of `R` inside `S`. It is a vertex cover when the cut capacity is below `b(L) + 1`; see
`Graph.IsBipartition.isVertexCover_bipartiteCutCover`. -/
noncomputable def bipartiteCutCover
    (L R : Finset V(G)) (S : Finset (V(G) ⊕ Bool)) : Finset V(G) := by
  classical
  exact (L \ S.toLeft) ∪ (R ∩ S.toLeft)

@[simp]
theorem mem_bipartiteCutCover (L R : Finset V(G)) (S : Finset (V(G) ⊕ Bool)) (x : V(G)) :
    x ∈ bipartiteCutCover L R S ↔
      (x ∈ L ∧ inl x ∉ S) ∨ (x ∈ R ∧ inl x ∈ S) := by
  simp [bipartiteCutCover]

private theorem sum_bipartiteCoverSourceSide [DecidableEq V(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ)
    (C : Finset V(G)) :
    ∑ x ∈ L \ ((L \ C) ∪ (R ∩ C)), (b x : ℤ) +
        ∑ x ∈ R ∩ ((L \ C) ∪ (R ∩ C)), (b x : ℤ) =
      ∑ x ∈ C, (b x : ℤ) := by
  classical
  have hL : L \ ((L \ C) ∪ (R ∩ C)) = L ∩ C := by
    ext x
    have hdisjoint : x ∈ L → x ∈ R → False :=
      fun hxL hxR ↦ disjoint_left.1 hLR.disjoint hxL hxR
    grind
  have hR : R ∩ ((L \ C) ∪ (R ∩ C)) = R ∩ C := by
    ext x
    have hdisjoint : x ∈ L → x ∈ R → False :=
      fun hxL hxR ↦ disjoint_left.1 hLR.disjoint hxL hxR
    grind
  rw [hL, hR, ← sum_union]
  · congr 1
    ext x
    have hmem := hLR.mem_or_mem x
    grind
  · exact hLR.disjoint.mono inter_subset_left inter_subset_left

private theorem sum_bipartiteCutCover [DecidableEq V(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ) (S : Finset (V(G) ⊕ Bool)) :
    ∑ x ∈ L \ S.toLeft, (b x : ℤ) + ∑ x ∈ R ∩ S.toLeft, (b x : ℤ) =
      ∑ x ∈ bipartiteCutCover L R S, (b x : ℤ) := by
  classical
  have hcover : bipartiteCutCover L R S = (L \ S.toLeft) ∪ (R ∩ S.toLeft) := by
    ext x
    simp
  rw [hcover, sum_union]
  exact hLR.disjoint.mono sdiff_subset inter_subset_left

private theorem bipartiteHom_closed_of_arrowSum_lt [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] (b : V(G) → ℕ) {S : Finset (V(G) ⊕ Bool)}
    (hsmall : arrowSum (bipartiteCapacity L R b) S Sᶜ < bipartiteLargeCapacity L b) :
    ∀ {x y : V(G)}, G.BipartiteHom L x y → x ∈ S.toLeft → y ∈ S.toLeft := by
  intro x y e hx
  by_contra hy
  have hx' : inl x ∈ S := by simpa using hx
  have hy' : inl y ∈ Sᶜ := by
    simp only [mem_compl]
    exact fun hyS ↦ hy (Finset.mem_toLeft.2 hyS)
  have hle := apply_le_arrowSum (bipartiteCapacity_nonneg L R b) hx' hy'
    (AuxTerminalHom.original e)
  rw [bipartiteCapacity_original] at hle
  exact (not_lt_of_ge hle) hsmall

/-- A vertex cover gives a terminal-separating cut whose capacity is exactly the weight of the
cover. -/
theorem IsVertexCover.arrowSum_bipartiteCapacity_bipartiteCoverSourceSide
    [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] {C : Finset V(G)}
    (hC : G.IsVertexCover (C : Set V(G))) (hLR : G.IsBipartition L R) (b : V(G) → ℕ) :
    arrowSum (bipartiteCapacity L R b) (bipartiteCoverSourceSide L R C)
        (bipartiteCoverSourceSide L R C)ᶜ = ∑ x ∈ C, (b x : ℤ) := by
  classical
  rw [bipartiteCapacity_def]
  rw [arrowSum_auxTerminalCapacity (S := bipartiteCoverSourceSide L R C)
    (fun {_ _} _ ↦ bipartiteLargeCapacity L b) (fun x ↦ (b x : ℤ)) (fun x ↦ (b x : ℤ))
    (by simp) (by simp)]
  rw [arrowSum_compl_eq_zero_of_forall_mem]
  · simpa only [bipartiteCoverSourceSide_toLeft, add_zero] using
      sum_bipartiteCoverSourceSide hLR b C
  · intro x y e hx
    have hxC : x ∉ C := by
      simpa [e.source_mem, disjoint_left.1 hLR.disjoint] using hx
    have hyR := e.target_mem hLR
    have hyC : y ∈ C := by
      rw [isVertexCover_def] at hC
      rcases hC e.isLink with h | h
      · exact (hxC h).elim
      · exact h
    simp [hyR, hyC]

/-- A terminal-separating cut below the large capacity has the same capacity as the weight of its
associated vertex cover. -/
theorem IsBipartition.arrowSum_bipartiteCapacity_eq_sum_bipartiteCutCover
    [Fintype V(G)] [DecidableEq V(G)] [Fintype E(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ) {S : Finset (V(G) ⊕ Bool)}
    (hsource : inr false ∈ S) (hsink : inr true ∉ S)
    (hsmall : arrowSum (bipartiteCapacity L R b) S Sᶜ < bipartiteLargeCapacity L b) :
    arrowSum (bipartiteCapacity L R b) S Sᶜ =
      ∑ x ∈ bipartiteCutCover L R S, (b x : ℤ) := by
  have hclosed : ∀ {x y : V(G)}, G.BipartiteHom L x y →
      x ∈ S.toLeft → y ∈ S.toLeft :=
    bipartiteHom_closed_of_arrowSum_lt b hsmall
  rw [bipartiteCapacity_def]
  rw [arrowSum_auxTerminalCapacity (S := S) (fun {_ _} _ ↦ bipartiteLargeCapacity L b)
    (fun x ↦ (b x : ℤ)) (fun x ↦ (b x : ℤ)) hsource hsink]
  rw [arrowSum_compl_eq_zero_of_forall_mem]
  · simpa only [add_zero] using sum_bipartiteCutCover hLR b S
  · intro x y e hx
    exact hclosed e hx

/-- A cut below the large capacity cannot cross an original edge, so its associated vertex set
is a vertex cover. -/
theorem IsBipartition.isVertexCover_bipartiteCutCover [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ) {S : Finset (V(G) ⊕ Bool)}
    (hsmall : arrowSum (bipartiteCapacity L R b) S Sᶜ < bipartiteLargeCapacity L b) :
    G.IsVertexCover (bipartiteCutCover L R S : Set V(G)) := by
  classical
  have hclosed : ∀ {x y : V(G)}, G.BipartiteHom L x y →
      x ∈ S.toLeft → y ∈ S.toLeft :=
    bipartiteHom_closed_of_arrowSum_lt b hsmall
  rw [isVertexCover_def]
  intro e x y he
  rcases hLR.isLink he with hxy | hxy
  · by_cases hxS : x ∈ S.toLeft
    · have hyS : y ∈ S.toLeft :=
        hclosed (⟨⟨e, he.edge_mem⟩, he, hxy.1⟩ : G.BipartiteHom L x y) hxS
      have hyS' : inl y ∈ S := by simpa using hyS
      right
      simp [hxy.2, hyS']
    · left
      have hxS' : inl x ∉ S := by simpa using hxS
      simp [hxy.1, hxS']
  · by_cases hyS : y ∈ S.toLeft
    · have hxS : x ∈ S.toLeft :=
        hclosed (⟨⟨e, he.edge_mem⟩, he.symm, hxy.2⟩ : G.BipartiteHom L y x) hyS
      have hxS' : inl x ∈ S := by simpa using hxS
      left
      simp [hxy.1, hxS']
    · right
      have hyS' : inl y ∉ S := by simpa using hyS
      simp [hxy.2, hyS']

end Graph
