/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Slice
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity

/-!
# Finite uniform hypergraphs

An `r`-uniform hypergraph on a vertex type `V` is a finite set of unordered edges, each an
`r`-element finset of vertices. This finite representation carries the counting and density API.
Mathlib's set-based `Hypergraph` has neither uniformity nor finiteness, and `toHypergraph` relates
the two carriers.

The edge density of an `r`-uniform hypergraph on a finite vertex type is its number of edges over
`(card V).choose r`, the number of possible edges, as a rational number. When `card V < r` there
are no possible edges, the denominator is `0`, and the density is `0`. When `r = 0` the only
possible edge is the empty set, which is an edge of the complete hypergraph even on an empty
vertex type.

## Main definitions

* `TauCeti.UniformHypergraph r V`: a finite set of `r`-element edges.
* `TauCeti.UniformHypergraph.toHypergraph`: the corresponding Mathlib `Hypergraph`, with the whole
  vertex type as its vertex set.
* `TauCeti.UniformHypergraph.empty` and `TauCeti.UniformHypergraph.complete`.
* `TauCeti.UniformHypergraph.edgeDensity`: the rational edge density.

## Main results

* `TauCeti.UniformHypergraph.toHypergraph_vertexSet` and
  `TauCeti.UniformHypergraph.toHypergraph_edgeSet`: the two carriers agree.
* `TauCeti.UniformHypergraph.edgeDensity_nonneg` and `TauCeti.UniformHypergraph.edgeDensity_le_one`.
* `TauCeti.UniformHypergraph.edgeDensity_empty` and
  `TauCeti.UniformHypergraph.edgeDensity_complete`.

## References

* Adapted from `RegularityLemmata/Hypergraph/Uniform.lean` in `cameronfreer/regularity-lemmata` at
  commit `315ef979f55f31cc43cd791302519d9a34cc2dc0`. Divergences from that source: the edge density
  is rational rather than real, the edge-cardinality field is `edge_card`, the complete hypergraph
  needs no decidable equality on vertices, and the bridge to `Hypergraph` states its edge set as
  the coerced edges.
-/

public section

open Finset

namespace TauCeti

/-- An **`r`-uniform hypergraph** on `V`: a finite set of unordered edges, each an `r`-element
finset of vertices. -/
structure UniformHypergraph (r : ℕ) (V : Type*) where
  /-- The edges. -/
  edges : Finset (Finset V)
  /-- Every edge has exactly `r` vertices. -/
  edge_card : ∀ e ∈ edges, e.card = r

namespace UniformHypergraph

variable {r : ℕ} {V : Type*}

/-- A uniform hypergraph is determined by its edges. -/
@[ext]
theorem ext {H G : UniformHypergraph r V} (h : H.edges = G.edges) : H = G := by
  cases H
  cases G
  congr

/-- The edges form an `r`-sized family of finsets, so Mathlib's `Set.Sized` API applies to them. -/
theorem sized_edges (H : UniformHypergraph r V) : (H.edges : Set (Finset V)).Sized r :=
  fun e he => H.edge_card e he

/-! ### Mathlib's set-based carrier -/

/-- The corresponding Mathlib `Hypergraph`: the whole vertex type as vertex set, and the edges
coerced to sets. -/
def toHypergraph (H : UniformHypergraph r V) : Hypergraph V where
  vertexSet := Set.univ
  edgeSet := {e | ∃ f ∈ H.edges, (f : Set V) = e}
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _

/-- The bridge keeps the whole vertex type as its vertex set. -/
@[simp]
theorem toHypergraph_vertexSet (H : UniformHypergraph r V) :
    H.toHypergraph.vertexSet = Set.univ := (rfl)

/-- The edges of the bridge are exactly the coerced edges. -/
theorem toHypergraph_edgeSet (H : UniformHypergraph r V) :
    H.toHypergraph.edgeSet = {e | ∃ f ∈ H.edges, (f : Set V) = e} := (rfl)

/-- A finset is an edge of the bridge exactly when it is an edge. -/
@[simp]
theorem coe_mem_toHypergraph_edgeSet {H : UniformHypergraph r V} {e : Finset V} :
    (e : Set V) ∈ H.toHypergraph.edgeSet ↔ e ∈ H.edges := by
  rw [toHypergraph_edgeSet]
  exact ⟨fun ⟨f, hf, hfe⟩ => Finset.coe_injective hfe ▸ hf, fun he => ⟨e, he, rfl⟩⟩

/-! ### Empty and complete hypergraphs -/

/-- The **empty** `r`-uniform hypergraph, with no edges. -/
def empty (r : ℕ) (V : Type*) : UniformHypergraph r V :=
  ⟨∅, fun _ he => absurd he (Finset.notMem_empty _)⟩

/-- The empty hypergraph has no edges. -/
@[simp]
theorem edges_empty : (empty r V).edges = ∅ := (rfl)

/-- The **complete** `r`-uniform hypergraph on a finite vertex type: every `r`-element finset is an
edge. -/
def complete (r : ℕ) (V : Type*) [Fintype V] : UniformHypergraph r V :=
  ⟨univ.powersetCard r, fun _ he => Set.sized_powersetCard univ r he⟩

/-- The edges of the complete hypergraph are exactly the `r`-element finsets. -/
@[simp]
theorem mem_edges_complete [Fintype V] {e : Finset V} :
    e ∈ (complete r V).edges ↔ e.card = r := by
  simp [complete, Finset.mem_powersetCard]

/-- Every edge set lies in the edge set of the complete hypergraph. -/
theorem edges_subset_powersetCard [Fintype V] (H : UniformHypergraph r V) :
    H.edges ⊆ univ.powersetCard r :=
  H.sized_edges.subset_powersetCard_univ

/-- An `r`-uniform hypergraph has at most `(card V).choose r` edges. -/
theorem card_edges_le [Fintype V] (H : UniformHypergraph r V) :
    #H.edges ≤ (Fintype.card V).choose r :=
  H.sized_edges.card_le

/-- The complete hypergraph has `(card V).choose r` edges. -/
theorem card_edges_complete [Fintype V] :
    #(complete r V).edges = (Fintype.card V).choose r := by
  rw [complete, Finset.card_powersetCard, Finset.card_univ]

/-! ### Edge density -/

/-- The **edge density** of an `r`-uniform hypergraph on a finite vertex type: its number of edges
over the number `(card V).choose r` of possible edges. It is `0` when `card V < r`. -/
def edgeDensity [Fintype V] (H : UniformHypergraph r V) : ℚ :=
  (#H.edges : ℚ) / ((Fintype.card V).choose r : ℚ)

/-- The edge density is the number of edges over the number of possible edges. -/
theorem edgeDensity_def [Fintype V] (H : UniformHypergraph r V) :
    H.edgeDensity = (#H.edges : ℚ) / ((Fintype.card V).choose r : ℚ) := (rfl)

/-- The edge density is nonnegative. -/
theorem edgeDensity_nonneg [Fintype V] (H : UniformHypergraph r V) : 0 ≤ H.edgeDensity := by
  unfold edgeDensity
  positivity

/-- The edge density is at most `1`. -/
theorem edgeDensity_le_one [Fintype V] (H : UniformHypergraph r V) : H.edgeDensity ≤ 1 := by
  unfold edgeDensity
  rcases Nat.eq_zero_or_pos ((Fintype.card V).choose r) with h0 | hpos
  · simp [h0]
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast H.card_edges_le

/-- The empty hypergraph has density `0`. -/
@[simp]
theorem edgeDensity_empty [Fintype V] : (empty r V).edgeDensity = 0 := by
  simp [edgeDensity]

/-- The complete hypergraph has density `1` when there are possible edges, `r ≤ card V`. -/
theorem edgeDensity_complete [Fintype V] (hr : r ≤ Fintype.card V) :
    (complete r V).edgeDensity = 1 := by
  rw [edgeDensity, card_edges_complete]
  exact div_self (by exact_mod_cast (Nat.choose_pos hr).ne')

/-- With no possible edges, `card V < r`, every density is `0`. -/
theorem edgeDensity_eq_zero_of_card_lt [Fintype V] (H : UniformHypergraph r V)
    (hr : Fintype.card V < r) : H.edgeDensity = 0 := by
  simp [edgeDensity, Nat.choose_eq_zero_of_lt hr]

end UniformHypergraph

end TauCeti
