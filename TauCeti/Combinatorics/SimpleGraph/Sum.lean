/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Disjoint sums of graphs

Four gaps in Mathlib's `SimpleGraph.sum` API.

`SimpleGraph.sum` has no `DecidableRel` instance in Mathlib. Consequently, even when adjacency in
both summands is decidable, `(G ⊕g H).edgeFinset` is not expressible without supplying an
instance. `TauCeti.instDecidableRelSumAdj` supplies it by the four-way case split in the definition
of `SimpleGraph.sum`.

Nor does it describe the graphs containing a disjoint sum: `SimpleGraph.sum_le_iff` says a graph on
`V ⊕ W` contains `G ⊕g H` exactly when its two sides contain `G` and `H`, which is how containing a
disjoint union of patterns splits into two independent containment events.

`SimpleGraph.sum` has no `bot` law in Mathlib either: `SimpleGraph.sum_bot_bot` says a disjoint
sum of edgeless graphs is edgeless, the form in which a graph parameter that is multiplicative over
disjoint sums is evaluated on an edgeless graph.

Finally, Mathlib's `SimpleGraph.edgeSetSumEquiv`, implemented by `Sym2.fromRelNdrec`, comes with
no evaluation lemmas. `SimpleGraph.coe_edgeSetSumEquiv_symm_inl` and
`SimpleGraph.coe_edgeSetSumEquiv_symm_inr` say that its inverse sends an edge of either summand to
its image under the corresponding inclusion, which is how a product over the edges of `G ⊕g H`
splits into products over the edges of `G` and of `H`.

## Main results

* `TauCeti.instDecidableRelSumAdj` — adjacency in a disjoint sum is decidable;
* `SimpleGraph.sum_le_iff` — a graph contains a disjoint sum exactly when its two sides contain the
  summands;
* `SimpleGraph.sum_bot_bot` — a disjoint sum of edgeless graphs is edgeless;
* `SimpleGraph.coe_edgeSetSumEquiv_symm_inl`, `SimpleGraph.coe_edgeSetSumEquiv_symm_inr` — the
  edges of the two summands sit in the disjoint sum through the two inclusions.
-/

public section

namespace TauCeti

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Adjacency in a disjoint sum of graphs is decidable: `SimpleGraph.sum` splits on which sides its
two arguments lie, and vertices on opposite sides are never adjacent. -/
instance instDecidableRelSumAdj (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | .inl u, .inl v => ‹DecidableRel G.Adj› u v
  | .inr u, .inr v => ‹DecidableRel H.Adj› u v
  | .inl _, .inr _ => isFalse (by simp)
  | .inr _, .inl _ => isFalse (by simp)

/-- A graph on `V ⊕ W` contains the disjoint sum `G ⊕g H` exactly when its restrictions to the two
sides contain `G` and `H`: the sum has no edges across the sides. -/
@[simp]
theorem _root_.SimpleGraph.sum_le_iff {K : SimpleGraph (V ⊕ W)} :
    G ⊕g H ≤ K ↔ G ≤ K.comap Sum.inl ∧ H ≤ K.comap Sum.inr := by
  -- `G ⊕g H` is the join of the images of `G` and `H`; bound each through the map–comap Galois
  -- connection of the embeddings `Function.Embedding.inl/inr`, which coerce to `Sum.inl/inr`.
  rw [← map_inl_sup_map_inr, sup_le_iff]
  exact (map_le_iff_le_comap (f := .inl)).and (map_le_iff_le_comap (f := .inr))

/-- A disjoint sum of edgeless graphs is edgeless: no edge is contributed by either summand, and
none across the two sides. -/
theorem _root_.SimpleGraph.sum_bot_bot : ((⊥ : SimpleGraph V) ⊕g (⊥ : SimpleGraph W)) = ⊥ := by
  ext (u | u) (v | v) <;> simp

-- Both evaluation lemmas reduce the `Sym2.fromRelNdrec` implementation of `edgeSetSumEquiv` on an
-- edge `s(a, b)`, which holds by `rfl` once the edge is split into its endpoints.

/-- The inverse of `SimpleGraph.edgeSetSumEquiv` sends an edge of `G` to its image under the left
inclusion `Sum.inl`. -/
@[simp]
theorem _root_.SimpleGraph.coe_edgeSetSumEquiv_symm_inl (e : G.edgeSet) :
    ((edgeSetSumEquiv.symm (.inl e) : (G ⊕g H).edgeSet) : Sym2 (V ⊕ W)) =
      Sym2.map Sum.inl (e : Sym2 V) := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  rfl

/-- The inverse of `SimpleGraph.edgeSetSumEquiv` sends an edge of `H` to its image under the right
inclusion `Sum.inr`. -/
@[simp]
theorem _root_.SimpleGraph.coe_edgeSetSumEquiv_symm_inr (e : H.edgeSet) :
    ((edgeSetSumEquiv.symm (.inr e) : (G ⊕g H).edgeSet) : Sym2 (V ⊕ W)) =
      Sym2.map Sum.inr (e : Sym2 W) := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  rfl

end TauCeti
