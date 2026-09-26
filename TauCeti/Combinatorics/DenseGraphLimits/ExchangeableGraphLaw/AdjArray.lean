/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import TauCeti.Combinatorics.SimpleGraph.Measurable

/-!
# The adjacency array of a graph and the graph of an array

The adjacency array `SimpleGraph.adjArray G` of a graph on `ℕ` is symmetric with `false` diagonal.
An array is read back as a graph by `graphOfArray`, the `SimpleGraph.fromRel` of the array: `i` and
`j` are adjacent when they are distinct and the array is `true` at `(i, j)` or at `(j, i)`. The two
are mutually inverse on the symmetric arrays with `false` diagonal and intertwine relabelling of the
graph with the diagonal relabelling of the array. The adjacency array itself, its measurability and
its injectivity are in `SimpleGraph/Maps.lean` and `SimpleGraph/Measurable.lean`.

## Main results

* `SimpleGraph.adjArray_mem_symmetricArraysWithDiag`, `SimpleGraph.adjArray_comap` — the
  adjacency array of a graph on `ℕ` lies in the carrier and intertwines relabelling.
* `TauCeti.DenseGraphLimits.graphOfArray`, `graphOfArray_adj`, `measurable_graphOfArray`,
  `graphOfArray_pairReindex`.
* `SimpleGraph.graphOfArray_adjArray`, `TauCeti.DenseGraphLimits.adjArray_graphOfArray` — the
  two round trips.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5: exchangeable random graphs as symmetric zero-diagonal arrays.

No material is adapted from `cameronfreer/graphon`; the adjacency array is read directly from
Mathlib's adjacency relation, and the relabelling square is `SimpleGraph.comap_adj`.
-/

public section

open MeasureTheory Set TauCeti.Probability SimpleGraph

namespace TauCeti

namespace DenseGraphLimits

/-- The adjacency array of a graph is symmetric with `false` diagonal. -/
theorem _root_.SimpleGraph.adjArray_mem_symmetricArraysWithDiag (G : SimpleGraph ℕ) :
    G.adjArray ∈ symmetricArraysWithDiag Bool false :=
  mem_symmetricArraysWithDiag_iff.2
    ⟨fun i j => by simp [SimpleGraph.adjArray_apply, G.adj_comm], fun i => by simp⟩

/-- Relabelling the graph is relabelling both axes of its adjacency array. -/
theorem _root_.SimpleGraph.adjArray_comap (σ : Equiv.Perm ℕ) (G : SimpleGraph ℕ) :
    (SimpleGraph.comap ⇑σ G).adjArray = pairReindex σ σ G.adjArray := by
  funext ⟨i, j⟩
  simp [SimpleGraph.adjArray_apply, SimpleGraph.comap_adj, pairReindex_apply]

/-- The graph of an array: `i` and `j` are adjacent when they are distinct and the array is
`true` at `(i, j)` or at `(j, i)`, so on a symmetric array at either. -/
def graphOfArray (x : ℕ × ℕ → Bool) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun i j => x (i, j) = true

/-- Adjacency in the graph of an array. -/
@[simp]
theorem graphOfArray_adj (x : ℕ × ℕ → Bool) (i j : ℕ) :
    (graphOfArray x).Adj i j ↔ i ≠ j ∧ (x (i, j) = true ∨ x (j, i) = true) :=
  SimpleGraph.fromRel_adj _ _ _

/-- Reading an array as a graph is measurable. -/
@[fun_prop]
theorem measurable_graphOfArray : Measurable graphOfArray :=
  measurable_iff_adj.2 fun i j => by
    simp only [graphOfArray_adj]
    have hij : Measurable fun x : ℕ × ℕ → Bool => x (i, j) := measurable_pi_apply (i, j)
    have hji : Measurable fun x : ℕ × ℕ → Bool => x (j, i) := measurable_pi_apply (j, i)
    exact measurable_const.and ((hij.eq_const true).or (hji.eq_const true))

/-- The graph of the adjacency array of a graph is the graph. -/
@[simp]
theorem _root_.SimpleGraph.graphOfArray_adjArray (G : SimpleGraph ℕ) :
    graphOfArray G.adjArray = G := by
  ext i j
  simp only [graphOfArray_adj, SimpleGraph.adjArray_apply, decide_eq_true_eq]
  exact ⟨fun ⟨_, h⟩ => h.elim id G.adj_symm, fun h => ⟨G.ne_of_adj h, Or.inl h⟩⟩

/-- The adjacency array of the graph of a symmetric `false`-diagonal array is the array. -/
@[simp]
theorem adjArray_graphOfArray {x : ℕ × ℕ → Bool} (hx : x ∈ symmetricArraysWithDiag Bool false) :
    (graphOfArray x).adjArray = x := by
  obtain ⟨hs, hd⟩ := mem_symmetricArraysWithDiag_iff.1 hx
  funext ⟨i, j⟩
  rw [SimpleGraph.adjArray_apply]
  by_cases hij : i = j
  · subst hij; simp [hd]
  · simp [graphOfArray_adj, hij, hs i j]

/-- The graph of a relabelled array is the relabelling of its graph. -/
theorem graphOfArray_pairReindex (σ : Equiv.Perm ℕ) (x : ℕ × ℕ → Bool) :
    graphOfArray (pairReindex σ σ x) = SimpleGraph.comap ⇑σ (graphOfArray x) := by
  ext i j
  simp [graphOfArray_adj, pairReindex_apply, σ.injective.ne_iff]

end DenseGraphLimits

end TauCeti
