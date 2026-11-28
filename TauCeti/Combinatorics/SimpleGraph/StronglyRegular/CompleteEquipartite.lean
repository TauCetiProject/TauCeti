/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import TauCeti.Combinatorics.SimpleGraph.CompleteMultipartite

/-!
# Complete equipartite graphs are strongly regular

The complete equipartite graph `K_{m × a}` (Mathlib's `SimpleGraph.completeEquipartiteGraph m a`)
has the vertex set `Fin m × Fin a`, and two vertices are adjacent when they lie in different
parts, that is, when their first coordinates differ. Its complement `m K_a` is the disjoint union
of `m` complete graphs on `a` vertices. This file proves that both graphs are strongly regular,
from the counts of common neighbours in `TauCeti.Combinatorics.SimpleGraph.CompleteMultipartite`.

The parameters use truncated subtraction and hold for all `m` and `a`. For `m = 1` the graph
`K_{1 × a}` is edgeless with parameters `(a, 0, 0, 0)`, and its complement is the complete graph
`K_a` with parameters `(a, a - 1, a - 2, 0)`.

## Main results

* `SimpleGraph.completeEquipartiteGraph_isSRGWith`: `K_{m × a}` is strongly regular with
  parameters `(m a, (m - 1) a, (m - 2) a, (m - 1) a)`.
* `SimpleGraph.compl_completeEquipartiteGraph_isSRGWith`: `m K_a` is strongly regular with
  parameters `(m a, a - 1, a - 2, 0)`.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012,
  Section 9.1.1 (vii) and (ix), p. 116.
-/

public section

namespace SimpleGraph

/-- **Complete equipartite graphs.** `K_{m × a}` is strongly regular with parameters
`(m a, (m - 1) a, (m - 2) a, (m - 1) a)`. -/
theorem completeEquipartiteGraph_isSRGWith (m a : ℕ) :
    (completeEquipartiteGraph m a).IsSRGWith (m * a) ((m - 1) * a) ((m - 2) * a)
      ((m - 1) * a) where
  card := by simp
  regular := degree_completeEquipartiteGraph
  of_adj v w h := by
    simp only [← Set.toFinset_card, commonNeighbors_completeEquipartiteGraph, Set.toFinset_prod,
      Set.toFinset_compl, Set.toFinset_insert, Set.toFinset_singleton, Set.toFinset_univ,
      Finset.card_product, Finset.card_compl, Finset.card_pair (completeEquipartiteGraph_adj.1 h),
      Finset.card_univ, Fintype.card_fin]
  of_not_adj v w _ h := by
    have hvw : v.1 = w.1 := not_not.1 (completeEquipartiteGraph_adj.not.1 h)
    simp only [← Set.toFinset_card, commonNeighbors_completeEquipartiteGraph, hvw,
      Set.insert_eq_of_mem, Set.mem_singleton_iff, Set.toFinset_prod, Set.toFinset_compl,
      Set.toFinset_singleton, Set.toFinset_univ, Finset.card_product, Finset.card_compl,
      Finset.card_singleton, Finset.card_univ, Fintype.card_fin]

/-- **Disjoint unions of complete graphs.** The complement `m K_a` of `K_{m × a}` is strongly
regular with parameters `(m a, a - 1, a - 2, 0)`. -/
theorem compl_completeEquipartiteGraph_isSRGWith (m a : ℕ) :
    (completeEquipartiteGraph m a)ᶜ.IsSRGWith (m * a) (a - 1) (a - 2) 0 where
  card := by simp
  regular := degree_compl_completeEquipartiteGraph
  of_adj v w h := by
    obtain ⟨hne, hvw⟩ : v ≠ w ∧ v.1 = w.1 := by simpa using h
    have hsub : ({v, w} : Finset (Fin m × Fin a)) ⊆ {w.1} ×ˢ Finset.univ := by
      intro u hu
      rw [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;>
        simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true, hvw]
    simp only [← Set.toFinset_card, commonNeighbors_compl_completeEquipartiteGraph, hvw,
      Set.inter_self, Set.toFinset_sdiff, Set.toFinset_prod, Set.toFinset_insert,
      Set.toFinset_singleton, Set.toFinset_univ]
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_product, Finset.card_pair hne,
      Finset.card_singleton, Finset.card_univ, Fintype.card_fin, one_mul]
  of_not_adj v w hne h := by
    have hvw : v.1 ≠ w.1 := fun hvw ↦ h (by simp [hne, hvw])
    simp [commonNeighbors_compl_completeEquipartiteGraph, hvw]

end SimpleGraph
