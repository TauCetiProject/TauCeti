/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import TauCeti.Data.Fin.Sum
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Sum
import TauCeti.Data.Finset.Sum

/-!
# Vertex and edge counts of bipartite trace words

The trace of `(X Xᴴ) ^ k` for a rectangular matrix `X` expands over the closed words

`u 0, v 0, u 1, v 1, …, u (k - 1), v (k - 1), u 0`

alternating between row indices `u : Fin k → α` and column indices `v : Fin k → β`
(`Matrix.trace_mul_conjTranspose_pow_eq_sum_prod`). Such a word has `2 * k` steps. The step
from `u t` to `v t` reads the entry of `X` at `(u t, v t)`, and the step from `v t` back to
`u (t + 1)` reads the entry at `(u (t + 1), v t)`; `TauCeti.bipartiteEdge u v` records these
positions, which are the edges of the bipartite graph traversed by the word.

A connected graph has at most one more vertex than edges, so a bipartite word visits at most
one more row and column index than it reads positions. When no position is read exactly once,
the word reads at most `k` positions, and hence visits at most `k + 1` row and column indices in
total. In the moment method for sample covariance matrices these are the words left in the
expected trace expansion of a matrix with independent centred entries, and the bound controls
the number of their labellings by `p` row and `n` column indices.

## Main declarations

* `TauCeti.bipartiteEdge`: the positions read by the steps of a bipartite word.
* `TauCeti.image_univ_sumMap_comp_interleaveIndexEquiv_symm`: read as an ordinary cyclic word
  through `TauCeti.interleaveIndexEquiv`, a bipartite word visits its row and column indices.
* `TauCeti.card_image_add_card_image_le_card_image_bipartiteEdge_add_one`: a bipartite word
  visits at most one more row and column index than it reads positions.
* `TauCeti.card_image_bipartiteEdge_le_of_no_singleton_edge`: a bipartite word of half-length
  `k` reading no position exactly once reads at most `k` positions.
* `TauCeti.card_image_add_card_image_le_add_one_of_no_singleton_edge`: such a word visits at
  most `k + 1` row and column indices.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.2.1, the moment method for sample covariance matrices.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, the counting argument for the moment method.
-/

public section

open Finset

namespace TauCeti

variable {α β : Type*} {k : ℕ}

/-- The positions read by the steps of the closed bipartite word
`u 0, v 0, u 1, v 1, …, v (k - 1), u 0`: the step `inl t` from `u t` to `v t` reads `(u t, v t)`
and the step `inr t` from `v t` to `u (t + 1)` reads `(u (t + 1), v t)`, the row indices being
read cyclically. -/
def bipartiteEdge (u : Fin k → α) (v : Fin k → β) : Fin k ⊕ Fin k → α × β :=
  Sum.elim (fun t ↦ (u t, v t)) fun t ↦ (u (finRotate k t), v t)

/-- The edge map as a function on the two kinds of steps. -/
theorem bipartiteEdge_def (u : Fin k → α) (v : Fin k → β) :
    bipartiteEdge u v = Sum.elim (fun t ↦ (u t, v t))
      (fun t ↦ (u (finRotate k t), v t)) := (rfl)

@[simp, grind =]
theorem bipartiteEdge_inl (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteEdge u v (.inl t) = (u t, v t) := by
  simp [bipartiteEdge]

@[simp, grind =]
theorem bipartiteEdge_inr (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteEdge u v (.inr t) = (u (finRotate k t), v t) := by
  simp [bipartiteEdge]

/-- The ordinary edge traversed by an interleaved step is the unordered pair of vertices
specified by the bipartite edge of that step. -/
theorem interleaveIndexEquiv_edge_eq_pair_bipartiteEdge (u : Fin k → α) (v : Fin k → β)
    (a : Fin k ⊕ Fin k) :
    let e := interleaveIndexEquiv k
    let w := Sum.map u v ∘ e.symm
    s(w (e a), w (finRotate (2 * k) (e a))) =
      s(Sum.inl (bipartiteEdge u v a).1, Sum.inr (bipartiteEdge u v a).2) := by
  cases a
  · simp only [Function.comp_apply, finRotate_interleaveIndexEquiv_inl, Equiv.symm_apply_apply,
      Sum.map_inl, Sum.map_inr, bipartiteEdge_inl]
  · simp only [Function.comp_apply, finRotate_interleaveIndexEquiv_inr, Equiv.symm_apply_apply,
      Sum.map_inr, Sum.map_inl, bipartiteEdge_inr]
    exact Sym2.eq_swap

variable [DecidableEq α] [DecidableEq β]

/-- The interleaved word visits exactly the row indices and the column indices of the
bipartite word. -/
theorem image_univ_sumMap_comp_interleaveIndexEquiv_symm (u : Fin k → α) (v : Fin k → β) :
    univ.image (Sum.map u v ∘ (interleaveIndexEquiv k).symm) =
      (univ.image u).disjSum (univ.image v) := by
  rw [← image_image, image_univ_equiv, ← univ_disjSum_univ, image_sumMap_disjSum]

/-- A bipartite word visits at most one more row and column index than it reads positions.
The word may revisit indices and positions. -/
theorem card_image_add_card_image_le_card_image_bipartiteEdge_add_one (u : Fin k → α)
    (v : Fin k → β) :
    #(univ.image u) + #(univ.image v) ≤ #(univ.image (bipartiteEdge u v)) + 1 := by
  -- Read the alternating word as an ordinary cyclic word.
  let e := interleaveIndexEquiv k
  let w := Sum.map u v ∘ e.symm
  have hedges : (({i | w i ≠ w (finRotate (2 * k) i)} : Finset (Fin (2 * k))).image
      fun i ↦ s(w i, w (finRotate (2 * k) i))) ⊆
        (univ.image (bipartiteEdge u v)).image fun p ↦ s(.inl p.1, .inr p.2) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    obtain ⟨a, rfl⟩ := e.surjective i
    exact mem_image.2 ⟨bipartiteEdge u v a, mem_image_of_mem _ (mem_univ a),
      (interleaveIndexEquiv_edge_eq_pair_bipartiteEdge u v a).symm⟩
  have hcyclic := card_image_le_card_nonloop_cyclic_edges_add_one w
  rw [image_univ_sumMap_comp_interleaveIndexEquiv_symm, card_disjSum] at hcyclic
  exact hcyclic.trans (Nat.add_le_add_right ((card_le_card hedges).trans card_image_le) 1)

/-- A bipartite word of half-length `k` that reads no position exactly once reads at most `k`
distinct positions. -/
theorem card_image_bipartiteEdge_le_of_no_singleton_edge {u : Fin k → α} {v : Fin k → β}
    (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) :
    #(univ.image (bipartiteEdge u v)) ≤ k := by
  have hcount := two_mul_card_image_le_of_no_singleton_fiber h
  simp only [Fintype.card_sum, Fintype.card_fin] at hcount
  omega

/-- A bipartite word of half-length `k` that reads no position exactly once visits at most
`k + 1` row and column indices in total. -/
theorem card_image_add_card_image_le_add_one_of_no_singleton_edge {u : Fin k → α}
    {v : Fin k → β} (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) :
    #(univ.image u) + #(univ.image v) ≤ k + 1 :=
  (card_image_add_card_image_le_card_image_bipartiteEdge_add_one u v).trans
    (Nat.add_le_add_right (card_image_bipartiteEdge_le_of_no_singleton_edge h) 1)

end TauCeti
