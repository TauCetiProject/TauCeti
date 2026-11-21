/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Rotate

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

variable [DecidableEq α] [DecidableEq β]

/-- A bipartite word visits at most one more row and column index than it reads positions.
The word may revisit indices and positions. -/
theorem card_image_add_card_image_le_card_image_bipartiteEdge_add_one (u : Fin k → α)
    (v : Fin k → β) :
    #(univ.image u) + #(univ.image v) ≤ #(univ.image (bipartiteEdge u v)) + 1 := by
  cases k with
  | zero => simp
  | succ m =>
    -- Read the alternating word as an ordinary path, omitting its closing step.
    let w (i : ℕ) : α ⊕ β := if i % 2 = 0 then
      .inl (u (Fin.ofNat (m + 1) (i / 2))) else .inr (v (Fin.ofNat (m + 1) (i / 2)))
    let edge (p : α × β) : Sym2 (α ⊕ β) := s(.inl p.1, .inr p.2)
    have hvertices : (univ.image u).disjSum (univ.image v) ⊆
        (range (2 * m + 2)).image w := by
      rintro (a | b) hx <;> simp only [inl_mem_disjSum, inr_mem_disjSum] at hx
      · obtain ⟨t, -, rfl⟩ := mem_image.1 hx
        exact mem_image.2 ⟨2 * t.val, mem_range.2 (by omega), by simp [w]⟩
      · obtain ⟨t, -, rfl⟩ := mem_image.1 hx
        refine mem_image.2 ⟨2 * t.val + 1, mem_range.2 (by omega), ?_⟩
        simp [w, Nat.add_div]
    have hedges :
        (((range (2 * m + 1)).filter fun i ↦ w i ≠ w (i + 1)).image
          fun i ↦ s(w i, w (i + 1))) ⊆ (univ.image (bipartiteEdge u v)).image edge := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.1 he
      have hi' : i < 2 * m + 1 := mem_range.1 (mem_filter.1 hi).1
      let t : Fin (m + 1) := ⟨i / 2, by omega⟩
      have hidx : Fin.ofNat (m + 1) (i / 2) = t := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt t.isLt
      by_cases hpar : i % 2 = 0
      · have hnext : (i + 1) % 2 ≠ 0 := by omega
        have hdiv : (i + 1) / 2 = i / 2 := by omega
        refine mem_image.2 ⟨bipartiteEdge u v (.inl t), mem_image_of_mem _ (mem_univ _), ?_⟩
        simp only [edge, bipartiteEdge_inl, w, hpar, hnext, ↓reduceIte, hdiv, hidx]
      · have hnext : (i + 1) % 2 = 0 := by omega
        have hdiv : (i + 1) / 2 = i / 2 + 1 := by omega
        have ht : t ≠ Fin.last m := by
          intro h
          have := congrArg Fin.val h
          dsimp [t] at this
          omega
        have hrot : finRotate (m + 1) t = Fin.ofNat (m + 1) ((i + 1) / 2) := by
          apply Fin.ext
          rw [coe_finRotate_of_ne_last ht]
          simp only [Fin.val_ofNat, t]
          rw [Nat.mod_eq_of_lt (by omega)]
          exact hdiv.symm
        refine mem_image.2 ⟨bipartiteEdge u v (.inr t), mem_image_of_mem _ (mem_univ _), ?_⟩
        simp only [edge, bipartiteEdge_inr, w, hpar, hnext, ↓reduceIte, hrot, hidx]
        exact Sym2.eq_swap
    have hpath := card_image_range_le_card_nonloop_edges_add_one w (2 * m + 1)
    have hv := card_le_card hvertices
    rw [card_disjSum] at hv
    exact hv.trans (hpath.trans (Nat.add_le_add_right
      ((card_le_card hedges).trans (card_image_le)) 1))

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
